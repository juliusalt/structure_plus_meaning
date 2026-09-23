#!/usr/bin/env python3
"""What a simulation run (simrun.py) did and cost, and whether what the machinery believed was so.

    simreport.py OUT [OUT ...]      one column per run; a JSON of everything beside each run (OUT/report.json)

Costs are input-equivalent tokens as the harness prices them: cache read 0.1, cache write 2 (1-hour entries), input 1,
output 5 — every request of every session, from the fake's log (pings' transcripts are deleted by the harness).

  upkeep     what keeps the context current and warm: stable loads, parts, the reference reasoning, delta messages,
             role layers, churns, the knowledge base, pings of bases, parts and sessions
  work       the replayed sessions' own requests: the prefix each forked (read from cache or written anew at its first
             request, then carried in every request at 0.1) and its own growth (identical in every run: recorded)
  stale      a model, the review's B made explicit: what a fork lacks of the current held content at its start (the
             changed units since what its prefix holds, ground truth from git), written into its context once as it
             reads it (2 a token)

Checks: every fork's stale line against the truth (the held files that changed between what its prefix holds and main
at its start); cold forks; what the machinery recorded of a fork against what the fake gave it.
"""
import collections
import json
import shutil
import os
import re
import subprocess
import sys
import tempfile

PRICE = dict(read=0.1, write=2.0, input=1.0, output=5.0)


def cost(r):
    return (PRICE["read"] * r.get("cache_read_input_tokens", 0) + PRICE["write"] * r.get("cache_creation_input_tokens", 0)
            + PRICE["input"] * r.get("input_tokens", 0) + PRICE["output"] * r.get("output_tokens", 0))


def rows(path):
    try:
        return [json.loads(line) for line in open(path) if line.strip()]
    except OSError:
        return []


def category(r, work_names):
    name, kind = r["name"], r["kind"]
    if kind == "work" or name in work_names:
        return "work"
    if kind == "ping":
        if re.match(r"warm-(max|xhigh|high)(-|$)", name):
            return "ping base/part"
        return "ping session"
    if kind == "load":
        if re.fullmatch(r"(max|xhigh|high)-base(-\d+)?", name):
            return "stable load"
        if "-delta-" in name:
            return "delta message"
        return "part load"
    if kind == "held":
        return "churn" if name.startswith("churn-") else "delta message"
    if kind == "role-layer":
        return "role layer"
    if kind == "reference":
        return "reference reasoning"
    if kind == "kb":
        return "knowledge base"
    return kind


class Run:
    def __init__(self, out):
        self.out = out
        self.sim = rows(os.path.join(out, "sim.jsonl"))
        self.requests = rows(os.path.join(out, "fake", "requests.jsonl"))
        try:
            self.fake = json.load(open(os.path.join(out, "fake", "sessions.json")))
        except (OSError, ValueError):
            self.fake = {}
        self.starts = [r for r in self.sim if r["what"] == "start"]
        self.work = {r["name"] for r in self.starts}
        self.project = os.path.join(out, "project")
        self.orch = os.path.join(self.project, ".claude", "orchestration")
        self.log = open(os.path.join(out, "state", "v2.log"), errors="ignore").read().splitlines() \
            if os.path.exists(os.path.join(out, "state", "v2.log")) else []
        self.warm = open(os.path.join(out, "state", "warm.log"), errors="ignore").read().splitlines() \
            if os.path.exists(os.path.join(out, "state", "warm.log")) else []

    # ---------------------------------------------------------------- costs

    def costs(self):
        by = collections.Counter()
        n = collections.Counter()
        for r in self.requests:
            c = category(r, self.work)
            by[c] += cost(r)
            n[c] += 1
        work_first = collections.Counter()
        seen = set()
        for r in self.requests:
            if r["name"] in self.work and r["name"] not in seen:
                seen.add(r["name"])
                work_first["read"] += r.get("cache_read_input_tokens", 0)
                work_first["write"] += r.get("cache_creation_input_tokens", 0)
        prefix = 0.0
        for s in self.starts:
            reqs = [r for r in self.requests if r["name"] == s["name"]]
            start = (self.fake.get(s.get("sid") or "") or {}).get("start_ctx") or 0
            first = s.get("first") or 0
            prefix += 0.1 * max(0, start - first) * len(reqs)
        upkeep = sum(v for k, v in by.items() if k != "work")
        return dict(by={k: round(v) for k, v in sorted(by.items())}, requests=dict(n), upkeep=round(upkeep),
                    work=round(by["work"]), total=round(sum(by.values())), work_first=dict(work_first),
                    work_prefix_carried=round(prefix))

    # ---------------------------------------------------------------- what the machinery did

    def events(self):
        pats = collections.OrderedDict([
            ("delta increment", r"delta grows by an increment"),
            ("delta written anew", r" delta is written anew"),
            ("delta built again (missed entry)", r"delta is built again: a fork missed"),
            ("delta session made", r"delta's session is made"),
            ("delta begun anew (one text)", r"delta's chain is begun anew"),
            ("delta text cut", r"delta \w+: cut "),
            ("kb took texts", r"integrated .*holding max's chain"),
            ("parts refreshed", r"parts from \w+ up are refreshed"),
            ("layer refreshed (structure)", r"layer is refreshed: (the reference|the material boundaries|the list)"),
            ("layer refreshed (cold entry)", r"layer is refreshed: its own cache entry is cold"),
            ("role layer built", r"reasoning layer \S+ is being built"),
            ("role layer did not finish", r"reasoning layer \S+ did not finish"),
            ("churn built", r"churn \S+ is being built"),
            ("churn grown", r"churn \S+ is being grown"),
            ("kb built", r"holds the knowledge"),
            ("launch refused", r"^\S+ no \w[\w-]* started"),
            ("ATTENTION", r"ATTENTION"),
        ])
        out = collections.Counter()
        detail = collections.defaultdict(list)
        for line in self.log:
            for k, p in pats.items():
                if re.search(p, line):
                    out[k] += 1
                    if len(detail[k]) < 400:
                        detail[k].append(line[:300])
        for line in self.warm:
            m = re.match(r"^\S+ (warm|stack|layer|delta|reasoning|direction|inventory|catalogue) (\w+)[: ]", line)
            if "MISS" in line:
                out["cache MISS (warm.log)"] += 1
                detail["cache MISS (warm.log)"].append(line[:240])
            if "FAILED" in line:
                out["FAILED (warm.log)"] += 1
                detail["FAILED (warm.log)"].append(line[:240])
            if re.match(r"^\S+ warm ", line):
                out["pings (base.sh)"] += 1
            if re.match(r"^\S+ delta \w+: cut ", line):
                out["delta text cut"] += 1
        per_base = collections.Counter()
        for line in self.log:
            m = re.search(r"the (max|xhigh|high) (delta grows by an increment|delta is written anew|delta's session is made|"
                          r"delta's chain is begun anew|parts from (\w+) up)", line)
            if m:
                per_base[(m.group(1), m.group(2) if not m.group(3) else "refresh from " + m.group(3))] += 1
        return dict(counts=dict(out), per_base={f"{a}: {b}": v for (a, b), v in sorted(per_base.items())},
                    detail={k: v for k, v in detail.items()})

    def forks(self):
        """How the replayed sessions started: what they forked, and what that cost at their first request."""
        kinds = collections.Counter()
        cold = []
        refused = [r for r in self.sim if r["what"] == "refused"]
        for s in self.starts:
            origin = s.get("origin") or ""
            kind = ("churn" if origin.startswith("churn-") else "role layer" if origin.startswith("layer-") else
                    "knowledge base" if origin.startswith("kb-") else "base top" if origin in ("max", "xhigh", "high")
                    else "base part" if ":" in origin else "other")
            kinds[kind] += 1
            first = next((r for r in self.requests if r["name"] == s["name"]), None)
            if first and first.get("cache_creation_input_tokens", 0) > 50_000:
                cold.append((s["name"], origin, first.get("cache_read_input_tokens"), first.get("cache_creation_input_tokens")))
        return dict(origins=dict(kinds), cold=cold[:50], cold_count=len(cold), refused=len(refused),
                    refused_roles=dict(collections.Counter(r["role"] for r in refused)))

    # ---------------------------------------------------------------- the stale lines against the truth

    def held(self):
        """{path relative to the project: (part, level)} of every base's list as it stands at the end."""
        sys.path.insert(0, self.orch)
        import manifest
        out = {}
        for who, name in manifest.LISTS.items():
            path = os.path.join(self.orch, name)
            if not os.path.exists(path):
                continue
            for e in manifest.list_entries(open(path).read(), self.project):
                rel = os.path.relpath(e["path"], self.project)
                out.setdefault(who, {})[rel] = (e["part"], e["level"])
        return out

    INDEX_SOURCES = {"decisions-index": ["DECISIONS.md"], "theory-map-index": ["THEORY_MAP.md"],
                     "tool-index": ["tools/"], "plan-index": ["native_control_plan.md"], "theory-names": ["theories/"],
                     "library-practice": []}

    def indexes_at(self, head):
        """{index file name: text} as the harness's generator makes them from the repository at `head` (the truth for
        a generated index: the decisions' index holds each decision's heading and first sentence, so an edit of
        DECISIONS.md elsewhere changes nothing in it)."""
        self._indexes = getattr(self, "_indexes", {})
        if head in self._indexes:
            return self._indexes[head]
        cached = os.path.join(os.path.dirname(os.path.abspath(__file__)), "index-cache", head + ".json")
        if os.path.exists(cached):  # made once for every run, on every core (indexcache.py)
            self._indexes[head] = json.load(open(cached))
            return self._indexes[head]
        out = {}
        with tempfile.TemporaryDirectory() as d:
            archive = subprocess.Popen(["git", "-C", self.project, "archive", head], stdout=subprocess.PIPE)
            subprocess.run(["tar", "-x", "-C", d, "--exclude=.claude/orchestration"], stdin=archive.stdout)
            archive.wait()
            orch = os.path.join(d, ".claude", "orchestration")
            shutil.copytree(self.orch, orch, ignore=shutil.ignore_patterns("state", "__pycache__", "notes"))
            env = {k: v for k, v in os.environ.items() if not k.startswith(("ORCH_", "SIM_"))}
            env.update(ORCH_PROJECT=d, ORCH_STATE_DIR=os.path.join(d, "state"), HOME=os.path.join(self.out, "home"))
            subprocess.run([sys.executable, "-B", "-c", "import sys; sys.path.insert(0, sys.argv[1]); "
                            "import select_base_load as s; s.refresh_indexes()", orch], env=env, cwd=d,
                           capture_output=True)
            held = os.path.join(orch, "state", "held")
            for name in os.listdir(held) if os.path.isdir(held) else []:
                out[os.path.splitext(name)[0]] = open(os.path.join(held, name), errors="ignore").read()
        self._indexes[head] = out
        return out

    def changed(self, a, b):
        if a == b:
            return set()
        out = subprocess.run(["git", "-C", self.project, "diff", "--name-only", a, b], capture_output=True, text=True)
        return {p for p in out.stdout.split("\n") if p}

    def holds_head(self, sid):
        """The head as of which a session's prefix holds the base's content: that of its nearest ancestor that brought
        the held files up to its own time — a delta message, a churn, a load — or None."""
        if not hasattr(self, "_v2"):
            try:
                self._v2 = json.load(open(os.path.join(self.out, "state", "v2.json")))["sessions"]
            except (OSError, ValueError, KeyError):
                self._v2 = {}
            self._by_sid = {v.get("sid"): v for v in self._v2.values() if v.get("sid")}
        s = sid
        while s:
            rec = self.fake.get(s) or {}
            if (rec.get("name") or "").startswith("churn-"):
                # a churn holds the delta's messages as of the top it copied, not as of its own start
                top = (self._by_sid.get(s) or {}).get("delta_sid")
                if top and top in self.fake:
                    return self.fake[top].get("head")
            if rec.get("kind") in ("held", "load") or (rec.get("name") or "").startswith(("kb-",)) \
                    or (self._by_sid.get(s) or {}).get("holds_node"):  # a judging layer holding the texts itself
                return rec.get("head")
            s = rec.get("parent")
        return None

    def lacking(self, rel, level, a, b):
        """Tokens of the held units of a file that differ between two commits: what a fork holding it as of `a` lacks at
        `b` (the delta's own measure, manifest.changed_units over digest.held_text at the file's depth)."""
        key = (rel, level, a, b)
        if key in self._lack:
            return self._lack[key]
        import manifest
        from digest import held_text
        texts = []
        with tempfile.TemporaryDirectory() as d:
            for sha in (a, b):
                blob = subprocess.run(["git", "-C", self.project, "show", f"{sha}:{rel}"], capture_output=True).stdout
                path = os.path.join(d, sha[:8] + "-" + os.path.basename(rel))
                open(path, "wb").write(blob)
                try:
                    texts.append(held_text(path, level)[0])
                except Exception:  # noqa: BLE001
                    texts.append(blob.decode(errors="ignore"))
        n = 0
        if texts[0] != texts[1]:
            n = int(len(manifest.changed_units(rel, texts[0], texts[1])) / manifest.RATIO.get(os.path.splitext(rel)[1], 2.6))
        self._lack[key] = n
        return n

    def stale_check(self):
        held = self.held()
        self._lack = {}
        results = []
        for s in self.starts:
            role = s["role"]
            who = "max" if role == "planner" else ("xhigh" if role in ("designer", "task-designer", "investigator",
                                                                         "reviewer") else "high")
            files = held.get(who) or {}
            origin_sid = s.get("origin_sid")
            since = self.holds_head(origin_sid)
            if not since or not s.get("head"):
                continue
            moved = self.changed(since, s["head"])
            truth = set()
            for rel in files:
                base = os.path.splitext(os.path.basename(rel))[0]
                if rel.startswith(".claude/orchestration/state/held/"):
                    stem = re.sub(r"-(max|xhigh|high)$", "", base)
                    sources = self.INDEX_SOURCES.get(stem, [])
                    if any(m == src or (src.endswith("/") and m.startswith(src)) for m in moved for src in sources) \
                            and self.indexes_at(since).get(base) != self.indexes_at(s["head"]).get(base):
                        truth.add(base)
                elif rel in moved:
                    truth.add(base)
            said = set()
            for m in re.finditer(r"\(\d+\): ([^;]*)", s.get("stale") or ""):
                said |= {x.strip().lstrip("+") for x in m.group(1).split(",") if x.strip() and x.strip() != "none"
                         and not x.strip().startswith("…")}
            lack = sum(self.lacking(rel, files[rel][1], since, s["head"]) for rel in files
                       if rel in moved and not rel.startswith(".claude/"))
            results.append(dict(name=s["name"], origin=s.get("origin"), truth=sorted(truth), said=sorted(said),
                                missed=sorted(truth - said), extra=sorted(said - truth), lacking=lack,
                                missed_index=sorted(x for x in truth - said if re.search(r"index|names|practice", x))))
        n = len(results)
        missed = sum(1 for r in results if r["missed"])
        extra = sum(1 for r in results if r["extra"])
        missed_names = collections.Counter(x for r in results for x in r["missed"])
        extra_names = collections.Counter(x for r in results for x in r["extra"])
        lacking = [r["lacking"] for r in results]
        return dict(forks=n, forks_missing_a_change=missed, forks_told_a_change_that_is_not=extra,
                    lacking_total=sum(lacking), lacking_mean=round(sum(lacking) / n) if n else 0,
                    stale_model_cost=2 * sum(lacking),
                    forks_missing_an_index=sum(1 for r in results if r["missed_index"]),
                    missed_most=missed_names.most_common(15), extra_most=extra_names.most_common(15),
                    truth_files_total=sum(len(r["truth"]) for r in results),
                    said_files_total=sum(len(r["said"]) for r in results), cases=results[:400])

    def recorded_vs_actual(self):
        """What the machinery recorded of a fork against what the fake gave it: the context it forked."""
        out = []
        for s in self.starts:
            actual = (self.fake.get(s.get("origin_sid") or "") or {}).get("context")
            recorded = s.get("origin_context")
            if actual and recorded and abs(actual - recorded) > 0.02 * actual:
                out.append((s["name"], s.get("origin"), recorded, actual))
        return dict(mismatches=len(out), cases=out[:30])

    def hindsight(self):
        """Each context-holding session the machinery built — a delta message, a churn, a role layer — with what it
        cost, how many of the replayed forks descended from it, and what it spared them under the review's B (its own
        written tokens, which each of them would otherwise have written as it read them)."""
        by_sid = collections.defaultdict(lambda: dict(cost=0.0, written=0, requests=0))
        for r in self.requests:
            b = by_sid[r["sid"]]
            b["cost"] += cost(r)
            b["requests"] += 1
            if b["requests"] == 1:
                b["written"] = r.get("cache_creation_input_tokens", 0)
        served = collections.Counter()
        for s in self.starts:
            sid = s.get("origin_sid")
            seen = set()
            while sid and sid not in seen:
                seen.add(sid)
                served[sid] += 1
                sid = (self.fake.get(sid) or {}).get("parent")
        out = collections.defaultdict(lambda: dict(built=0, cost=0.0, forks=0, spared=0.0, unused=0))
        for sid, rec in self.fake.items():
            name = rec.get("name") or ""
            kind = ("delta message" if re.match(r"(max|xhigh|high)-delta-\d", name) else "churn" if name.startswith("churn-")
                    else "role layer" if name.startswith("layer-") else "knowledge base" if name.startswith("kb-")
                    else "part" if re.match(r"(max|xhigh|high)-(direction|inventory|catalogue|layer)-", name)
                    else "reference" if name.startswith("reference-") else None)
            if not kind:
                continue
            b, o = by_sid.get(sid) or dict(cost=0.0, written=0), out[kind]
            o["built"] += 1
            o["cost"] += b["cost"]
            o["forks"] += served[sid]
            o["spared"] += 2 * b["written"] * served[sid] if kind in ("delta message", "churn") else 0
            o["unused"] += served[sid] == 0
        return {k: {kk: round(vv) for kk, vv in v.items()} for k, v in out.items()}

    def pings(self):
        """Keep-warm pings by what they kept warm."""
        out = collections.defaultdict(lambda: dict(pings=0, cost=0.0))
        for r in self.requests:
            if r["kind"] != "ping":
                continue
            m = re.match(r"warm-((max|xhigh|high)(-[a-z]+)?|[a-z-]+?)(-\d+(\.\d+)?)?(-\d{9,})?$", r["name"])
            key = re.sub(r"-\d+(\.\d+)?(-\d+)?$", "", r["name"][5:])
            key = re.sub(r"-\d{9,}$", "", key)
            key = re.sub(r"^(implement|fix|review|design|brief|investigate|plan|kb|layer|churn)-.*", r"\1 sessions", key)
            o = out[key]
            o["pings"] += 1
            o["cost"] += cost(r)
        return {k: dict(pings=v["pings"], cost=round(v["cost"])) for k, v in sorted(out.items())}

    def report(self):
        rep = dict(run=self.out, done=[r for r in self.sim if r["what"] == "done"][-1:],
                   errors=[r for r in self.sim if r["what"] == "error"][:20],
                   costs=self.costs(), events=self.events(), forks=self.forks(),
                   stale=self.stale_check(), recorded=self.recorded_vs_actual(), hindsight=self.hindsight(),
                   pings=self.pings())
        json.dump(rep, open(os.path.join(self.out, "report.json"), "w"), indent=1)
        return rep


def main():
    reps = [Run(out).report() for out in sys.argv[1:]]
    for rep in reps:
        c, e, f, s = rep["costs"], rep["events"], rep["forks"], rep["stale"]
        print(f"=== {rep['run']}")
        print(f"  total {c['total']:,}  upkeep {c['upkeep']:,}  work {c['work']:,} (prefix carried {c['work_prefix_carried']:,})")
        for k, v in c["by"].items():
            print(f"    {k:22} {v:>14,}  ({c['requests'].get(k, 0)} requests)")
        print(f"  forks by origin {f['origins']}; cold first requests {f['cold_count']}; refused {f['refused']} "
              f"{f['refused_roles']}")
        print(f"  events {json.dumps(e['counts'])}")
        print(f"  per base {json.dumps(e['per_base'])}")
        print(f"  stale lines: {s['forks']} forks; {s['forks_missing_a_change']} not told a change they lack "
              f"(true {s['truth_files_total']}, said {s['said_files_total']}); {s['forks_told_a_change_that_is_not']} "
              f"told one they do not lack")
        print(f"    lacking at start (held units, ground truth): total {s['lacking_total']:,}, mean {s['lacking_mean']:,} a fork;"
              f" modelled stale cost (B: written once) {s['stale_model_cost']:,}; forks missing an index {s['forks_missing_an_index']}")
        print(f"    missed most: {s['missed_most'][:8]}")
        print(f"    extra most: {s['extra_most'][:8]}")
        print(f"  recorded origin context off by >2%: {rep['recorded']['mismatches']}; errors: {len(rep['errors'])}")
        for k, v in rep["hindsight"].items():
            print(f"    hindsight {k:14} built {v['built']:>3}  cost {v['cost']:>11,}  forks descended {v['forks']:>4}  "
                  f"spared (B) {v['spared']:>11,}  never forked {v['unused']}")
        print("  pings: " + "; ".join(f"{k} {v['pings']} ({v['cost'] // 1000:,}K)" for k, v in rep["pings"].items()))


if __name__ == "__main__":
    main()
