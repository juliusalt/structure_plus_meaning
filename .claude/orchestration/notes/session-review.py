"""The review of the run's sessions that the owner asked to be kept up (2026-09-22): what each session started since a
moment was refused or failed, how it batched its reads and its writes, what the harness's log says since, and how
the bases, the machine and the disk stand. Not part of the harness; read-only: it writes nothing but its own mark.

    python3 -B notes/session-review.py [--since "YYYY-MM-DD HH:MM"] [--mark FILE]

Without --since it starts where the last review ended (the mark file, written at the end of each run).
"""
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
import v2  # noqa: E402
import work_meter as w  # noqa: E402

args = sys.argv[1:]
mark = args[args.index("--mark") + 1] if "--mark" in args else os.path.join(os.environ.get("TMPDIR", "/tmp"), "session-review.since")
if "--since" in args:
    since = time.mktime(time.strptime(args[args.index("--since") + 1], "%Y-%m-%d %H:%M"))
else:
    try:
        since = float(open(mark).read())
    except (OSError, ValueError):
        since = time.time() - 3600
now = time.time()
iso = lambda t: time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(t))
print(f"# review of {time.strftime('%H:%M', time.localtime(since))} to {time.strftime('%H:%M', time.localtime(now))}")

st = v2.peek()
NOTES = ("[What this request holds was ready", "[Your last request read", "[one change in this call")


def own_records(s):
    f = glob.glob(os.path.expanduser(f"~/.claude/projects/*/{s['sid']}.jsonl"))
    if not f:
        return []
    t0 = time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime((s.get("started") or 0) - 5))
    out = []
    for line in open(f[0]):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if r.get("timestamp", "") >= t0:
            out.append(r)
    return out


def text_of(content):
    return " ".join(x.get("text", "") for x in content) if isinstance(content, list) else str(content)


# sessions with anything since the mark: started since, or with records since
rows = []
for name, s in sorted(st["sessions"].items(), key=lambda x: x[1].get("started") or 0):
    if s["role"] in ("kb",) or not s.get("sid"):
        continue
    recs = own_records(s)
    newer = [r for r in recs if r.get("timestamp", "") >= time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(since))]
    if not newer:
        continue
    calls, kinds, order, shown, changes = {}, {}, [], {}, []
    for r in recs:
        if r.get("type") == "assistant":
            mid = r["message"].get("id")
            for b in r["message"]["content"]:
                if b.get("type") == "tool_use":
                    k = w.kind(b["name"], b["input"])
                    calls[b["id"]] = (r["timestamp"][11:19], mid, (b["input"].get("command") or json.dumps(b["input"]))[:160].replace("\n", "⏎"))
                    kinds.setdefault(mid, []).append(k)
                    if mid not in order:
                        order.append(mid)
                    c = b["input"].get("command") or ""
                    if w.CHANGE_VERB.search(w.shell_syntax(c)) and not re.search(r"v2\.py\s+again", c):
                        m = re.search(r"<<-?\s*'?EOF'?\n(.*?)\nEOF", c, re.S)
                        body = m.group(1) if m else c
                        changes.append(len(re.findall(r"^=== write ", body, re.M)) + len(re.findall(r"^<<<<<<< SEARCH$", body, re.M)))
    errors = []
    for r in newer:
        if r.get("type") == "assistant" and (r.get("message") or {}).get("model") == "<synthetic>" \
                and text_of(r["message"].get("content")) != "No response requested.":  # a resume's own, harmless
            errors.append((r["timestamp"][11:19], "(its turn)", text_of(r["message"].get("content"))[:200]))
        if r.get("type") == "user" and isinstance(r["message"]["content"], list):
            for b in r["message"]["content"]:
                if b.get("type") == "tool_result" and b["tool_use_id"] in calls:
                    t, mid, cmd = calls[b["tool_use_id"]]
                    body = text_of(b.get("content"))
                    shown[mid] = shown.get(mid, 0) + len(body.encode())
                    if b.get("is_error"):
                        errors.append((t, cmd, body[:260].replace("\n", " ")))
    rd = [m for m in order if all(k in ("read", "other") for k in kinds[m])]
    small = [m for m in rd if shown.get(m, 0) < 2500]
    text = "".join(json.dumps(r) for r in newer)
    rows.append(dict(name=name, role=s["role"], task=s.get("task") or s.get("reviews"), state=s["state"],
                     tree=s.get("tree") or "one tree", req=len(order), calls=sum(len(v) for v in kinds.values()),
                     rd=len(rd), small=len(small), chain=sum(1 for a, b in zip(order, order[1:]) if a in small and b in small),
                     kb=sum(shown.get(m, 0) for m in rd) / 1000 / max(1, len(rd)), chg=len(changes),
                     blocks=sum(changes), notes=[text.count(n) // 2 for n in NOTES], errors=errors))

print(f"\n## sessions with work since ({len(rows)})")
for r in rows:
    print(f"- {r['name']} ({r['role']}, task {r['task']}, {r['state']}, {r['tree']}): {r['req']} requests, "
          f"{r['calls'] / max(1, r['req']):.1f} calls each; reads {r['rd']} at {r['kb']:.1f}K, {r['small']} small, "
          f"{r['chain']} small after small; changes {r['chg']} of {r['blocks'] / max(1, r['chg']):.1f} each; "
          f"notes ready/small/one-change {r['notes'][0]}/{r['notes'][1]}/{r['notes'][2]}; {len(r['errors'])} errors")
    for t, cmd, said in r["errors"]:
        print(f"    [{t}] {cmd}\n        -> {said}")

print("\n## the harness's log since")
pattern = re.compile(r"ATTENTION|went cold|lost|is gone|error|failed|refused|does not|standstill|stood with|waited|"
                     r"given up|inconsistent|not resumed|could not|API failed|waits to measure|superseded check")
for line in open(os.path.join(v2.STATE, "v2.log"), errors="ignore"):
    if line[:19] >= iso(since)[:19] and pattern.search(line) and "protocol has no value" not in line:
        print("  " + line.rstrip()[:260])

print("\n## keep-warm since")
keep = False  # a traceback's lines carry no date: they go with the dated line before them
for line in open(os.path.join(v2.STATE, "warm.log"), errors="ignore"):
    if re.match(r"\d{4}-\d\d-\d\dT", line):
        keep = line[:19] >= iso(since)[:19]
    if keep:
        print("  " + line.rstrip()[:200])

print("\n## stuck work")
for tid in v2.resume_order(st):
    t = st["tasks"][tid]
    p = t.get("parked") or {}
    waited = (now - p.get("since", now)) / 60
    if waited > 30:
        holder = v2.slot(st, v2.PRODUCING)
        ready = v2.parked_ready(st, tid, p)
        why = ("ready, waiting for the producing slot, which is " + holder["name"] + "'s") if ready and holder else \
              ("ready" if ready else "not ready")
        print(f"  task {tid} parked {waited:.0f} min for {p.get('for')} ({why}; hold left "
              f"{(v2.hold_left(t) or 0) / 60:.0f} min)")
for name, sess in st["sessions"].items():
    woken = os.path.join(v2.STATE, f"{name}.woken")
    if os.path.exists(woken) and not sess.get("released"):
        times = [l[:19] for l in open(woken, errors="ignore") if re.match(r"\d{4}-", l)]
        recent = [x for x in times if x >= iso(now - 600)[:19]]
        if len(recent) >= 3:
            print(f"  {name} resumed {len(recent)} times in ten minutes: {', '.join(x[11:] for x in recent)}")
    if sess["state"] in v2.LIVE and not sess.get("released"):
        r = v2.row(name)
        f = glob.glob(os.path.expanduser(f"~/.claude/projects/*/{sess.get('sid')}.jsonl"))
        if r and r.get("activity") == "busy" and f and now - os.path.getmtime(f[0]) > 1200:
            print(f"  {name} busy, its transcript still for {(now - os.path.getmtime(f[0])) / 60:.0f} min")
ready = v2.startable(st)  # ready and unblocked, as the dispatch reads it
# a brief or a review waits for the supporting slot, not a producing one: task 141 (a brief) was named "nothing
# produces" at 10:22 while brief-142 held the supporting slot and no build could start
ready = [t for t in ready if (st["tasks"].get(t) or {}).get("kind") in v2.PRODUCING_KINDS
         or not v2.slot(st, v2.SUPPORTING)]
if ready and not v2.slot(st, v2.PRODUCING):
    print(f"  nothing produces while {len(ready)} queued task(s) could: {', '.join(ready[:6])}")
elif not ready and not v2.slot(st, v2.PRODUCING) and not v2.resume_order(st):
    print(f"  nothing produces and nothing can start: all {len(st['queue'])} queued tasks wait on blockers "
          "(the planner's graph is that narrow)")
# what a measurement costs the others is the time it holds the machine, not how often it takes one: task 269's four
# holds of about 30 s each were flagged where nothing was wrong (2026-09-22 21:22), each ended by the call that ran it
HELD_LONG, HELD_TOTAL = 300, 600
held, since, log = {}, {}, [l for l in open(os.path.join(v2.STATE, "v2.log"), errors="ignore") if l[:19] >= iso(now - 7200)[:19]]
for l in log:
    m = re.search(r"task (\w+) holds the machine", l)
    at = time.mktime(time.strptime(l[:19], "%Y-%m-%dT%H:%M:%S")) if l[:4] == "2026" else None
    if m and at:
        since[m.group(1)] = at
    end = re.search(r"the measurement of task (\w+) ended|cleared the machine's claim by task (\w+)", l)
    if end and at:
        tid = end.group(1) or end.group(2)
        if tid in since:
            held[tid] = held.get(tid, (0, 0))
            held[tid] = (held[tid][0] + at - since.pop(tid), held[tid][1] + 1)
for tid, at in since.items():  # still holding it
    held[tid] = (held.get(tid, (0, 0))[0] + now - at, held.get(tid, (0, 0))[1] + 1)
for tid, (seconds, n) in held.items():
    if seconds >= HELD_TOTAL or (n == 1 and seconds >= HELD_LONG):
        print(f"  task {tid} held the whole machine {int(seconds // 60)} min {int(seconds % 60)} s in two hours "
              f"({n} measurement{'s' if n > 1 else ''}; every other task's runs wait meanwhile)")

print("\n## standing")
for who in v2.BASES:
    hit = os.path.join(v2.STATE, f"{who}-base.hit")
    stable = os.path.join(v2.STATE, f"{who}-stable.hit")
    share = subprocess.run([sys.executable, os.path.join(HERE, "manifest.py"), "stale-share", who],
                           capture_output=True, text=True).stdout.strip()
    age = lambda p: f"{int((now - os.path.getmtime(p)) // 60)} min" if os.path.exists(p) else "none"
    print(f"  {who}: layer last hit {age(hit)} ago, stable base's own entry {age(stable)}, layer stale {share}")
    delta = v2.delta_record(who)  # the third part (notes/plan-delta-layer.md): forked once the base is switched to it
    if delta:
        print(f"    delta {delta.get('sessionId', '?')[:8]} sealed {delta.get('sealed', '?')[11:16]}, "
              f"{delta.get('tokens', '?')} tokens ({delta.get('layer_tokens', '?')} frontier, "
              f"{delta.get('stable_tokens', '?')} stable), {'forked' if v2.deltas_on(who) else 'not yet forked'}; "
              f"the layer's own entry {age(os.path.join(v2.STATE, f'{who}-layer.hit'))}")
beat = os.path.join(v2.STATE, "warm.beat")
print(f"  daemon heartbeat {int(now - os.path.getmtime(beat))} s ago" if os.path.exists(beat) else "  NO daemon heartbeat")
disk = shutil.disk_usage(v2.PROJECT)
mem = {l.split(":")[0]: int(l.split()[1]) / 2**20 for l in open("/proc/meminfo") if l.split()[1:2]}
print(f"  disk {disk.used / disk.total:.0%} used, {disk.free // 2**30} GiB free; memory available "
      f"{mem.get('MemAvailable', 0):.1f} of {mem.get('MemTotal', 0):.0f} GiB, swap used "
      f"{mem.get('SwapTotal', 0) - mem.get('SwapFree', 0):.1f} GiB (no run starts below {v2.MEM_MARGIN_GB:g})")
print(f"  one tree: uncommitted {[p for p in v2.changed_paths() if not p.startswith('.')]}, writer {v2.tree_writer(st)}, "
      f"trouble {v2.tree_trouble() or 'none'}")
print(f"  active {st['active']}, stopped {os.path.exists(os.path.join(v2.STATE, 'stopped'))}, "
      f"queue {len(st['queue'])}, events waiting {len(st['events'])}")
open(mark, "w").write(str(now))
