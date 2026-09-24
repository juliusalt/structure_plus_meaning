#!/usr/bin/env python3
"""The orchestration's context machinery run end to end over the recorded run, on a simulated clock.

    simrun.py ORCH OUT [--since 'YYYY-MM-DD HH:MM'] [--until 'YYYY-MM-DD HH:MM'] [--every 60] [--daemon-every 300]
                       [--deltas 'max xhigh high'] [--role-layers all|none|ROLES] [--max-sessions N]

ORCH is a copy of .claude/orchestration (the machinery under test); OUT a new directory for the world and its record.

What is real: the repository (a shared clone walking main's commits at their times), the harness's own code — base.sh,
base_stack.py, manifest.py, base_pack.py, select_base_load.py, v2.py (launch, the role layers and churns, the knowledge
base, the sweep), watchdog.py (holds, layers, deltas) and the daemon's loop body (the pings) — and the demand: every
session of the roles that fork a base, recorded in state/analysis/timeline.jsonl, started at its recorded time through
v2.launch, its requests at their recorded times with their recorded growth over the prefix it actually forked.
What is simulated: the clock (sitecustomize and a `date` shim; file times set to the simulated time after each step),
and Claude (fakeclaude.py: sessions, forks, loads, replies, and the prompt cache, from the real text's size).
Not simulated: the task lifecycle (planning, checks, reviews' verdicts, landings as work): the commits land at their
recorded times, and each session ends when its recorded requests end, then is sealed and released by the harness.
"""
import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import time

REPO = "/home/julius/structure_and_semantics"
SIM = os.path.dirname(os.path.abspath(__file__))
TIMELINE = os.path.join(REPO, ".claude/orchestration/state/analysis/timeline.jsonl")
REAL_MEMORY = os.path.expanduser("~/.claude/projects/-home-julius-structure-and-semantics/memory")
DEMAND = {"implementer", "fixer", "reviewer", "designer", "task-designer", "investigator", "planner"}
CHARS = 2.9

_real_time = time.time
_localtime, _gmtime, _strftime, _ctime = time.localtime, time.gmtime, time.strftime, time.ctime


class Clock:
    """The world's one clock, a file every process reads (sitecustomize): the driver moves it to each step, the fake
    claude past each session's replies; it never moves back."""

    def __init__(self, path):
        self.path, self.count = path, 0

    def read(self):
        try:
            with open(self.path) as f:
                return float(f.read().split()[0])
        except (OSError, ValueError, IndexError):
            return 0.0

    def set(self, t):
        t = max(float(t), self.read())
        with open(self.path + ".tmp", "w") as f:
            f.write(repr(t))
        os.replace(self.path + ".tmp", self.path)
        return t

    @property
    def t(self):
        return self.read()

    def now(self):
        self.count += 1
        return self.read() + self.count * 1e-6


CLOCK = None


def patch_time(clock):
    time.time = clock.now
    time.time_ns = lambda: int(clock.now() * 1e9)
    time.localtime = lambda secs=None: _localtime(clock.now() if secs is None else secs)
    time.gmtime = lambda secs=None: _gmtime(clock.now() if secs is None else secs)
    time.strftime = lambda fmt, t=None: _strftime(fmt, time.localtime() if t is None else t)
    time.ctime = lambda secs=None: _ctime(clock.now() if secs is None else secs)
    import datetime as dt

    class DateTime(dt.datetime):
        @classmethod
        def now(cls, tz=None):
            return cls.fromtimestamp(clock.now(), tz)

        @classmethod
        def today(cls):
            return cls.fromtimestamp(clock.now())
    dt.datetime = DateTime


_Popen = subprocess.Popen


class SyncPopen(_Popen):
    """What the harness starts in the background runs to its end within the step: a build, a ping, an evidence read."""

    def __init__(self, *args, **kwargs):
        kwargs.pop("start_new_session", None)
        piped = subprocess.PIPE in (kwargs.get("stdout"), kwargs.get("stderr"), kwargs.get("stdin"))
        super().__init__(*args, **kwargs)
        if not piped:
            self.wait()


def at(text):
    return time.mktime(time.strptime(text, "%Y-%m-%d %H:%M"))


def run(cmd, env, cwd, check=True, timeout=3600):
    r = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if check and r.returncode:
        raise RuntimeError(f"{' '.join(map(str, cmd))} failed ({r.returncode}): {r.stdout[-2000:]} {r.stderr[-2000:]}")
    return r


def commits(since, until):
    """[(epoch, sha)] of main's first-parent history up to `until`, oldest first."""
    out = subprocess.run(["git", "-C", REPO, "log", "--first-parent", "--format=%ct %H", "main"], capture_output=True,
                         text=True).stdout.split("\n")
    rows = sorted((int(line.split()[0]), line.split()[1]) for line in out if line.strip())
    return [r for r in rows if r[0] <= until]


def daemon_stub(real):
    """The daemon's loop body, as it stands in the copy under test, run once a pass: its pings. `--ensure` is nothing —
    the driver is the daemon — and the watchdog the driver runs in its own process."""
    text = open(real).read()
    head = [line for line in text.splitlines() if line.startswith(("HERE=", "every=", "age() {", "active() {"))]
    body = text[text.index("  any=0\n"):]
    body = body[:body.index('  [ "$any" = 0 ]')]
    return "#!/bin/sh\n# the simulation's daemon: one pass of the loop's pings (simrun.py)\n" \
           '[ "${1:-}" = "--ensure" ] && exit 0\n' + "\n".join(head) + "\n" + body


def mangle(path):
    return re.sub(r"[^A-Za-z0-9]", "-", path)


class Sim:
    def __init__(self, args):
        self.args = args
        self.out = os.path.abspath(args.out)
        self.project = os.path.join(self.out, "project")
        self.orch = os.path.join(self.project, ".claude", "orchestration")
        self.state = os.path.join(self.out, "state")
        self.home = os.path.join(self.out, "home")
        self.fake = os.path.join(self.out, "fake")
        self.clockfile = os.path.join(self.out, "clock")
        self.since, self.until = at(args.since), at(args.until)
        self.record = open(os.path.join(self.out, "sim.jsonl"), "a") if os.path.isdir(self.out) else None
        self.names = {}          # recorded session name -> simulated name
        self.last_norm = _real_time()

    # ------------------------------------------------------------------ the world

    def setup(self):
        os.makedirs(self.out)
        self.record = open(os.path.join(self.out, "sim.jsonl"), "a")
        self.history = commits(self.since, self.until)
        start = [sha for t, sha in self.history if t <= self.since][-1]
        # the project is a plain directory the replay writes each commit's changes into, never git's work tree: git
        # takes a file present in its tree back from a sparse pattern, and checked out the old harness over the copy
        subprocess.run(["git", "clone", "-q", "--shared", "-n", REPO, self.project], check=True)
        archive = subprocess.Popen(["git", "-C", self.project, "archive", start], stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", self.project, "--exclude=.claude/orchestration"], stdin=archive.stdout,
                       check=True)
        archive.wait()
        subprocess.run(["git", "-C", self.project, "update-ref", "--no-deref", "HEAD", start], check=True)
        self.head = start
        assert not os.path.exists(self.orch), "the archive left the harness of the old commit in place"
        shutil.copytree(self.args.orch, self.orch, symlinks=True,
                        ignore=shutil.ignore_patterns("state", "__pycache__", "*.bak", ".mcp.json"))
        stub = daemon_stub(os.path.join(self.orch, "warm_daemon.sh"))
        open(os.path.join(self.orch, "warm_daemon.sh"), "w").write(stub)
        for d in (self.state, os.path.join(self.orch, "state", "held"), self.home, self.fake):
            os.makedirs(d, exist_ok=True)
        memory = os.path.join(self.home, ".claude", "projects", mangle(self.project), "memory")
        if os.path.isdir(REAL_MEMORY):
            shutil.copytree(REAL_MEMORY, memory)
        os.makedirs(os.path.join(self.home, ".claude", "tasks", "orchestration-graph"), exist_ok=True)
        open(os.path.join(self.state, "deltas"), "w").write(self.args.deltas + "\n")
        if self.args.role_layers != "none":
            open(os.path.join(self.state, "role-layers"), "w").write("" if self.args.role_layers == "all"
                                                                     else self.args.role_layers + "\n")
        json.dump({"active": True, "kb": None, "counters": {}, "sessions": {}, "tasks": {}, "queue": [], "events": [],
                   "notes": [], "asks": {}}, open(os.path.join(self.state, "v2.json"), "w"))
        self.say("setup", orch=self.args.orch, start=start, commits=len([1 for t, _ in self.history if t > self.since]))

    def environment(self):
        env = {k: v for k, v in os.environ.items() if not k.startswith(("CLAUDE", "AI_AGENT", "ORCH_"))}
        env.update(PATH=os.path.join(SIM, "bin") + os.pathsep + os.environ["PATH"], HOME=self.home,
                   FAKE_ROOT=self.fake, SIM_CLOCK=self.clockfile, PYTHONPATH=os.path.join(SIM, "pylib"),
                   ORCH_PROJECT=self.project, ORCH_STATE_DIR=self.state,  # the held indexes where the live layout has them
                   ORCH_CONTROL="1", ORCH_PAUSE="0", ORCH_CACHE_CHECK="0", ORCH_SYNC="1", ORCH_ISABELLE_RUNS="0",
                   ORCH_MEM_AVAILABLE_GB="1000", ORCH_WORKERS="8", ORCH_STACK_POLL="0.01",
                   ORCH_LEDGER=os.path.join(self.orch, "owner-ledger.md"),
                   CODEX_SESSIONS=os.path.join(self.home, "codex"))
        return env

    def enter(self):
        """This process becomes part of the world: its environment, its clock, its background starts synchronous."""
        global CLOCK
        self.env = self.environment()
        os.environ.clear()
        os.environ.update(self.env)
        CLOCK = Clock(self.clockfile)
        CLOCK.set(self.since)
        patch_time(CLOCK)
        subprocess.Popen = SyncPopen
        sys.path.insert(0, self.orch)
        sys.path.insert(0, SIM)
        os.chdir(self.project)
        import v2
        import watchdog
        import fakeclaude
        import base_stack
        import manifest
        import digest
        self.v2, self.watchdog, self.fakeclaude = v2, watchdog, fakeclaude
        self.transcripts = v2.TRANSCRIPTS
        # The driver's process lives the whole run, where the watchdog's lives a pass: what it reads again every pass from
        # files that have not changed — every held file's digest (the structure check, each minute, three bases), every
        # fork's own requests (the rules' accounts) — is kept by the file's identity. Nothing the harness decides changes.
        held = digest.held_text
        memo = {}

        def held_text(path, level="statements", *a, **k):
            try:
                st = os.stat(path)
                key = (path, level, st.st_mtime_ns, st.st_size, st.st_ino, a, tuple(sorted(k.items())))
            except OSError:
                return held(path, level, *a, **k)
            if key not in memo:
                if len(memo) > 200_000:
                    memo.clear()
                memo[key] = held(path, level, *a, **k)
            return memo[key]
        for module in (digest, base_stack, manifest):
            if getattr(module, "held_text", None) is held:
                module.held_text = held_text
        own = watchdog.own_requests
        counted = {}

        def own_requests(s):
            path = v2.transcript(s.get("sid") or "")
            try:
                st = os.stat(path)
            except OSError:
                return own(s)
            key = (path, s.get("started"), st.st_mtime_ns, st.st_size)
            if key not in counted:
                counted[key] = own(s)
            return counted[key]
        watchdog.own_requests = own_requests

    def say(self, what, **fields):
        t = CLOCK.now() if CLOCK else None
        self.record.write(json.dumps(dict(t=t, what=what, **fields)) + "\n")
        self.record.flush()

    def normalize(self, only=None):
        """Every file the step wrote carries the step's simulated time, as the harness reads ages from file times —
        `only` the files a step of requests alone wrote, which it names."""
        t, since = CLOCK.t, self.last_norm - 1
        if only is not None:
            for p in dict.fromkeys(only):
                try:
                    os.utime(p, (t, t), follow_symlinks=False)
                except OSError:
                    pass
            return
        for root in (self.state, self.transcripts, self.fake):
            for dirpath, dirs, files in os.walk(root):
                for n in files + dirs:
                    p = os.path.join(dirpath, n)
                    try:
                        if os.lstat(p).st_mtime >= since:
                            os.utime(p, (t, t), follow_symlinks=False)
                    except OSError:
                        pass
            try:
                if os.lstat(root).st_mtime >= since:
                    os.utime(root, (t, t))
            except OSError:
                pass
        self.last_norm = _real_time()

    def sh(self, *cmd, check=True):
        r = run(["sh", os.path.join(self.orch, cmd[0]), *cmd[1:]], self.env, self.project, check=check)
        self.say("run", cmd=list(cmd), code=r.returncode, out=r.stdout[-600:], err=r.stderr[-600:])
        return r

    def advance(self, t):
        """main at time t: the last commit landed by then."""
        sha = [s for c, s in self.history if c <= t][-1]
        self.head_moved = sha != self.head
        if sha == self.head:
            return
        out = subprocess.run(["git", "-C", self.project, "diff", "--no-renames", "--name-status", "-z", self.head, sha],
                             capture_output=True, check=True).stdout.decode().split("\0")
        changed = []
        for status, path in zip(out[0::2], out[1::2]):
            if not path or path.startswith(".claude/orchestration/"):
                continue
            target = os.path.join(self.project, path)
            if status.startswith("D"):
                if os.path.lexists(target):
                    os.remove(target)
            else:
                os.makedirs(os.path.dirname(target), exist_ok=True)
                blob = subprocess.run(["git", "-C", self.project, "show", f"{sha}:{path}"], capture_output=True,
                                      check=True).stdout
                with open(target, "wb") as f:
                    f.write(blob)
            changed.append(path)
        subprocess.run(["git", "-C", self.project, "update-ref", "--no-deref", "HEAD", sha], check=True)
        self.say("commit", sha=sha, files=changed)
        self.head = sha

    # ------------------------------------------------------------------ the demand

    def demand(self):
        rows = [json.loads(line) for line in open(TIMELINE)]
        rows = [r for r in rows if r.get("role") in DEMAND and r.get("requests") and self.since <= r["started"] < self.until]
        rows.sort(key=lambda r: r["started"])
        if self.args.max_sessions:
            rows = rows[:self.args.max_sessions]
        firsts = {}
        for r in rows:
            q = r["requests"][0]
            if q["read"] > 0.5 * (q["read"] + q["write"]):
                firsts.setdefault(r["role"], []).append(q["write"])
        self.first_median = {role: int(statistics.median(v)) for role, v in firsts.items()}
        events = []
        for r in rows:
            events.append((r["started"], 0, "start", r, 0))
            for i, q in enumerate(r["requests"][1:], 1):
                events.append((max(q["sent"], r["started"] + 1), 1, "request", r, i))
            events.append(((r.get("last") or r["requests"][-1]["sent"]) + 2, 2, "end", r, 0))
        events.sort(key=lambda e: (e[0], e[1]))
        self.say("demand", sessions=len(rows), requests=sum(len(r["requests"]) for r in rows))
        return events

    def first_message(self, r):
        q = r["requests"][0]
        if q["read"] > 0.5 * (q["read"] + q["write"]):
            return q["write"]
        return self.first_median.get(r["role"], 8000)

    def launch(self, r):
        v2 = self.v2
        role, recorded = r["role"], r["name"]
        key = str(r.get("task") or recorded.split("-", 1)[-1])
        size = self.first_message(r)
        told = {}

        def prompt_of(name):
            s = v2.peek()["sessions"][name]
            who = "max" if role == "planner" else (v2.base_part(v2.medium_record(v2.ROLES[role]["origin"])[0])
                                                  or v2.ROLES[role]["origin"])
            stale = v2.stale_of(name, who)
            layered = (v2.peek()["sessions"].get(s.get("origin") or "") or {}).get("role") in ("role-layer", "role-churn")
            own = size - (int(len(v2.generic_protocol(role)) / CHARS) if layered and role in v2.LAYERABLE else 0)
            told.update(stale=stale, layered=layered, first=max(1500, own))
            head = (f"You are {name}, a session of the {role} (simulated from {recorded}).\n\nWhat has changed since what "
                    f"you hold loaded: {stale}\n\n")
            return head + "~" * int(max(1500, own) * CHARS - len(head))
        name = v2.launch(role, key, prompt_of, tree=None)
        if not name:
            self.say("refused", recorded=recorded, role=role)
            return
        s = v2.peek()["sessions"][name]
        world = self.fakeclaude.World()
        rec = world.sessions.get(s.get("sid") or "") or {}
        rec["start_ctx"] = rec.get("context", 0)
        world.save()
        self.names[recorded] = name
        self.say("start", recorded=recorded, name=name, role=role, origin=s.get("origin"), origin_sid=s.get("origin_sid"),
                 sid=s.get("sid"), head=self.head, **{k: s.get(k) for k in (
                     "origin_context", "pending_tokens", "delta_tokens", "superseded_tokens", "old_forms", "delta_shares")},
                 **told)

    def world(self):
        """The fake's registry as the driver last wrote it, or read again when a fake call has written it since."""
        stamp = tuple(os.stat(os.path.join(self.fake, f)).st_mtime_ns if os.path.exists(os.path.join(self.fake, f)) else 0
                      for f in ("sessions.json", "cache.json", "counter.json"))
        if getattr(self, "_world", None) is None or stamp != self._stamp:
            self._world = self.fakeclaude.World()
        return self._world

    def keep(self, world):
        from fakeclaude import save
        save("sessions.json", world.sessions)
        save("cache.json", world.cache)
        save("counter.json", world.counter)
        self._stamp = tuple(os.stat(os.path.join(self.fake, f)).st_mtime_ns
                            for f in ("sessions.json", "cache.json", "counter.json"))

    def request(self, r, i):
        name = self.names.get(r["name"])
        if not name:
            return
        v2, fc = self.v2, self.fakeclaude
        s = v2.peek()["sessions"].get(name) or {}
        sid = s.get("sid")
        world = self.world()
        rec = world.sessions.get(sid)
        if not rec:
            return
        q, q0 = r["requests"][i], r["requests"][0]
        growth = max(0, (q["read"] + q["write"]) - (q0["read"] + q0["write"]))
        ctx = rec["start_ctx"] + growth
        t = CLOCK.now()
        usage = world.request(sid, ctx, t, q["out"], prefix_sid=sid, blocks=2)
        world.counter["msgs"] = world.counter.get("msgs", 0) + 1
        mid = f"msg_{sid[:7]}_{world.counter['msgs']}"
        rec.update(context=ctx + q["out"], last=t)
        fc.record_request(sid, name, "work", t, usage)
        fc.append(sid, [fc.assistant(sid, t, mid, fc.api_model(s.get("model")), [{"type": "tool_use", "id": "t" + mid,
                                                                                  "name": "Bash", "input": {}}], usage),
                        fc.user(sid, t, [{"type": "tool_result", "tool_use_id": "t" + mid, "content": "ok"}])])
        self.keep(world)
        v2.hit(name)
        self.touched += [fc.transcript(sid), os.path.join(self.state, "hits", name)] + [
            os.path.join(self.fake, f) for f in ("sessions.json", "cache.json", "counter.json", "requests.jsonl")]

    def end(self, r):
        name = self.names.get(r["name"])
        if not name:
            return
        with self.v2.state() as st:
            if name in st["sessions"]:
                st["sessions"][name].update(state="done", ended=CLOCK.now())
        self.v2.seal(name)
        self.say("end", name=name)

    # ------------------------------------------------------------------ the machinery

    def build(self):
        for who in ("max", "xhigh", "high"):
            self.sh("base.sh", who, "build")
            self.normalize()
            self.sh("base.sh", who, "seal")
            self.normalize()
            self.sh("base.sh", who, "layer")
            self.normalize()
            self.say("built", who=who, layer=(self.v2.layer_record(who) or {}).get("sessionId"),
                     context=(self.v2.layer_record(who) or {}).get("context"))

    def machinery(self, daemon):
        v2, wd = self.v2, self.watchdog
        # the watchdog's own parts in its order (watch), those about the context machinery; the dispatch's after
        parts = [wd.holds] + ([wd.held_indexes] if hasattr(wd, "held_indexes") else []) + [wd.layers, wd.deltas]
        for part in parts + [v2.kb_care, v2.role_layer_care, v2.tidied]:
            wd.contained(part.__name__, part)
        if daemon:
            self.sh("warm_daemon.sh", check=False)

    def snapshot(self, accounts):
        v2, wd = self.v2, self.watchdog
        out = {}
        for who in v2.BASES:
            layer, delta = v2.layer_record(who) or {}, v2.delta_record(who) or {}
            b = dict(layer=layer.get("sessionId"), context=layer.get("context"),
                     parts=[(p.get("part"), p.get("sessionId"), p.get("context"), p.get("sealed"))
                            for p in layer.get("parts") or []],
                     delta=delta.get("sessionId"), delta_context=delta.get("context"), stack=len(delta.get("stack") or []),
                     tokens=delta.get("tokens"), superseded=delta.get("superseded"), old_forms=delta.get("old_forms"),
                     pending=v2.delta_pending(who))
            if accounts and layer.get("parts"):
                with_suppress = {}
                try:
                    with_suppress["carried_parts"] = wd.carried_parts(who)
                    with_suppress["refresh_plan"] = wd.refresh_plan(who)
                    if delta:
                        with_suppress["pending_paid"] = wd.pending_paid(who, delta, v2.delta_pending(who))
                        with_suppress["stack_waste"] = wd.stack_waste(who, delta)
                except Exception as e:  # noqa: BLE001
                    with_suppress["error"] = repr(e)
                b.update(with_suppress)
            out[who] = b
        st = v2.peek()
        out["roles"] = {role: dict(rec, layer_of=v2.role_layer_of(role), churn_of=v2.role_churn_of(role))
                        for role, rec in (st.get("role_layers") or {}).items()}
        out["kb"] = st.get("kb")
        self.say("snapshot", **out)

    def go(self):
        self.setup()
        self.enter()
        started = _real_time()
        self.build()
        events = self.demand()
        every, daemon_every = self.args.every, self.args.daemon_every
        t = self.since
        next_pass, next_daemon, next_account = t, t, t
        i = 0
        while t <= self.until and (i < len(events) or t < self.until):
            step = min(next_pass, events[i][0] if i < len(events) else self.until + 1)
            if step > self.until:
                break
            step = CLOCK.set(step)  # later, when the sessions of the step before took the clock past it
            self.advance(step)
            self.touched, only_requests = [], True
            while i < len(events) and events[i][0] <= step:
                _, _, kind, r, n = events[i]
                i += 1
                only_requests = only_requests and kind == "request"
                try:
                    if kind == "start":
                        self.launch(r)
                    elif kind == "request":
                        self.request(r, n)
                    else:
                        self.end(r)
                except Exception as e:  # noqa: BLE001  the demand goes on; what failed is recorded
                    import traceback
                    self.say("error", kind=kind, recorded=r.get("name"), error=repr(e), trace=traceback.format_exc()[-1500:])
            if step >= next_pass:
                self.machinery(daemon=step >= next_daemon)
                if step >= next_daemon:
                    next_daemon = step + daemon_every
                self.normalize()
                self.snapshot(accounts=step >= next_account)
                if step >= next_account:
                    next_account = step + 900
                next_pass = step + every
            else:
                self.normalize(only=self.touched if only_requests and not self.head_moved else None)
            t = step
        self.say("done", real_seconds=round(_real_time() - started), events=i)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("orch")
    p.add_argument("out")
    p.add_argument("--since", default="2026-09-21 21:50")
    p.add_argument("--until", default="2026-09-22 23:00")
    p.add_argument("--every", type=int, default=60)
    p.add_argument("--daemon-every", type=int, default=300)
    p.add_argument("--deltas", default="max xhigh high")
    p.add_argument("--role-layers", default="all")
    p.add_argument("--max-sessions", type=int, default=0)
    Sim(p.parse_args()).go()


if __name__ == "__main__":
    main()
