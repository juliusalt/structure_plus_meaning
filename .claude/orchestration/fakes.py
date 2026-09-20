"""A throwaway world for the orchestration's tests: a project, a home, a state directory and a fake `claude` that keeps
a session listing and records every call. No Claude session is launched and nothing of the real project is touched.

Scripts run in it through World.run, with the environment every part reads: ORCH_PROJECT, ORCH_STATE_DIR, HOME (the
task lists and transcripts under it), ORCH_PAUSE=0 and ORCH_CACHE_CHECK=0 (no waits, no background cache check),
ORCH_SYNC=1 (a command's dispatch runs before it returns) and ORCH_EPISODE_GAP=0.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent

FAKE = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
root = os.environ["FAKE_ROOT"]
args = sys.argv[1:]
agents, registry = os.path.join(root, "agents.json"), os.path.join(root, "sessions.json")
load = lambda p: json.load(open(p)) if os.path.exists(p) else []
with open(os.path.join(root, "calls.jsonl"), "a") as f:
    f.write(json.dumps({"args": args, "env": sorted(k for k in os.environ if k.startswith(("CLAUDE", "AI_AGENT")))}) + "\n")
rows = load(agents)
if args[:2] == ["agents", "--json"]:
    print(json.dumps(rows))
elif args[:1] == ["stop"]:
    json.dump([r for r in rows if r["id"] != args[1]], open(agents, "w"))
elif args[:1] == ["rm"]:
    pass
elif args[:1] == ["attach"]:
    with open(os.path.join(root, "attached"), "a") as f:
        f.write(args[1] + "\n")
    n = len(open(os.path.join(root, "attached")).read().split())
    action = os.path.join(root, f"action{n}.sh")
    if os.path.exists(action):
        subprocess.run(["sh", action], check=True)
elif "--bg" in args:
    known = load(registry)
    if "-n" in args:
        name = args[args.index("-n") + 1]
        if os.path.exists(os.path.join(root, "fail-start")):
            sys.exit(1)
        n = len(known) + 1
        rec = {"name": name, "id": f"id{n}", "sessionId": f"sid{n}"}
        json.dump(known + [rec], open(registry, "w"))
    else:
        sid = args[args.index("--resume") + 1]
        rec = next(r for r in known if r["sessionId"] == sid)
    rows = [r for r in rows if r["name"] != rec["name"]] + [dict(rec, kind="background", status="busy", state="working",
                                                                   cwd=os.environ["ORCH_PROJECT"])]
    json.dump(rows, open(agents, "w"))
else:
    sys.exit("unexpected: " + " ".join(args))
'''

BRIEF = """Kind: build
Serves: the readiness of calls, now because the selection rests on it
Deliverable: `theories/Ready.thy`, the readiness theory
Acceptance: `true`
Inputs: `theories/Base.thy:1-40`, `Base.base_def`, and the decision in `DECISIONS.md`
Decided: readiness is a path
Plan:
1. define readiness over paths
2. prove it sound
Yours: the proof
Planner's: a change of the statement
While checks run: the documentation
Size: about 120K tokens of work
"""

BRIEF_TASK = """Kind: brief
Serves: the reach of a state, detailed into build tasks
Deliverable: a build task for the reach theory and its review task
Acceptance: the briefs are in form
Inputs: `DECISIONS.md`
Decided: reach is a closure
Plan:
1. name the reach's sources
2. brief the build task and its review
Size: about 40K tokens of work
"""

REVIEW_TASK = """Kind: review
Reviews: `{task}`
Serves: the reach theory's acceptance
Deliverable: the verdict
Acceptance: the verdict recorded
Inputs: the task's brief
Plan:
1. check the definition against the decided closure
2. check reuse of the founding theories
Size: about 30K tokens of work
"""

RESULT = """Status: {status}
## Produced
`theories/Ready.thy`
## Decisions
none
## Plan as followed
as briefed
## Remains
nothing
"""

PLANNER_STATE = "# Planner state\n\n## Graph\ng\n\n## Decisions\nd\n\n## Delivered\n-\n\n## Open\n-\n\n## Now\nwaiting\n"


class World:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.project, self.state, self.home = self.root / "project", self.root / "state", self.root / "home"
        for d in (self.project / "theories", self.state, self.home, self.root / "bin"):
            d.mkdir(parents=True)
        (self.root / "bin/claude").write_text(FAKE)
        (self.root / "bin/claude").chmod(0o755)
        self.tasks = self.home / ".claude/tasks/orchestration-graph"
        self.transcripts = self.home / ".claude/projects" / str(self.project).replace("/", "-").replace("_", "-")
        self.transcripts.mkdir(parents=True)
        self.env = {k: v for k, v in os.environ.items() if not k.startswith(("CLAUDE", "AI_AGENT", "ORCH_"))}
        self.env.update(PATH=str(self.root / "bin") + os.pathsep + os.environ["PATH"], HOME=str(self.home),
                        FAKE_ROOT=str(self.root), ORCH_PROJECT=str(self.project), ORCH_STATE_DIR=str(self.state),
                        ORCH_ISABELLE_RUNS="0",  # no run of this machine is this world's
                        ORCH_WORKERS="8",  # the slots' own capacity; the owner's rate is a setting, tested apart
                        ORCH_EPISODE_GAP="0", ORCH_URGENT_GAP="0",
                        ORCH_ACTIVE_CONTEXT=str(self.state / "active-context.json"),
                       
                        ORCH_PAUSE="0", ORCH_CACHE_CHECK="0", ORCH_SYNC="1",
                        CODEX_SESSIONS=str(self.home / "codex"), ORCH_LEDGER=str(self.root / "owner-ledger.md"))

    def close(self):
        self.temp.cleanup()

    # ------------------------------------------------------------ running

    def run(self, script, *args, stdin=None, env=None, timeout=60):
        """Run one of the orchestration's scripts in this world; (returncode, stdout, stderr)."""
        path = str(HERE / script)
        cmd = [sys.executable, path, *args] if script.endswith(".py") else ["sh", path, *args]
        out = subprocess.run(cmd, input=stdin, capture_output=True, text=True, timeout=timeout,
                             env=dict(self.env, **(env or {})), cwd=self.project)
        return out.returncode, out.stdout, out.stderr

    def v2(self, *args, env=None):
        return self.run("v2.py", *args, env=env)[1].strip()

    def hook(self, script, mode, hook, env=None):
        """Run a hook with its JSON input; (returncode, parsed JSON output or None, stderr)."""
        code, out, err = self.run(script, mode, stdin=json.dumps(hook), env=env)
        return code, (json.loads(out) if out.strip() else None), err

    # ------------------------------------------------------------ the fake claude

    def calls(self, first=None):
        path = self.root / "calls.jsonl"
        rows = [json.loads(l) for l in path.read_text().splitlines()] if path.exists() else []
        return [c for c in rows if first is None or c["args"][:1] == [first] or (first == "--bg" and "--bg" in c["args"])]

    def rows(self):
        path = self.root / "agents.json"
        return json.loads(path.read_text()) if path.exists() else []

    def set_rows(self, rows):
        (self.root / "agents.json").write_text(json.dumps(rows))

    def set_status(self, name, status):
        self.set_rows([dict(r, status=status) if r["name"] == name else r for r in self.rows()])

    # ------------------------------------------------------------ state and fixtures

    def base(self, who="max", sid="base-sid"):
        (self.state / f"{who}-base.json").write_text(json.dumps(
            {"sessionId": sid, "model": "claude-opus-5[1m]", "effort": "max", "name": f"{who}-base"}))

    def task(self, tid, description=BRIEF, subject="Readiness of calls", **fields):
        self.tasks.mkdir(parents=True, exist_ok=True)
        t = {"id": tid, "subject": subject, "description": description, "status": "pending", "blocks": [], "blockedBy": []}
        t.update(fields)
        (self.tasks / f"{tid}.json").write_text(json.dumps(t))

    def read_task(self, tid):
        return json.loads((self.tasks / f"{tid}.json").read_text())

    def st(self):
        path = self.state / "v2.json"
        return json.loads(path.read_text()) if path.exists() else {}

    def set_st(self, **fields):
        st = {"active": True, "kb": None, "counters": {}, "sessions": {}, "tasks": {}, "queue": [], "events": [],
              "notes": [], "asks": {}}
        st.update(self.st())
        st.update(fields)
        (self.state / "v2.json").write_text(json.dumps(st))

    def session(self, name, role, sid, state="working", live=True, status="busy", warm=True, **fields):
        """A session of a role, as if launched earlier: in the orchestration's state, in the fake's registry and, when
        live, in the listing; warm when its last hit is fresh."""
        registry = self.root / "sessions.json"
        known = json.loads(registry.read_text()) if registry.exists() else []
        registry.write_text(json.dumps(known + [{"name": name, "id": f"id-{sid}", "sessionId": sid}]))
        if live:
            self.set_rows([r for r in self.rows() if r["name"] != name] + [
                {"name": name, "id": f"id-{sid}", "sessionId": sid, "kind": "background", "status": status,
                 "state": "working", "cwd": str(self.project)}])
        rec = dict(dict(name=name, role=role, sid=sid, id=f"id-{sid}", state=state, model="claude-opus-5[1m]",
                        effort="max", settings="worker-settings.json", origin="max", started=time.time(),
                        sealed=not live), **fields)
        st = self.st() or {}
        sessions = st.get("sessions", {})
        sessions[name] = rec
        self.set_st(sessions=sessions)
        if warm:
            self.hit(name)
        return rec

    def kb(self, name="kb-1", sid="kbsid"):
        """A sealed, warm knowledge base."""
        self.session(name, "kb", sid, state="done", live=False, kb_state="sealed", settings="planner-settings.json")
        self.set_st(kb=name, counters=dict(self.st().get("counters", {}), kb=int(name.split("-")[1])))

    def hit(self, name, age=0.0):
        (self.state / "hits").mkdir(exist_ok=True)
        path = self.state / "hits" / name
        path.write_text("")
        os.utime(path, (time.time() - age, time.time() - age))

    def reply(self, sid, text, ago=0.0):
        """The session's transcript ends with this reply."""
        return self.transcript(sid, [assistant("r1", iso(time.time() - ago), [{"type": "text", "text": text}])])

    def as_session(self, sid):
        """The environment of a command run inside that session."""
        return {"CLAUDE_CODE_SESSION_ID": sid}

    def mail(self, name):
        path = self.state / "mail" / f"{name}.jsonl"
        return [json.loads(l) for l in path.read_text().splitlines()] if path.exists() else []

    def write(self, rel, text):
        path = self.project / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def transcript(self, sid, records):
        path = self.transcripts / f"{sid}.jsonl"
        path.write_text("".join(json.dumps(r) + "\n" for r in records))
        return str(path)

    def wait_for(self, path, seconds=20):
        end = time.time() + seconds
        while time.time() < end:
            if Path(path).exists():
                return True
            time.sleep(0.1)
        return False

    def git(self, *args, cwd=None):
        return subprocess.run(["git", *args], cwd=cwd or self.project, capture_output=True, text=True, check=True).stdout

    def repository(self):
        """The project as a git repository with a bare origin, one commit in both."""
        remote = self.root / "origin.git"
        subprocess.run(["git", "init", "-q", "--bare", str(remote)], check=True)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.org")
        self.git("config", "user.name", "t")
        self.write("README", "x\n")
        self.git("add", "README")
        self.git("commit", "-q", "-m", "start")
        self.git("remote", "add", "origin", str(remote))
        self.git("push", "-q", "origin", "main")
        return remote


def assistant(msg_id, ts, content=None, usage=None, model="claude-opus-5"):
    m = {"id": msg_id, "model": model, "content": content or [{"type": "text", "text": "ok"}]}
    if usage:
        m["usage"] = usage
    return {"type": "assistant", "timestamp": ts, "message": m}


def iso(epoch):
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(epoch)) + f".{int(epoch * 1000) % 1000:03d}Z"
