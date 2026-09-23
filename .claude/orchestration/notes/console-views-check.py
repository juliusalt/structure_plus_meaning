#!/usr/bin/env python3
"""Render every view of the console over the run's real state, without a browser or a network, and report what each
view showed wrong (console-views-check.js says what counts). The real server answers through the test transport
(console-test-transport.py: its handlers over pipes); the page's actual script renders in a stand-in DOM. The requests
each view makes are found by rendering: what a view asked for and the map lacked is asked of the server, and the views
rendered again, until nothing is missing.

    python3 -B .claude/orchestration/notes/console-views-check.py [VIEW...]

With no VIEW: every tab, the session with the most requests among the newest producers, the newest implementer's or
fixer's, the task landed last and the highest-numbered task. It exits 1 when a view showed something wrong.
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORCH = HERE.parent
TOKEN = "views-check"
TABS = ["now", "graph", "machine", "bases", "trains", "sessions", "tasks", "costs", "log", "control"]


def default_views():
    st = json.load(open(ORCH / "state/v2.json"))
    producers = [s for s in st["sessions"].values() if s.get("role") in ("fixer", "implementer")]
    newest = sorted(producers, key=lambda s: s.get("started") or 0)[-12:]
    views = list(TABS)
    if newest:
        views.append("sessions/" + newest[-1]["name"])
    try:
        lq = json.load(open(ORCH / "state/landing-queue.json"))
        landed = max((t for t, e in lq.items() if e.get("what") == "landed"), key=lambda t: lq[t].get("decided") or 0)
        views.append("tasks/" + landed)
    except (OSError, ValueError):
        pass
    tasks = [t for t in st["tasks"] if t.isdigit()]
    if tasks:
        views.append("tasks/" + max(tasks, key=int))
    return views, [s["name"] for s in newest]


class Server:
    def __init__(self):
        env = dict(os.environ, ORCH_DASHBOARD_TOKEN=TOKEN)
        self.p = subprocess.Popen([sys.executable, "-B", str(HERE / "console-test-transport.py"), "--port", "0"],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                                  env=env, cwd=ORCH.parent.parent)
        self.p.stdout.readline()  # its address

    def get(self, key):
        sep = "&" if "?" in key else "?"
        request = f"GET {key}{sep}token={TOKEN} HTTP/1.0\r\nHost: 127.0.0.1:8765\r\n\r\n"
        self.p.stdin.write(json.dumps({"request": request}) + "\n")
        self.p.stdin.flush()
        while True:
            line = self.p.stdout.readline()
            if not line:
                raise SystemExit("the console's transport ended")
            if line.startswith("{"):
                break
        head, body = json.loads(line)["response"].split("\r\n\r\n", 1)
        return [int(head.split()[1]), json.loads(body)]

    def close(self):
        self.p.terminate()
        self.p.wait(5)


def main():
    views = sys.argv[1:]
    extra = []
    if not views:
        views, recent = default_views()
        extra = recent
    server, answers = Server(), {}
    try:
        with tempfile.TemporaryDirectory() as temp:
            table = os.path.join(temp, "answers.json")
            if extra:  # the most requests among the newest producers: its conversation is the longest to render
                rows = server.get("/api/sessions")[1]
                answers["/api/sessions"] = [200, rows]
                most = max((r for r in rows if r["name"] in extra), key=lambda r: r.get("requests") or 0, default=None)
                if most and "sessions/" + most["name"] not in views:
                    views.append("sessions/" + most["name"])
            for _ in range(6):
                json.dump(answers, open(table, "w"))
                done = subprocess.run(["node", str(HERE / "console-views-check.js"), table, *views],
                                      capture_output=True, text=True, timeout=120)
                if done.returncode:
                    raise SystemExit(done.stderr[-4000:])
                out = json.loads(done.stdout)
                if not out["missing"]:
                    break
                for key in out["missing"]:
                    answers[key] = server.get(key)
    finally:
        server.close()
    bad = False
    for view, r in out["report"].items():
        mark = "ok " if not r["problems"] else "BAD"
        bad |= bool(r["problems"])
        print(f"{mark} {view:28} {r['words']:6} words" + "".join("\n      " + p for p in r["problems"]))
    for p in out["problems"]:
        bad = True
        print("BAD", p[:2000])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
