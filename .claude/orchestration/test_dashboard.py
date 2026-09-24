#!/usr/bin/env python3
"""The run's console (dashboard.py): its views read the harness's own records, and its controls need the token."""
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402

TOKEN = "t0ken-for-the-test"


class ConsoleTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.base()
        self.w.kb()
        self.w.task("7", subject="The locus")
        self.w.set_st(queue=["7"], tasks={"7": {"stage": "running", "kind": "build", "session": "implement-7"}})
        t0 = int(time.time()) - 300  # whole seconds, as the transcript's times are read
        self.w.session("implement-7", "implementer", "s7", task="7", started=t0)
        self.w.transcript("s7", [
            fakes.assistant("m1", fakes.iso(t0 + 5), [
                {"type": "thinking", "thinking": "", "signature": "sig"},
                {"type": "tool_use", "id": "a", "name": "Bash", "input": {"command": "v2.py result 7",
                                                                           "description": "record"}},
                {"type": "tool_use", "id": "b", "name": "Bash", "input": {"command": "cat theories/A.thy"}},
                {"type": "tool_use", "id": "e", "name": "TaskCreate", "input": {"subject": "one; two && three",
                                                                                 "description": "a\nb\nc"}}],
                usage={"cache_read_input_tokens": 500000, "output_tokens": 900}),
            {"type": "user", "timestamp": fakes.iso(t0 + 6), "message": {"content": [
                {"type": "tool_result", "tool_use_id": "a", "content": "refused: the result has no `Acceptance` part"},
                {"type": "tool_result", "tool_use_id": "b", "content": "theory A imports Main begin end"}]}},
            {"type": "attachment", "timestamp": fakes.iso(t0 + 6), "attachment": {
                "type": "hook_additional_context", "toolUseID": "b", "content": ["Since your last production: 1 of 3."]}},
            fakes.assistant("m2", fakes.iso(t0 + 20), [{"type": "tool_use", "id": "c", "name": "Bash", "input": {
                "command": ".claude/orchestration/v2.py change <<'EOF'\n=== write theories/A.thy\nx\n=== row A\nrow\nEOF"}}]),
            {"type": "user", "timestamp": fakes.iso(t0 + 21), "message": {"content": [
                {"type": "tool_result", "tool_use_id": "c", "content": "written: theories/A.thy (whole)"}]}},
            {"type": "assistant", "timestamp": fakes.iso(t0 + 22), "message": {"id": "s1", "model": "<synthetic>",
                                                                              "content": [{"type": "text", "text": "No response requested."}]}},
            fakes.assistant("m3", fakes.iso(t0 + 30), [{"type": "tool_use", "id": "d", "name": "Bash", "input": {
                "command": "python3 -B tools/probe_theories.py --theory A --timeout 60; grep -n x theories/A.thy"}}]),
        ])
        self.w.write(".build/tasks/7/result.md", "Status: partial\n")
        (self.w.state / "v2.log").write_text("2026-09-23T10:00:00 the train of tasks 7 is checked together\n")
        self.watched = self.w.root / "watched.py"
        self.watched.write_text("x = 1\n")
        self.built = self.w.root / "built.txt"  # what the console asked base.sh to build (ORCH_DASHBOARD_BUILD)
        stub = self.w.root / "build-stub"
        stub.write_text(f"#!/bin/sh\necho \"$@\" >> {self.built}\n")
        stub.chmod(0o755)
        self.proc = subprocess.Popen([sys.executable, str(HERE / "notes/console-test-transport.py"), "--port", "0"],
                                     env=dict(self.w.env, ORCH_DASHBOARD_TOKEN=TOKEN, ORCH_DASHBOARD_KEEP="0",
                                              ORCH_DASHBOARD_BUILD=str(self.w.root / "build-stub"),
                                              ORCH_DASHBOARD_WATCH=str(self.watched)), stdout=subprocess.PIPE, stdin=subprocess.PIPE,
                                     stderr=subprocess.PIPE, text=True, cwd=self.w.project)
        line = self.proc.stdout.readline()
        self.assertIn("the run's console: http://127.0.0.1:", line, self.proc.stderr.read() if not line else "")
        self.base = line.split("console: ")[1].split("/?")[0]

    def tearDown(self):
        self.proc.terminate()
        self.proc.wait(5)
        self.proc.stdin.close()
        self.proc.stdout.close()
        self.proc.stderr.close()
        self.w.close()

    def request(self,method,path,headers=None,body=''):
        headers={'Host':'127.0.0.1:8765',**(headers or {})}
        request=f'{method} {path} HTTP/1.0\r\n'+''.join(f'{k}: {v}\r\n' for k,v in headers.items())+'\r\n'+body
        self.proc.stdin.write(json.dumps({'request':request})+'\n');self.proc.stdin.flush()
        while True:
            line=self.proc.stdout.readline()
            if not line:self.fail('console transport ended: '+self.proc.stderr.read())
            if line.startswith('{'):break
        response=json.loads(line)['response']
        head,body=response.split('\r\n\r\n',1)
        code=int(head.splitlines()[0].split()[1])
        return code,json.loads(body) if 'application/json' in head else body

    def get(self,path,token=TOKEN,host=None):
        sep='&' if '?' in path else '?'
        return self.request('GET',path+(f'{sep}token={token}' if token else ''),{'Host':host} if host else {})

    def post(self,body,header=True):
        text=json.dumps(body)
        return self.request('POST',f'/api/control?token={TOKEN}',
                            {'Content-Type':'application/json','Content-Length':len(text.encode()),
                             **({'X-Token':TOKEN} if header else {})},text)

    def test_every_request_needs_the_token_and_the_local_host(self):
        self.assertEqual(self.get("/api/overview", token=None)[0], 403)
        self.assertEqual(self.get("/api/overview", token="wrong")[0], 403)
        self.assertEqual(self.get("/api/overview", host="evil.example:80")[0], 403)   # another host: refused
        self.assertEqual(self.post({"action": "dispatch"}, header=False)[0], 403)    # a control needs the header
        code, page = self.get("/")
        self.assertEqual(code, 200)
        self.assertIn(f'const TOKEN = "{TOKEN}"', page)

    def test_the_run_its_sessions_and_a_session_whole(self):
        code, o = self.get("/api/overview")
        self.assertEqual(code, 200)
        self.assertEqual([t["id"] for t in o["queue"]], ["7"])
        self.assertIn("measure-bound", o["switches"])
        self.assertIn("implement-7", [s["name"] for s in o["live"]])
        code, rows = self.get("/api/sessions")
        row = next(r for r in rows if r["name"] == "implement-7")
        self.assertEqual((row["requests"], row["calls"], row["refused"]), (3, 5, 1))  # the synthetic entry is none
        self.assertEqual(row["first_change"], 2)                                 # one request before its first change
        # the probe after a clean change is joinable; another tool's call is one operation, whatever its input holds
        self.assertEqual((row["ops"], row["joinable"]), (round((3 + 2 + 2) / 3, 2), 1))
        code, d = self.get("/api/session?name=implement-7")
        reqs = [i for i in d["items"] if i["kind"] == "request"]
        self.assertEqual(len(reqs[0]["calls"]), 3)                               # the batch, as it was made
        self.assertEqual(reqs[0]["thinking"], 1)
        refused = reqs[0]["calls"][0]
        self.assertIn("the result has no `Acceptance` part", refused["refused"])
        self.assertEqual(reqs[0]["calls"][1]["notes"], ["Since your last production: 1 of 3."])
        self.assertEqual(d["summary"]["produced"], ["theories/A.thy", "THEORY_MAP.md row A"])
        # where its time went, from the transcript's own times: each request's model time runs from what it answered
        # being ready (its launch, the last result before) to its last block, its calls' time from there to their
        # last result; the last call has no result yet, and is what it is doing now
        self.assertEqual([(q["model_s"], q["tools_s"]) for q in reqs], [(5, 1), (14, 1), (9, 0)])
        self.assertTrue(reqs[2]["open"])
        self.assertEqual((row["model_s"], row["tools_s"], row["idle_s"]), (28, 2, 0))
        self.assertEqual((row["last_call"], row["last_call_open"]),
                         ("python3 -B tools/probe_theories.py --theory A --timeout 60; grep -n x theories/A.thy", True))

    def test_a_call_refused_stopped_by_the_guard_or_failed_is_said_for_what_it_is(self):
        # 96% of the calls counted failed on 09-19/23 were the harness's guard stopping them before they ran
        t0 = int(time.time()) - 200
        self.w.session("fix-9", "fixer", "f9", task="9", started=t0)
        self.w.transcript("f9", [
            fakes.assistant("q1", fakes.iso(t0 + 5), [
                {"type": "tool_use", "id": "r", "name": "Bash", "input": {"command": "v2.py change"}},
                {"type": "tool_use", "id": "s", "name": "Bash", "input": {"command": "sleep 60"}},
                {"type": "tool_use", "id": "f", "name": "Bash", "input": {"command": "false"}}]),
            {"type": "user", "timestamp": fakes.iso(t0 + 6), "message": {"content": [
                {"type": "tool_result", "tool_use_id": "r", "content": "refused, and nothing was changed", "is_error": True},
                {"type": "tool_result", "tool_use_id": "s", "content": "Waiting is refused (sleep, wait loops)", "is_error": True},
                {"type": "tool_result", "tool_use_id": "f", "content": "Exit code 1\nboom", "is_error": True}]}}])
        row = next(r for r in self.get("/api/sessions")[1] if r["name"] == "fix-9")
        self.assertEqual((row["refused"], row["stopped"], row["failed"]), (1, 1, 1))
        # and the report reads the same, every section of it, inside the same world
        done = subprocess.run([sys.executable, "-B", str(HERE / "console_report.py"), "--since", "all", "--quick"],
                              capture_output=True, text=True, timeout=120, env=self.w.env, cwd=self.w.project)
        self.assertEqual(done.returncode, 0, done.stderr)
        for head in ("== FINDINGS", "== RUN", "== SESSIONS", "== PIPELINE", "== MACHINE", "== CHECKS", "== BATCHING",
                     "== DELIVERY: 2 refused, 1 stopped by the guard, 1 failed", "== COSTS", "== BASES", "== LOG"):
            self.assertIn(head, done.stdout)
        self.assertRegex(done.stdout, r"stopped by the guard ×1 \(\w+ 1\) \[[0-9a-f]+\]: Waiting is refused")
        self.assertIn("implement-7", done.stdout)                   # the live session, and its call running now

    def test_the_session_list_reads_a_transcript_once(self):
        # no whole conversation is kept here (ORCH_DASHBOARD_KEEP=0): the list is served from the summaries alone
        self.get("/api/sessions")
        parsed = self.get("/api/version")[1]["parses"]
        self.assertGreater(parsed, 0)
        self.get("/api/sessions")
        self.assertEqual(self.get("/api/version")[1]["parses"], parsed)       # nothing read again
        self.get("/api/session?name=implement-7")
        self.assertEqual(self.get("/api/version")[1]["parses"], parsed + 1)   # the whole, read when asked
        self.get("/api/sessions")
        self.assertEqual(self.get("/api/version")[1]["parses"], parsed + 1)

    def test_the_bases_their_parts_and_how_warm_each_is(self):
        st, now = self.w.state, time.time()
        self.w.base("max", sid="stable-sid")
        base = json.loads((st / "max-base.json").read_text())
        (st / "max-base.json").write_text(json.dumps(dict(base, context=300000, sealed="2026-09-23T01:00:00")))
        (st / "max-layer.json").write_text(json.dumps(dict(base, sessionId="layer-sid", name="max-layer", base="stable-sid",
                                                           context=450000, sealed="2026-09-23T02:00:00")))

        def mark(name, age, text=""):
            (st / name).write_text(text)
            os.utime(st / name, (now - age, now - age))
        mark("max-base.hit", 1000)        # what the roles fork, the layer: read 1000 s ago
        mark("max-base.used", 100)
        mark("max-stable.hit", 4000)      # the stable base under it: cold, and missed twice
        mark("max-stable.miss", 0, "x\nx\n")
        mark("warm.beat", 0)              # the daemon runs
        at = lambda ago: time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(now - ago))
        (st / "warm.log").write_text(
            f"{at(900)} warm max: OK   session fork aa of base bb: first own request cache_read=450000 cache_write=2000\n"
            f"{at(800)} warm max stable: MISS session fork cc of base dd: first own request cache_read=9000 cache_write=300000\n")
        self.w.kb("kb-1", "kbsid")
        self.w.hit("kb-1", age=100)
        with open(st / "v2.log", "a") as f:
            f.write(f"{at(700)} ping kb-1: OK   session fork ee of base ff: first own request cache_read=500000 "
                    "cache_write=1000\n")
        code, d = self.get("/api/bases")
        self.assertEqual(code, 200)
        self.assertTrue(d["daemon"])
        b = next(x for x in d["bases"] if x["who"] == "max")
        stable, layer = b["parts"]
        self.assertEqual((b["forks"], stable["own"], layer["own"], layer["forked"]), ("layer", 300000, 150000, True))
        self.assertTrue(layer["entry"]["warm"])
        self.assertAlmostEqual(layer["entry"]["expires_in"], 3600 - 1000, delta=30)       # an hour after its read
        self.assertAlmostEqual(layer["entry"]["next_ping"], d["rules"]["warm_every"] - 1000, delta=30)
        self.assertEqual((layer["entry"]["last_ping"]["ok"], layer["entry"]["last_ping"]["cost"]), (True, 45000 + 4000))
        self.assertEqual((stable["entry"]["warm"], stable["entry"]["misses"], stable["entry"]["next_ping"]), (False, 2, None))
        self.assertIn("missed", stable["entry"]["why"])                                    # never pinged after a miss
        kb = next(h for h in d["held"] if h["name"] == "kb-1")
        self.assertEqual(kb["held"], "the knowledge base")
        self.assertAlmostEqual(kb["entry"]["next_ping"], d["rules"]["ping_age"] - 100, delta=30)
        self.assertEqual((kb["pings"], kb["ping_cost"]), (1, 52000))
        (st / "warm.beat").unlink()       # the daemon gone: nothing is pinged, and each entry says so
        code, d = self.get("/api/bases")
        layer = next(x for x in d["bases"] if x["who"] == "max")["parts"][1]
        self.assertIsNone(layer["entry"]["next_ping"])
        self.assertIn("daemon", layer["entry"]["why"])
        self.assertIsNone(next(h for h in d["held"] if h["name"] == "kb-1")["entry"]["next_ping"])

    def test_building_it_from_the_console(self):
        st, now = self.w.state, time.time()
        self.w.base("max", sid="stable-sid")
        base = json.loads((st / "max-base.json").read_text())
        (st / "max-base.json").write_text(json.dumps(dict(base, context=300000, sealed="2026-09-23T01:00:00")))
        (st / "max-layer.json").write_text(json.dumps(dict(base, sessionId="layer-sid", name="max-layer", base="stable-sid",
                                                           context=450000, sealed="2026-09-23T02:00:00")))

        def mark(name, age):
            (st / name).write_text("")
            os.utime(st / name, (now - age, now - age))
        said = lambda body: self.post(dict(body, action="build"))[1]["said"]
        self.assertIn("not switched to deltas", said({"part": "delta", "who": "max"}))
        (st / "deltas").write_text("max\n")
        mark("max-base.hit", 5000)          # what its roles fork, the layer: cold
        self.assertIn("cold", said({"part": "delta", "who": "max"}))        # a delta over it would write it again
        (st / "role-layers").write_text("")  # every role
        code, d = self.get("/api/bases")
        self.assertNotIn("should", d)                                        # the owner, 2026-09-24: not shown
        self.assertIn("going", d)
        mark("max-base.hit", 10)
        self.assertIn("started", said({"part": "delta", "who": "max"}))
        mark("max-layer.building", 0)
        self.assertIn("is going", said({"part": "layer", "who": "max"}))    # one build over a layer at a time
        (st / "max-layer.building").unlink()
        self.assertIn("started", said({"part": "layer", "who": "max"}))
        self.w.wait_for(self.built)
        for _ in range(50):
            if len(self.built.read_text().split("\n")) > 2:
                break
            time.sleep(0.1)
        self.assertEqual(self.built.read_text().split("\n")[:2], ["max delta", "max layer"])
        # every base's layer, one after another, in one process; a second is refused while it goes
        self.w.base("high", sid="high-sid")
        self.built.write_text("")
        mark("high-layer.building", 0)
        self.assertIn("refused: a build over the high layer is going", said({"part": "layers"}))
        (st / "high-layer.building").unlink()
        (st / "layers-build.json").write_text(json.dumps({"pid": os.getpid(), "started": now, "order": ["max"]}))
        self.assertIn("refused: a build of every layer is going", said({"part": "layers"}))
        (st / "layers-build.json").unlink()
        said_all = said({"part": "layers"})
        self.assertIn("one after another: max, high", said_all)
        builds = self.get("/api/builds")[1]
        self.assertEqual([b["who"] for b in builds["bases"]], ["max", "high"])
        self.assertEqual(builds["bases"][0]["parts"], [])                   # the stable base and one medium layer
        for _ in range(50):
            if self.built.read_text().split("\n")[:2] == ["max layer", "high layer"]:
                break
            time.sleep(0.1)
        self.assertEqual(self.built.read_text().split("\n")[:2], ["max layer", "high layer"])
        self.assertIn("stopped", said({"part": "role-layer", "role": "implementer"}))  # nothing would seal it
        (st / "role-layers").unlink()
        self.assertIn("switched off", said({"part": "role-layer", "role": "implementer"}))

    def test_what_the_run_cost_by_kind_role_and_keep(self):
        now = time.time()
        t0 = now - 7200
        self.w.session("review-9", "reviewer", "r9", state="done", live=False, task="9", started=t0 - 5)
        self.w.transcript("r9", [
            fakes.assistant("q1", fakes.iso(t0), usage={"cache_read_input_tokens": 400000,
                                                         "cache_creation_input_tokens": 2000, "output_tokens": 100}),
            fakes.assistant("q2", fakes.iso(t0 + 60), usage={"cache_read_input_tokens": 402000,
                                                              "cache_creation_input_tokens": 500, "output_tokens": 200})])
        self.w.session("design-8", "designer", "d8", state="done", live=False, task="8", started=t0 - 5)
        self.w.transcript("d8", [fakes.assistant("q1", fakes.iso(t0), usage={
            "cache_read_input_tokens": 9000, "cache_creation_input_tokens": 450000, "output_tokens": 50})])
        at = time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(now - 3600))
        (self.w.state / "warm.log").write_text(
            f"{at} warm max: OK   session fork aa of base bb: first own request cache_read=450000 cache_write=2000\n")
        code, c = self.get("/api/costs?hours=24")
        self.assertEqual(code, 200)
        review = next(r for r in c["roles"] if r["role"] == "reviewer")
        self.assertEqual((review["read"], review["write"], review["output"], review["requests"]), (802000, 2500, 300, 2))
        self.assertEqual(review["reread"], 800000)                    # each request read again what its first read
        self.assertEqual(review["cost"], round(802000 * 0.1 + 2500 * 2 + 300 * 5))
        self.assertEqual([x["name"] for x in c["cold"]], ["design-8"])  # its first request wrote its prefix anew
        self.assertEqual((c["keep"]["count"], c["keep"]["cost"]), (1, 49000))
        self.assertEqual(sum(b["pings"] for b in c["buckets"]), 49000)   # in its hour's bar
        self.assertAlmostEqual(sum(b["read"] + b["write"] + b["input"] + b["output"] for b in c["buckets"]),
                               c["total"]["cost"], delta=2)
        self.assertEqual({"9", "8"} <= {t["task"] for t in c["tasks"]}, True)
        # a span with nothing in it (a run stopped for longer): the same span up to the last activity, said so
        self.w.transcript("s7", [])                      # the live session's requests of five minutes ago gone
        code, c = self.get("/api/costs?hours=0.25")
        self.assertIn("shifted", c)
        self.assertEqual(c["total"]["requests"], 3)
        self.assertLessEqual(c["now"], time.time() - 3600)

    def test_a_task_the_log_and_the_checks(self):
        code, d = self.get("/api/task?id=7")
        self.assertEqual(d["record"]["stage"], "running")
        self.assertEqual(d["files"]["result.md"], "Status: partial\n")
        self.assertEqual([s["name"] for s in d["sessions"]], ["implement-7"])
        self.assertIn("checked together", self.get("/api/log")[1][-1])
        self.assertIn("checked together", self.get("/api/checks")[1]["log"][-1])
        self.assertEqual(self.get("/api/file?path=../state/v2.json")[0], 404)     # nothing outside the project
        self.assertEqual(self.get("/api/file?path=.build/tasks/7/result.md")[1]["text"], "Status: partial\n")

    def test_a_task_s_history_and_what_waits_on_it(self):
        self.w.task("8", subject="After the locus", blockedBy=["7"])
        (self.w.state / "v2.log").write_text(
            "2026-09-23T09:00:00 the planner edited the graph: 2 operation(s); made 7, 8\n"
            "2026-09-23T09:01:00 started implement-7 (implementer, from high)\n"
            "2026-09-23T09:02:00 task 17 waits for the machine\n"                    # another task: not its line
            "2026-09-23T09:03:00 the train of tasks 5, 7 landed as abc\n"
            "2026-09-23T09:04:00 resumed review-7.1\n"
            "2026-09-23T09:05:00 the check of task 71: passed in 5 s\n")          # nor this
        code, d = self.get("/api/task?id=7")
        self.assertEqual([x[11:19] for x in d["history"]], ["09:00:00", "09:01:00", "09:03:00", "09:04:00"])
        self.assertEqual(d["dependents"], ["8"])

    def test_the_queue_drops_only_when_told_and_one_task_is_placed_in_it(self):
        for tid in ("8", "9", "10"):
            self.w.task(tid, subject="another")
        self.w.set_st(queue=["7", "8", "9"], tasks={"7": {"stage": "running", "kind": "build", "session": "implement-7"}})
        queue = lambda: json.loads((self.w.state / "v2.json").read_text())["queue"]
        # naming some tasks puts them first and keeps the rest (the owner, 2026-09-24: dropping only when told)
        self.assertIn("after them as they stood, not named: 7, 8", self.post({"action": "queue", "ids": ["9"]})[1]["said"])
        self.assertEqual(queue(), ["9", "7", "8"])
        self.post({"action": "queue", "ids": ["7", "8", "9"]})
        self.assertIn("placed first", self.post({"action": "place", "id": "9", "where": "first"})[1]["said"])
        self.assertEqual(queue(), ["9", "7", "8"])
        self.post({"action": "place", "id": "9", "where": "down"})
        self.assertEqual(queue(), ["7", "9", "8"])
        self.post({"action": "place", "id": "10", "where": "last"})          # not queued: it comes in
        self.assertEqual(queue(), ["7", "9", "8", "10"])
        self.post({"action": "place", "id": "7", "where": "out"})
        self.assertEqual(queue(), ["9", "8", "10"])
        self.assertIn("refused", self.post({"action": "place", "id": "99", "where": "first"})[1]["said"])
        self.post({"action": "queue", "ids": ["10", "8"], "drop_unnamed": True})
        self.assertEqual(queue(), ["10", "8"])

    def test_the_switches_and_the_holds_are_the_owner_s_controls(self):
        self.assertIn("switch measure-bound on (240)", self.post({"action": "switch", "name": "measure-bound", "on": True,
                                                                  "value": "240"})[1]["said"])
        self.assertEqual((self.w.state / "measure-bound").read_text(), "240\n")
        self.assertEqual(self.get("/api/overview")[1]["measure_seconds"], 240)
        self.assertIn("refused", self.post({"action": "switch", "name": "measure-bound", "on": True, "value": "x"})[1]["said"])
        self.post({"action": "switch", "name": "measure-bound", "on": False})
        self.assertFalse((self.w.state / "measure-bound").exists())
        self.assertIn("refused: no switch", self.post({"action": "switch", "name": "no-such", "on": True})[1]["said"])
        self.post({"action": "hold", "what": "graph", "on": True})
        self.assertTrue(self.get("/api/overview")[1]["holds"]["graph"])
        self.post({"action": "hold", "what": "graph", "on": False})
        self.assertFalse((self.w.state / "graph-held").exists())
        self.assertIn("the owner (console): switch", (self.w.state / "v2.log").read_text())


    def test_the_task_graph_says_where_each_task_stands(self):
        self.w.task("8", subject="After the locus", blockedBy=["7"])
        self.w.task("9", subject="Checked")
        self.w.task("10", subject="Landing")
        self.w.set_st(queue=["7", "8", "9", "10"], tasks={
            "7": {"stage": "running", "kind": "build", "session": "implement-7"},
            "9": {"stage": "checking", "kind": "fix"}, "10": {"stage": "committing", "kind": "build"}})
        (self.w.state / "check-queue.json").write_text(json.dumps({"9": {"queued": time.time(), "head": "abc"}}))
        (self.w.state / "landing-queue.json").write_text(json.dumps({"10": {"queued": time.time(), "head": "def"}}))
        code, g = self.get("/api/graph")
        nodes = {n["id"]: n for n in g["nodes"]}
        self.assertEqual(nodes["7"]["status"], "running (implement-7)")
        self.assertEqual((nodes["8"]["status"], nodes["8"]["group"]), ("waiting on #7", "waiting"))
        self.assertEqual((nodes["9"]["status"], nodes["9"]["group"]), ("waiting for a check batch", "check"))
        self.assertEqual((nodes["10"]["status"], nodes["10"]["group"]), ("waiting for a landing train", "train"))
        self.assertIn(["7", "8"], g["edges"])

    def test_the_machine_and_the_batches_and_trains(self):
        (self.w.state / "isabelle-processes.json").write_text(json.dumps({"at": "2026-09-23T11:00:00", "heavy": 1, "probes": 1,
            "roots": [{"pid": 10, "kind": "heavy", "session": False}, {"pid": 20, "kind": "probe", "session": True}],
            "processes": [{"pid": 11, "run": 10, "kind": "heavy", "rss_mb": 4096, "run_command": "incremental_check.py check"},
                          {"pid": 21, "run": 20, "kind": "probe", "rss_mb": 900, "run_command": "probe_theories.py"}]}))
        code, d = self.get("/api/machine")
        runs = {r["kind"]: r for r in d["runs"]}
        self.assertEqual((runs["heavy"]["rss_mb"], runs["heavy"]["session"], runs["probe"]["session"]), (4096, False, True))
        self.assertEqual((d["limits"]["heavy"], d["limits"]["probes"]), (2, 8))
        (self.w.state / "check-queue.json").write_text(json.dumps({
            "7": {"queued": time.time() - 60}, "5": {"queued": time.time() - 900, "decided": time.time() - 600, "code": 0,
                                                   "what": "passed", "log": "x.log"}}))
        (self.w.state / "landing-queue.json").write_text(json.dumps({"4": {"queued": time.time() - 300,
            "decided": time.time() - 100, "code": 0, "what": "landed", "ref": "abc123"}}))
        self.w.write(".build/tasks/batches/20260923-110000-batch7.log", "checking\n")
        code, d = self.get("/api/checks")
        self.assertEqual({r["task"]: r["state"] for r in d["batches"]}, {"7": "waiting", "5": "passed"})
        self.assertEqual((d["trains"][0]["state"], d["trains"][0]["ref"]), ("landed", "abc123"))
        self.assertEqual(d["batch_logs"][0]["name"], "20260923-110000-batch7.log")

    def test_a_change_made_before_the_follower_starts_is_followed(self):
        # the sources are read before the console serves anything: a change between its first answer and the
        # follower's first line was taken for the start and never followed
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp) / "watched.py"
            source.write_text("x = 1\n")
            started = ((str(source), os.path.getmtime(source)),)
            os.utime(source, (time.time() + 5, time.time() + 5))
            import dashboard
            from unittest.mock import Mock
            server, naps = Mock(), []

            def nap(seconds):
                naps.append(seconds)
                if len(naps) > 3:
                    raise RuntimeError("the change was never followed")
            with patch.object(dashboard, "WATCHED", [str(source)]), patch.object(dashboard.time, "sleep", nap):
                dashboard.follow(server, None, started)
            server.shutdown.assert_called_once()

    def test_the_console_follows_its_source_and_keeps_its_address(self):
        started = self.get("/api/version")[1]["started"]
        self.watched.write_text("x = 2\n")
        os.utime(self.watched, (time.time() + 5, time.time() + 5))
        # re-executed: the same port, the same token. It notices within 1.5 s, then a new process imports v2 again,
        # which on a loaded machine took more than the 10 s once allowed here (2026-09-23, twice in a full suite):
        # the deadline is reached only by a console that does not follow its source
        deadline = time.time() + 30
        while time.time() < deadline:
            time.sleep(0.25)
            try:
                now = self.get("/api/version")
            except OSError:
                continue
            if now[0] == 200 and now[1]["started"] != started:
                break
        self.assertNotEqual(now[1]["started"], started)
        started = now[1]["started"]
        self.watched.write_text("x = (\n")                     # a source that does not compile is not run
        os.utime(self.watched, (time.time() + 10, time.time() + 10))
        time.sleep(3)
        self.assertEqual(self.get("/api/version")[1]["started"], started)


if __name__ == "__main__":
    unittest.main()
