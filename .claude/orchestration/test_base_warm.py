"""base.sh warm: the keep-warm ping's verdict, and that it is recorded where health.py reads it.

The ping is run both by the daemon and by hand. It used to print its verdict and nothing more, so warm.log held
only what the daemon's redirection put there: a ping run by hand left no line, and health.py, which reads that log,
went on reporting an older and colder verdict. On 2026-09-20 all three bases were refreshed by hand at 16:09 and
answered OK while health.py said max had been COLD at 15:19, for the fifty minutes after.

base.sh's own PROJECT is this repository (it is the tree the base was loaded from), so this world fakes HOME and the
state directory around the real one rather than using fakes.World.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
TRANSCRIPTS = str(PROJECT).replace("/", "-").replace("_", "-")  # as session_fork_check.py and base.sh name it
LEAN = " ".join((HERE / "session-flags").read_text().split())  # the flags the base was built with, as base.sh records

FAKE = """#!/usr/bin/env python3
import json, os, sys
with open(os.environ['WARM_TEST_CALLS'], 'a') as f:
    f.write(json.dumps(sys.argv[1:]) + chr(10))
if sys.argv[1:] == ['agents', '--json']:
    print(json.dumps([dict(kind='background', id='t1', status='idle', state='done',
                           sessionId='warm-test-fork', cwd=os.environ['WARM_TEST_CWD'], name='warm-max')]))
"""


def assistant(msg_id, fresh, read, write):
    return {"type": "assistant", "timestamp": "2026-09-20T16:09:00.000Z",
            "message": {"id": msg_id, "model": "claude-opus-5",
                        "content": [{"type": "text", "text": "WARM"}],
                        "usage": {"input_tokens": fresh, "cache_read_input_tokens": read,
                                  "cache_creation_input_tokens": write}}}


class WarmVerdictTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        root = Path(self.temp.name)
        self.state, home, binary = root / "state", root / "home", root / "bin"
        for d in (self.state, binary):
            d.mkdir(parents=True)
        sessions = home / ".claude/projects" / TRANSCRIPTS
        sessions.mkdir(parents=True)
        (binary / "claude").write_text(FAKE)
        (binary / "claude").chmod(0o755)
        (self.state / "max-base.json").write_text(json.dumps(
            {"sessionId": "warm-test-base", "model": "claude-opus-5", "effort": "max", "name": "max-base", "flags": LEAN}))
        # the base's last request, and a fork that read it: 500K of the base's 500K context, so the verdict is OK
        base = assistant("base-1", 0, 0, 500000)
        (sessions / "warm-test-base.jsonl").write_text(json.dumps(base) + "\n")
        (sessions / "warm-test-fork.jsonl").write_text(
            json.dumps(base) + "\n" + json.dumps(assistant("own-1", 2, 500000, 62)) + "\n")
        self.calls = root / "calls.jsonl"
        self.env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], HOME=str(home),
                        ORCH_STATE_DIR=str(self.state), WARM_TEST_CWD=str(PROJECT),
                        WARM_TEST_CALLS=str(self.calls))
        for k in list(self.env):
            if k.startswith(("CLAUDE", "ORCH_")) and k != "ORCH_STATE_DIR":
                del self.env[k]

    def tearDown(self):
        self.temp.cleanup()

    def warm(self, shell=None):
        command = shell or ["sh", str(HERE / "base.sh"), "max", "warm"]
        out = subprocess.run(command, env=self.env, capture_output=True, text=True, timeout=60,
                             **({"shell": True} if shell else {}))
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        return out.stdout

    def log(self):
        path = self.state / "warm.log"
        return path.read_text() if path.exists() else ""

    def resumed(self):
        """The session id each background fork was made from."""
        out = []
        for line in self.calls.read_text().splitlines() if self.calls.exists() else []:
            args = json.loads(line)
            if "--bg" in args and "--resume" in args:
                out.append(args[args.index("--resume") + 1])
        return out

    def layer(self, sid="warm-test-layer", base="warm-test-base"):
        (self.state / "max-layer.json").write_text(json.dumps(
            {"sessionId": sid, "model": "claude-opus-5", "effort": "max", "name": "max-layer-1",
             "context": 525_000, "base": base, "sealed": "2026-09-20T10:00:00", "flags": LEAN}))

    def test_a_ping_run_by_hand_is_recorded_where_health_reads_it(self):
        printed = self.warm()
        self.assertIn("warm max: OK", printed)  # the caller still sees it
        self.assertIn("warm max: OK", self.log())  # and so does the log, with nothing redirected into it
        self.assertTrue((self.state / "max-base.hit").exists())
        self.assertFalse((self.state / "max-base.miss").exists())
        health = subprocess.run(
            [sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); "
             "import health; health.bases_and_trees()"],
            env=dict(self.env, ORCH_PROJECT=self.temp.name,
                     ORCH_ACTIVE_CONTEXT=str(Path(self.temp.name) / "no-such-context.json")),
            capture_output=True, text=True, timeout=60)
        self.assertEqual(health.returncode, 0, health.stdout + health.stderr)
        self.assertIn("base max: warm at", health.stdout)

    def test_a_base_started_with_other_tools_is_not_pinged(self):
        # every fork reads its origin from cache only with the same tools; a ping of a base started with others (all
        # three, when the owner took four tools out on 2026-09-21) would write its whole prefix again, each time
        rec = json.loads((self.state / "max-base.json").read_text())
        (self.state / "max-base.json").write_text(json.dumps(dict(rec, flags=LEAN.replace(" Bash", " Bash Grep"))))
        out = subprocess.run(["sh", str(HERE / "base.sh"), "max", "warm"], env=self.env, capture_output=True, text=True,
                             timeout=60)
        self.assertEqual(out.returncode, 3)
        self.assertIn("started with other tools than session-flags gives now", out.stderr)
        self.assertEqual(self.resumed(), [])  # nothing forked
        (self.state / "max-base.json").write_text(json.dumps({k: v for k, v in rec.items() if k != "flags"}))
        self.assertEqual(subprocess.run(["sh", str(HERE / "base.sh"), "max", "warm"], env=self.env, capture_output=True,
                                        timeout=60).returncode, 3)  # nor one recorded before the flags were

    def test_the_ping_goes_to_the_layer_the_roles_fork_not_the_base_under_it(self):
        # a layer left cold costs its whole size on the next fork; a fork of it reads the base under it anyway
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-base"])  # no layer: the base itself
        self.calls.write_text("")
        self.layer()
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-layer"])
        # a layer whose stable base has been rebuilt under it is a fork of a session that is gone: not it, the base
        self.calls.write_text("")
        self.layer(base="a-base-that-was-rebuilt-away")
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-base"])

    def test_the_daemon_s_redirection_does_not_write_the_verdict_twice(self):
        # the daemon runs `base.sh WHO warm >/dev/null 2>> warm.log`: the verdict comes from base.sh, the stream
        # carries only what failed before it
        self.warm(shell=f'sh {HERE / "base.sh"} max warm >/dev/null 2>> {self.state / "warm.log"}')
        self.assertEqual(len([l for l in self.log().splitlines() if "warm max:" in l]), 1, self.log())


if __name__ == "__main__":
    unittest.main()


class DaemonPidTests(WarmVerdictTests):
    """`warm.pid` is how both `warm_daemon.sh --ensure` and health.py decide a daemon runs. A daemon that dies
    without clearing it leaves a number the system hands to something else, and then --ensure starts nothing while
    health says "daemon: alive": the keep-warm pings stop for good and the report says they do not."""

    def ensure(self):
        """Run `warm_daemon.sh --ensure` with a `setsid` that records instead of starting anything."""
        started = Path(self.temp.name) / "started"
        fake = Path(self.env["PATH"].split(os.pathsep)[0]) / "setsid"
        fake.write_text(f"#!/bin/sh\necho started >> {started}\n")
        fake.chmod(0o755)
        out = subprocess.run(["sh", str(HERE / "warm_daemon.sh"), "--ensure"], env=self.env,
                             capture_output=True, text=True, timeout=60)
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        for _ in range(50):     # it detaches and returns at once: the start lands after it
            if started.exists():
                return True
            time.sleep(0.1)
        return False

    def alive(self):
        out = subprocess.run(
            [sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); "
             "import health; print(health.daemon_alive())"],
            env=dict(self.env, ORCH_PROJECT=self.temp.name), capture_output=True, text=True, timeout=60)
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        return out.stdout.strip()

    def stub(self):
        """A live process whose command line names the daemon, as the daemon's own does."""
        path = Path(self.temp.name) / "warm_daemon_stub.sh"
        path.write_text("#!/bin/sh\nsleep 30\n")
        p = subprocess.Popen(["sh", str(path)])
        self.addCleanup(p.wait)
        self.addCleanup(p.kill)
        return p.pid

    def test_a_pid_that_is_not_the_daemon_is_not_a_running_daemon(self):
        (self.state / "warm.pid").write_text(str(os.getpid()))  # alive, and not the daemon
        self.assertTrue(self.ensure())
        self.assertEqual(self.alive(), "False")

    def test_the_daemon_itself_is_left_alone_and_reported_alive(self):
        (self.state / "warm.pid").write_text(str(self.stub()))
        self.assertFalse(self.ensure())     # nothing is started beside it
        self.assertEqual(self.alive(), "True")

    def test_no_pid_file_and_a_pid_that_is_gone_both_mean_no_daemon(self):
        self.assertEqual(self.alive(), "False")
        self.assertTrue(self.ensure())
        (self.state / "warm.pid").write_text("999999999")
        self.assertEqual(self.alive(), "False")
