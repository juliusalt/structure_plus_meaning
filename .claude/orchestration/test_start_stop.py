"""start.sh and stop.sh: the orchestration made active with a planner and the daemon, then every role stopped and the
daemon with them; in a throwaway world (fakes.py), the daemon's loop shortened to a second."""
import os
from pathlib import Path
import signal
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import PLANNER_STATE  # noqa: E402


class StartStopTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.env["ORCH_DAEMON_EVERY"] = "1"
        self.w.write("HANDOFF.md", PLANNER_STATE)

    def tearDown(self):
        pid = self.daemon()
        if pid:
            os.kill(pid, signal.SIGTERM)
        self.w.close()

    def daemon(self):
        """The daemon's pid while it runs."""
        try:
            pid = int((self.w.state / "warm.pid").read_text())
            os.kill(pid, 0)
            return pid
        except (OSError, ValueError):
            return None

    @staticmethod
    def children(pid):
        """The command names of a process's children."""
        names = []
        for c in filter(str.isdigit, os.listdir("/proc")):
            try:
                with open(f"/proc/{c}/stat") as f:
                    comm, rest = f.read().rsplit(") ", 1)
            except OSError:
                continue  # gone meanwhile
            if pid and rest.split()[1] == str(pid):
                names.append(comm.split(" (", 1)[1])
        return names

    def test_a_request_from_inside_the_sandbox_wakes_the_sleeping_daemon_within_seconds(self):
        # a session asks the supervisor for what it cannot do in the sandbox (v2.want); the daemon's minute of sleep
        # ends when one is waiting, so a released session is stopped in seconds, not at the next minute (2026-09-21)
        self.w.env["ORCH_DAEMON_EVERY"] = "60"
        self.w.base()
        code, _, err = self.w.run("start.sh", "--no-attach")
        self.assertEqual(code, 0, err)
        for _ in range(100):  # its first pass done, it sleeps
            if "sleep" in self.children(self.daemon()):
                break
            time.sleep(0.1)
        self.assertIn("sleep", self.children(self.daemon()))
        wanted = self.w.state / "wanted" / "dispatch.json"
        wanted.parent.mkdir(exist_ok=True)
        wanted.write_text('{"run": ["v2.py", "dispatch"], "by": "a session"}')
        for _ in range(100):
            if not wanted.exists():
                break
            time.sleep(0.1)
        self.assertFalse(wanted.exists())

    def test_health_run_inside_the_sandbox_reads_the_daemon_by_its_heartbeat(self):
        # only a command's own processes are visible there, and the pid of the live daemon read as dead (2026-09-21)
        self.w.env["ORCH_BEAT_EVERY"] = "1"
        self.w.base()
        self.assertEqual(self.w.run("start.sh", "--no-attach")[0], 0)
        beat = self.w.state / "warm.beat"
        for _ in range(50):
            if beat.exists():
                break
            time.sleep(0.1)
        inside = {"ORCH_CONTROL": "0"}
        pid = self.daemon()
        (self.w.state / "warm.pid").write_text(str(2 ** 22 + 1))  # its process out of sight, as it is inside
        try:
            self.assertIn("daemon: alive", self.w.run("health.py", env=inside)[1])
        finally:
            (self.w.state / "warm.pid").write_text(str(pid))
        os.kill(pid, signal.SIGTERM)  # it dies while the run is active
        time.sleep(2.5)  # the heartbeat ends with the daemon, within its beat
        old = time.time() - 600
        os.utime(beat, (old, old))
        self.assertIn("ATTENTION daemon is not running", self.w.run("health.py", env=inside)[1])

    def test_start_then_stop_then_start_again(self):
        code, out, _ = self.w.run("start.sh", "--no-attach")
        self.assertEqual(code, 3)
        self.assertIn("refused: no sealed base", out)
        self.w.base()
        code, out, err = self.w.run("start.sh", "--no-attach")
        self.assertEqual(code, 0, err)
        self.assertIn("active; knowledge base kb-1", out)
        for _ in range(50):
            if self.daemon():
                break
            time.sleep(0.1)
        pid = self.daemon()
        self.assertIsNotNone(pid)
        self.assertTrue(self.w.st()["active"])
        self.w.reply(self.w.st()["sessions"]["kb-1"]["sid"], "INTEGRATED")
        for _ in range(50):  # the daemon's watchdog seals the loaded knowledge base
            if self.w.st()["kb"] == "kb-1":
                break
            time.sleep(0.1)
        self.assertEqual(self.w.st()["sessions"]["kb-1"]["kb_state"], "sealed")
        code, out, err = self.w.run("stop.sh")
        self.assertEqual(code, 0, err)
        self.assertIn("daemon stopped", out)
        for _ in range(50):
            if not os.path.exists(f"/proc/{pid}"):
                break
            time.sleep(0.1)
        self.assertFalse(os.path.exists(f"/proc/{pid}"))
        self.assertFalse(self.w.st()["active"])
        self.assertTrue((self.w.state / "stopped").exists())
        # and nothing starts one again by another door: `v2.py talk` does not go through the dispatch, and would
        # have forked the knowledge base for a planner while everything was stopped (2026-09-21)
        self.assertEqual(self.w.v2("talk"), "")     # no planner to join, and none opened
        self.assertEqual([s["state"] for n, s in self.w.st()["sessions"].items() if n.startswith("plan-")
                          and s["state"] not in ("done", "lost")], [])
        self.assertIn("the run is stopped", (self.w.state / "v2.log").read_text())
        _, said, _ = self.w.run("talk.sh")
        self.assertIn("the orchestration is stopped", said)
        code, out, _ = self.w.run("start.sh", "--no-attach")
        self.assertIn("active; knowledge base kb-1", out)  # the sealed knowledge base is kept
        self.assertFalse((self.w.state / "stopped").exists())
        self.w.run("stop.sh")

    def test_a_stop_that_keeps_the_warmth_daemon_stops_every_role_and_nothing_else(self):
        self.w.base()
        code, out, err = self.w.run("start.sh", "--no-attach")
        self.assertEqual(code, 0, err)
        for _ in range(50):
            if self.daemon():
                break
            time.sleep(0.1)
        pid = self.daemon()
        self.assertIsNotNone(pid)
        code, out, err = self.w.run("stop.sh", "--keep-warm")
        self.assertEqual(code, 0, err)
        self.assertIn("daemon kept", out)
        self.assertNotIn("daemon stopped", out)
        self.assertFalse(self.w.st()["active"])
        self.assertTrue((self.w.state / "stopped").exists())
        self.assertEqual([n for n, s in self.w.st()["sessions"].items() if s["state"] not in ("done", "lost")], [])
        time.sleep(2.5)  # two of the daemon's shortened rounds: it lives, and its watchdog starts nothing
        self.assertEqual(self.daemon(), pid)
        self.assertFalse(self.w.st()["active"])
        self.assertEqual([n for n, s in self.w.st()["sessions"].items() if s["state"] not in ("done", "lost")], [])
        code, _, err = self.w.run("stop.sh", "--keep-warmth")
        self.assertEqual(code, 2)
        self.assertIn("usage: stop.sh [--keep-warm]", err)


if __name__ == "__main__":
    unittest.main()
