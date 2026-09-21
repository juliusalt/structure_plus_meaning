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


if __name__ == "__main__":
    unittest.main()
