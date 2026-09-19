"""attach.sh follows a role (the planning episodes, the producing session, ...) through wakes and successors; no Claude
sessions are launched (fakes.py's fake `claude` records the attaches and runs a scripted action after each)."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402


class AttachTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()

    def tearDown(self):
        self.w.close()

    def row(self, name, sid):
        return {"name": name, "id": f"id-{sid}", "sessionId": sid, "kind": "background", "status": "idle",
                "state": "done", "cwd": str(self.w.project)}

    def holds(self, role, name, sid):
        """The state as v2.py keeps it, the role held by that session."""
        kind = {"planner": "planner", "producer": "implementer"}[role]
        return json.dumps({"active": True, "sessions": {name: {"name": name, "role": kind, "sid": sid, "task": "1",
                                                                "state": "working"}}})

    def attach(self, role, name, sid, actions, stopped=False):
        """Attach to the role held by (name, sid); after the n-th attach the fake runs actions[n-1] ($STATE, $ROOT)."""
        self.w.set_rows([self.row(name, sid)])
        (self.w.state / "v2.json").write_text(self.holds(role, name, sid))
        if stopped:
            (self.w.state / "stopped").write_text("x\n")
        for n, body in enumerate(actions, 1):
            (self.w.root / f"action{n}.sh").write_text(body.replace("$STATE", str(self.w.state)).replace("$ROOT", str(self.w.root)))
        out = self.w.run("attach.sh", *([role] if role != "planner" else []), timeout=30)
        attached = (self.w.root / "attached").read_text().split() if (self.w.root / "attached").exists() else []
        return out[1] + out[2], attached

    def successor(self, role, name, sid):
        """An action: the attached session is stopped, and a moment later its successor holds the role."""
        rows = json.dumps([self.row(name, sid)]).replace("'", "'\\''")
        state = self.holds(role, name, sid).replace("'", "'\\''")
        return (f"echo '[]' > $ROOT/agents.json; (sleep 3; echo '{rows}' > $ROOT/agents.json; "
                f"echo '{state}' > $STATE/v2.json) &")

    def test_the_next_planning_episode_is_followed(self):
        out, attached = self.attach("planner", "plan-1", "p1", [self.successor("planner", "plan-2", "p2"),
                                                                    "touch $STATE/stopped"])
        self.assertEqual(attached, ["id-p1", "id-p2"], out)
        self.assertIn("attaching to plan-2", out)
        self.assertIn("stopped", out.splitlines()[-1])

    def test_a_wake_reattaches_to_the_same_session(self):
        out, attached = self.attach("planner", "plan-1", "p1", ["echo woken > $STATE/plan-1.woken",
                                                                    "touch $STATE/stopped"])
        self.assertEqual(attached, ["id-p1", "id-p1"], out)

    def test_leaving_a_running_session_ends_following(self):
        out, attached = self.attach("planner", "plan-1", "p1", [""])
        self.assertEqual(attached, ["id-p1"])
        self.assertIn("left plan-1, which keeps running; attach.sh planner opens it again", out)

    def test_the_producing_role_follows_to_the_next_session(self):
        out, attached = self.attach("producer", "implement-1", "w1", [self.successor("producer", "implement-2", "w2"),
                                                                       "touch $STATE/stopped"])
        self.assertEqual(attached, ["id-w1", "id-w2"], out)
        self.assertIn("waiting for the live producer", out)

    def test_a_stopped_orchestration_attaches_nothing(self):
        out, attached = self.attach("planner", "plan-1", "p1", [], stopped=True)
        self.assertEqual(attached, [])
        self.assertIn("the orchestration is stopped", out)

    def test_an_unknown_role_is_refused(self):
        code, _, err = self.w.run("attach.sh", "implementer")
        self.assertEqual(code, 2)
        self.assertIn("usage", err)


if __name__ == "__main__":
    unittest.main()
