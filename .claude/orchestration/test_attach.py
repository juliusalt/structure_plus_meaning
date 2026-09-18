"""attach.sh follows the implementer through rotations and wakes; no Claude sessions are launched."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
PROJECT = str(HERE.parent.parent)
FAKE = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
root = os.environ["FAKE_ROOT"]
if sys.argv[1:3] == ["agents", "--json"]:
    print(open(os.path.join(root, "agents.json")).read())
elif sys.argv[1] == "attach":
    with open(os.path.join(root, "attached"), "a") as f:
        f.write(sys.argv[2] + "\n")
    n = len(open(os.path.join(root, "attached")).read().split())
    action = os.path.join(root, f"action{n}.sh")
    if os.path.exists(action):
        subprocess.run(["sh", action], check=True)
else:
    sys.exit("unexpected: " + " ".join(sys.argv[1:]))
'''


def agent(name, ident):
    return {"name": name, "id": ident, "kind": "background", "status": "idle", "state": "done",
            "sessionId": ident + "-0000", "cwd": PROJECT}


class AttachTests(unittest.TestCase):
    def run_attach(self, agents, current, actions, stopped=False):
        with tempfile.TemporaryDirectory() as temp:
            root, state = Path(temp), Path(temp) / "state"
            state.mkdir()
            (root / "bin").mkdir()
            (root / "bin/claude").write_text(FAKE)
            (root / "bin/claude").chmod(0o755)
            (root / "agents.json").write_text(json.dumps(agents))
            (state / "current-impl").write_text(current + "\n")
            if stopped:
                (state / "stopped").write_text("x\n")
            for n, body in enumerate(actions, 1):
                (root / f"action{n}.sh").write_text(body.replace("$STATE", str(state)).replace("$ROOT", str(root)))
            env = dict(os.environ, PATH=str(root / "bin") + os.pathsep + os.environ["PATH"],
                       FAKE_ROOT=str(root), ORCH_STATE_DIR=str(state))
            out = subprocess.run(["sh", str(HERE / "attach.sh")], env=env, capture_output=True, text=True, timeout=30)
            attached = (root / "attached").read_text().split() if (root / "attached").exists() else []
            return out, attached

    @staticmethod
    def agents_json(*pairs):
        return json.dumps([agent(n, i) for n, i in pairs]).replace('"', '\\"')

    def test_rotation_moves_to_the_successor(self):
        out, attached = self.run_attach([agent("impl-1", "aaa")], "impl-1", [
            "echo rotated > $STATE/rotated; echo '[]' > $ROOT/agents.json; "
            f"(sleep 3; echo \"{self.agents_json(('impl-2', 'bbb'))}\" > $ROOT/agents.json; echo impl-2 > $STATE/current-impl) &",
            "touch $STATE/stopped"])
        self.assertEqual(attached, ["aaa", "bbb"], out.stdout + out.stderr)
        self.assertIn("attaching to impl-2", out.stdout)
        self.assertIn("stopped", out.stdout.splitlines()[-1])

    def test_wake_reattaches_to_the_same_session(self):
        out, attached = self.run_attach([agent("impl-1", "aaa")], "impl-1", [
            "echo woken > $STATE/impl-1.woken", "touch $STATE/stopped"])
        self.assertEqual(attached, ["aaa", "aaa"], out.stdout + out.stderr)

    def test_leaving_a_running_session_ends_following(self):
        out, attached = self.run_attach([agent("impl-1", "aaa")], "impl-1", [""])
        self.assertEqual(attached, ["aaa"])
        self.assertIn("left impl-1, which keeps running", out.stdout)

    def test_a_vanished_session_is_followed_to_its_replacement(self):
        out, attached = self.run_attach([agent("impl-1", "aaa")], "impl-1", [
            "echo '[]' > $ROOT/agents.json; "
            f"(sleep 3; echo \"{self.agents_json(('impl-2', 'bbb'))}\" > $ROOT/agents.json; echo impl-2 > $STATE/current-impl) &",
            "touch $STATE/stopped"])
        self.assertEqual(attached, ["aaa", "bbb"], out.stdout + out.stderr)

    def test_a_stopped_orchestration_attaches_nothing(self):
        out, attached = self.run_attach([agent("impl-1", "aaa")], "impl-1", [], stopped=True)
        self.assertEqual(attached, [])
        self.assertIn("stopped", out.stdout)


if __name__ == "__main__":
    unittest.main()
