"""efficiency.py by role: a planning episode, an implementer credited with its task's finalized commit, and a v1
implementer."""
import json
from pathlib import Path
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import assistant  # noqa: E402

USAGE = {"input_tokens": 2, "cache_read_input_tokens": 600_000, "cache_creation_input_tokens": 1000, "output_tokens": 500}


def user(ts, content):
    return {"type": "user", "timestamp": ts, "message": {"role": "user", "content": content}}


def call(n, ts, name, inp, ctx=600_000):
    return assistant(f"m{n}", ts, [{"type": "tool_use", "id": f"t{n}", "name": name, "input": inp}],
                     usage=dict(USAGE, cache_read_input_tokens=ctx))


def result(n, ts, text):
    return user(ts, [{"type": "tool_result", "tool_use_id": f"t{n}", "content": text}])


class EfficiencyTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.repository()
        self.t0 = time.time() - 600
        self.w.write("theories/Ready.thy", "".join(f"line {i}\n" for i in range(30)))
        self.w.git("add", "theories/Ready.thy")
        self.w.git("commit", "-q", "-m", "Add readiness")
        self.commit = self.w.git("rev-parse", "--short", "HEAD").strip()

    def tearDown(self):
        self.w.close()

    def ts(self, minutes):
        return fakes.iso(self.t0 + 60 * minutes)

    def session(self, sid, start, own):
        load = user(self.ts(-100), "Load the reference library; do no development work.")  # the base's copied load
        self.w.transcript(sid, [load, assistant("base1", self.ts(-99), usage=USAGE), user(self.ts(0), start), *own])

    def test_every_role_is_measured_and_an_implementer_is_credited_with_its_finalized_commit(self):
        self.session("w2", "You are implement-2, an implementer forked from the loaded library for one task.", [
            call(1, self.ts(1), "Read", {"file_path": str(self.w.project / "theories/Ready.thy")}),
            result(1, self.ts(1.1), "x" * 2500),
            call(2, self.ts(2), "Bash", {"command": "sed -n 1,10p theories/Ready.thy"}),
            result(2, self.ts(2.1), "y" * 250),
            call(3, self.ts(3), "Bash", {"command": "sleep 30"}),
            result(3, self.ts(3.1), "Waiting is refused (sleep, wait loops, tail -f)"),
            call(4, self.ts(4), "Edit", {"file_path": "theories/Ready.thy"}, ctx=610_000),
            result(4, self.ts(4.1), "edited")])
        self.w.write(".build/tasks/2/finalized.json", json.dumps({"ok": True, "commit": self.commit}))
        self.session("p1", "You are plan-1, a planning episode of the development.", [
            call(1, self.ts(1), "Bash", {"command": ".claude/orchestration/show.py --statement ready"}),
            result(1, self.ts(1.1), "lemma ready")])
        self.session("i9", "You are impl-9, a working copy forked from the loaded base.", [
            call(1, self.ts(1), "Write", {"file_path": "theories/Ready.thy"}),
            result(1, self.ts(12), "written")])
        self.session("x1", "Review the orchestrator.", [call(1, self.ts(1), "Bash", {"command": "ls"})])
        code, out, err = self.w.run("efficiency.py", "--json")
        self.assertEqual(code, 0, err)
        rows = {r["name"]: r for r in json.loads(out)}
        self.assertEqual(sorted(rows), ["impl-9", "implement-2", "plan-1"])  # the base's own request is not theirs
        w = rows["implement-2"]
        self.assertEqual((w["requests"], w["calls"], w["reads"], w["refused"]), (4, 4, 2, 1))
        self.assertAlmostEqual(w["reread_share"], 100 / 1100, places=2)  # by file: the sed re-read Ready.thy
        self.assertAlmostEqual(w["first_write_min"], 4.0, places=1)
        self.assertEqual(w["first_write_ctx"], 10_000)
        self.assertEqual((w["commits"], w["lines"]), (1, 30))
        self.assertNotIn("commits", rows["plan-1"])
        # an implementer is credited with every commit made while it ran: the repository's first and the theory's
        self.assertEqual((rows["impl-9"]["commits"], rows["impl-9"]["lines"]), (2, 30))
        code, table, _ = self.w.run("efficiency.py")
        self.assertIn("mean of 1 implement session:", table)
        self.assertIn("mean of 1 impl session:", table)


if __name__ == "__main__":
    unittest.main()
