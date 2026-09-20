"""The layered bases: a list split into a stable reference and a frontier layer (notes/bases-design.md section 8).

The stable reference is rebuilt rarely, and that is the owner's; the layer holds the working frontier and the
direction, and the harness refreshes it on its own. A fork of the layer reads the whole prefix under it from cache —
measured on 2026-09-20: a fork of the sealed knowledge base, a layer over `max` in all but name, read 538,051 of its
538,044 tokens and wrote 62 — so the layer is what every role forks and what is pinged.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
import manifest  # noqa: E402
import select_base_load  # noqa: E402
import v2  # noqa: E402

PROJECT = HERE.parent.parent


def parts(who):
    """(stable, layer, whole) file lists of that base's list, read in its own environment."""
    code = ("import sys, os, json; sys.path.insert(0, %r); "
            "os.environ['ORCH_LOAD_LIST'] = %r; import manifest; "
            "print(json.dumps({p: [q for _, q in manifest.held_files(p)] for p in ('stable', 'layer', '')}))")
    out = subprocess.run([sys.executable, "-c", code % (str(HERE), str(HERE / manifest.LISTS[who]))],
                         capture_output=True, text=True,
                         env={k: v for k, v in os.environ.items() if k not in ("ORCH_LOAD_LIST", "ORCH_BASE_PART")})
    return json.loads(out.stdout)


class SplitListTests(unittest.TestCase):
    def test_the_split_lists_divide_in_two_and_nothing_is_lost(self):
        for who in ("max", "xhigh", "high"):
            p = parts(who)
            self.assertTrue(p["stable"], f"{who} has no stable reference")
            self.assertTrue(p["layer"], f"{who} has no layer")
            self.assertEqual(sorted(p["stable"] + p["layer"]), sorted(p[""]), who)
            self.assertEqual(set(p["stable"]) & set(p["layer"]), set(), f"{who} holds a file in both parts")

    def test_the_planner_s_layer_holds_what_changes_and_no_frontier(self):
        # its reference moved by nothing in twelve hours while the generated indexes, the reasoning inventory, the
        # plan and the owner's words moved by 66,526 tokens: those are the layer (2026-09-20)
        self.assertTrue(manifest.has_layer(HERE / manifest.LISTS["max"]))
        layer = parts("max")["layer"]
        for name in ("state/held/theory-names.md", "state/held/decisions-index.md", "REASONING_REUSE.md",
                     "native_control_plan.md"):
            self.assertTrue(any(p.endswith(name) for p in layer), f"{name} is not in the planner's layer")
        stable = parts("max")["stable"]
        self.assertTrue(any(p.endswith("theories/RRA_Core.thy") for p in stable))   # the reference stays put
        self.assertNotIn(select_base_load.FRONTIER_HEAD, (HERE / manifest.LISTS["max"]).read_text())

    def test_the_layer_begins_at_the_working_frontier(self):
        for who in ("xhigh", "high"):
            layer = parts(who)["layer"]
            self.assertIn(str(PROJECT / "theories/Development_Machinery.thy"), layer, who)
            # the founding theories and the central ideas stay in the stable reference
            self.assertIn(str(PROJECT / "theories/RRA_Core.thy"), parts(who)["stable"], who)

    def test_the_frontier_tier_holds_the_theories_it_says_it_does(self):
        for who in ("xhigh", "high"):
            text = (HERE / manifest.LISTS[who]).read_text()
            at = text.index(select_base_load.FRONTIER_HEAD)
            after = text[at:].splitlines()
            entries = []
            for line in after[1:]:
                if line.startswith("# "):
                    break
                name = line.split("  #")[0].strip()
                if name:
                    entries.append(name)
            self.assertEqual(len(entries), select_base_load.FRONTIER_N, f"{who}'s frontier is not {select_base_load.FRONTIER_N} theories")
            for name in entries:
                self.assertTrue((PROJECT / name).is_file(), f"{who}'s frontier names {name}, which is not there")

    def test_a_layer_pays_for_no_fresh_session(self):
        # it is loaded by a fork of the sealed stable base, which carries the lean session already
        code = "import sys; sys.path.insert(0, %r); import base_pack; print(base_pack.SESSION_TOKENS)" % str(HERE)
        for part, expected in (("layer", "0"), ("stable", "15000"), ("", "15000")):
            out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True,
                                 env=dict(os.environ, ORCH_BASE_PART=part))
            self.assertEqual(out.stdout.strip(), expected, part)


if __name__ == "__main__":
    unittest.main()


class TransitionTests(unittest.TestCase):
    """A layer is replaced while sessions forked from the one before it are still working."""

    def setUp(self):
        self.w = fakes.World()
        self.w.base("xhigh", sid="xhigh-sid")
        (self.w.state / "xhigh-base.json").write_text(json.dumps(
            {"sessionId": "xhigh-sid", "model": "claude-opus-5[1m]", "effort": "xhigh", "context": 310_000}))
        self.now = "layer-2"
        self.record_layer(self.now, base="xhigh-sid")

    def tearDown(self):
        self.w.close()

    def record_layer(self, sid, base="xhigh-sid"):
        (self.w.state / "xhigh-layer.json").write_text(json.dumps(
            {"sessionId": sid, "model": "claude-opus-5[1m]", "effort": "xhigh", "context": 525_000, "base": base,
             "sealed": "2026-09-20T10:00:00"}))

    def py(self, code):
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); import v2\n{code}"],
                             env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        return out.stdout.strip()

    def test_a_session_on_the_layer_before_a_refresh_no_longer_marks_the_new_one_warm(self):
        # warmth is marked per base name, and a worker's origin is that name: without this, a session still running
        # on the layer it forked would keep the layer that replaced it looking warm while nothing had read it, and
        # the first fork of the new one would pay a cold write of its whole size
        self.w.session("design-1", "designer", "d1", origin="xhigh", origin_sid="layer-1")  # the layer before
        self.w.session("design-2", "designer", "d2", origin="xhigh", origin_sid=self.now)  # the one that stands
        old = 10_000
        for name in ("xhigh-base.hit",):
            (self.w.state / name).write_text("")
            os.utime(self.w.state / name, (time.time() - old, time.time() - old))
        self.py("v2.hit_chain('design-1')")
        self.assertGreater(time.time() - (self.w.state / "xhigh-base.hit").stat().st_mtime, old - 60,
                           "a session on the layer before the refresh marked the base")
        self.assertTrue((self.w.state / "hits/design-1").exists())  # its own entry is warm, and that is true
        self.py("v2.hit_chain('design-2')")
        self.assertLess(time.time() - (self.w.state / "xhigh-base.hit").stat().st_mtime, 60,
                        "a session on the layer that stands did not mark it")

    def test_an_orphaned_layer_is_not_forked(self):
        self.assertEqual(self.py("print(v2.base_record('xhigh')[1]['sid'])"), self.now)
        self.record_layer(self.now, base="a-base-that-was-rebuilt-away")
        self.assertEqual(self.py("print(v2.layer_record('xhigh'))"), "None")
        self.assertEqual(self.py("print(v2.base_record('xhigh')[1]['sid'])"), "xhigh-sid")

    def test_a_layer_s_snapshot_is_kept_while_a_session_holds_it_and_swept_when_none_does(self):
        for sid in ("layer-1", "layer-2", "layer-0"):
            (self.w.state / f"layer-{sid}-manifest.json").write_text(json.dumps({"taken": "t", "files": {}}))
        self.w.session("design-1", "designer", "d1", origin="xhigh", origin_sid="layer-1", state="working")
        gone = self.py("print(sorted(v2.tidied()))")
        self.assertIn("layer-layer-0-manifest.json", gone)      # nothing holds it and it is not the one forked
        self.assertNotIn("layer-layer-1-manifest.json", gone)   # a session still holds that layer
        self.assertNotIn("layer-layer-2-manifest.json", gone)   # it is the layer that stands


class StalenessTests(unittest.TestCase):
    """What a session is told changed since its load, when the layer has been refreshed under it."""

    def setUp(self):
        self.w = fakes.World()
        (self.w.project / "held-a.md").write_text("the stable part\n")
        (self.w.project / "held-b.md").write_text("the frontier, as it was\n")
        self.list = self.w.project / "list.txt"
        self.list.write_text("# pinned: the stable reference\nheld-a.md\n"
                             "# === layer ===\n# the working frontier, as statements\nheld-b.md\n")
        self.env = dict(self.w.env, ORCH_LOAD_LIST=str(self.list))

    def tearDown(self):
        self.w.close()

    def manifest(self, *args):
        out = subprocess.run([sys.executable, str(HERE / "manifest.py"), *args], env=self.env,
                             capture_output=True, text=True)
        return out.stdout.strip()

    def test_a_session_is_told_what_changed_since_the_layer_it_actually_holds(self):
        self.manifest("snapshot", "xhigh")                       # everything as it stands: the stable snapshot
        (self.w.state / "xhigh-layer-manifest.json").write_text((self.w.state / "xhigh-manifest.json").read_text())
        held = json.loads((self.w.state / "xhigh-manifest.json").read_text())
        (self.w.state / "layer-old-manifest.json").write_text(json.dumps(
            {"taken": "2026-09-20T09:00:00",
             "files": {p: ("0" * 40 if p.endswith("held-b.md") else h) for p, h in held["files"].items()}}))
        # the layer standing now was sealed on the current frontier, so against it nothing has changed
        self.assertIn("none", self.manifest("changed", "xhigh"))
        # a session that forked the layer before it holds the older copy, and is told so
        self.assertIn("held-b", self.manifest("changed", "xhigh", "--since-layer", "old"))
        # a session whose layer's snapshot is gone falls back to the one standing rather than saying nothing
        self.assertIn("none", self.manifest("changed", "xhigh", "--since-layer", "a-layer-swept-long-ago"))


class FrontierMeasureTests(unittest.TestCase):
    """What counts as consulting a theory, when the reading the protocols prescribe names facts and not files."""

    def transcript(self, command, result="x" * 5000):
        import tempfile
        self.temp = tempfile.TemporaryDirectory()
        path = Path(self.temp.name) / "s.jsonl"
        lines = [
            {"type": "assistant", "message": {"content": [
                {"type": "tool_use", "id": "t1", "name": "Bash", "input": {"command": command}}]}},
            {"type": "user", "message": {"content": [
                {"type": "tool_result", "tool_use_id": "t1", "content": result}]}},
        ]
        path.write_text("".join(json.dumps(l) + "\n" for l in lines))
        return str(path)

    def tearDown(self):
        if hasattr(self, "temp"):
            self.temp.cleanup()

    def test_a_gather_that_names_a_fact_counts_for_its_theory(self):
        # the planner, the task designer and the reviewer read statements by name, and counting only file paths made
        # that reading invisible: the xhigh roles measured one theory on 2026-09-20 and the implementers six
        use = select_base_load.measure([self.transcript(
            ".claude/orchestration/v2.py step 7 1 Development_Machinery.development_machinery_def")])
        self.assertIn("theories/Development_Machinery.thy", use)

    def test_a_gather_that_names_a_file_still_counts(self):
        use = select_base_load.measure([self.transcript("cat theories/Development_Machinery.thy")])
        self.assertIn("theories/Development_Machinery.thy", use)

    def test_prose_that_merely_mentions_a_word_does_not_count(self):
        use = select_base_load.measure([self.transcript("echo 'the machinery is ready. and so on.'")])
        self.assertEqual(use, {})


class BaseScriptTests(unittest.TestCase):
    """base.sh reads the list of the base it was asked for, and not another's."""

    def list_seen_by(self, who):
        """Which list base.sh's own line resolves to for that base. Asked here rather than by running
        `base.sh WHO layer`, which builds one: a test starts no session."""
        out = subprocess.run(
            [sys.executable, "-c", "import sys; sys.path.insert(0, sys.argv[1]); import manifest; "
             "print(manifest.load_list())", str(HERE)],
            capture_output=True, text=True,
            env=dict(os.environ, ORCH_LOAD_LIST=str(HERE / manifest.LISTS[who])))
        return out.stdout.strip()

    def test_base_sh_reads_the_list_of_the_base_it_was_asked_for(self):
        # manifest falls back to max's list when none is named, so without naming it every base read max's: no layer
        # could ever be built, and `base.sh xhigh layer` refused "not split" (2026-09-20, caught before the build)
        for who in ("max", "xhigh", "high"):
            self.assertEqual(self.list_seen_by(who), str(HERE / manifest.LISTS[who]))
        line = next(l for l in (HERE / "base.sh").read_text().splitlines() if l.startswith("split="))
        self.assertIn("ORCH_LOAD_LIST=", line)  # base.sh names the list; nothing is inherited


class StartGuardTests(unittest.TestCase):
    """A split base whose layer has not been built is a reference with no direction in it."""

    def setUp(self):
        self.w = fakes.World()
        self.w.base("xhigh", sid="xhigh-sid")
        self.list = self.w.project / "split.txt"
        (self.w.project / "ref.md").write_text("the stable reference\n")
        (self.w.project / "front.md").write_text("the frontier and the direction\n")
        self.list.write_text("# pinned: the reference\nref.md\n"
                             "# === layer ===\n# the working frontier, as statements\nfront.md\n")

    def tearDown(self):
        self.w.close()

    def layerless(self, manifest_files):
        (self.w.state / "xhigh-manifest.json").write_text(json.dumps({"taken": "t", "files": manifest_files}))
        code = ("import sys, os; sys.path.insert(0, %r); import manifest; "
                "manifest.LISTS['xhigh'] = %r; import v2; print(','.join(v2.layerless()))" % (str(HERE), str(self.list)))
        out = subprocess.run([sys.executable, "-c", code], env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        return out.stdout.strip()

    def test_a_base_built_from_the_reference_alone_has_no_layer_to_fork(self):
        ref = str(self.w.project / "ref.md")
        self.assertEqual(self.layerless({ref: "d"}), "xhigh")

    def test_a_base_built_from_the_whole_list_needs_none(self):
        # it was built before the list was split: what it holds is the question, not what the list says now
        files = {str(self.w.project / "ref.md"): "d", str(self.w.project / "front.md"): "d"}
        self.assertEqual(self.layerless(files), "")

    def test_a_base_with_a_layer_recorded_needs_none(self):
        (self.w.state / "xhigh-layer.json").write_text(json.dumps(
            {"sessionId": "l", "model": "m", "effort": "xhigh", "context": 1, "base": "xhigh-sid"}))
        self.assertEqual(self.layerless({str(self.w.project / "ref.md"): "d"}), "")
