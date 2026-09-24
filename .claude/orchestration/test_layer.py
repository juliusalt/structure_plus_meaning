"""The layered bases: a list split into a stable reference and a frontier layer (notes/bases-design.md section 8).

The stable reference is rebuilt rarely, and that is the owner's; the layer holds the working frontier and the
direction, and the harness refreshes it on its own. A fork of the layer reads the whole prefix under it from cache —
measured on 2026-09-20: a fork of the sealed knowledge base, a layer over `max` in all but name, read 538,051 of its
538,044 tokens and wrote 62 — so the layer is what every role forks and what is pinged.
"""
import json
import re
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

PROJECT = Path(os.environ.get("ORCH_PROJECT") or HERE.parent.parent)


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
    def test_named_parts_retain_the_owner_reference_and_explicit_deepening(self):
        for who in ('max','xhigh','high'):
            path=HERE/manifest.LISTS[who]
            es=manifest.list_entries(path.read_text(),str(PROJECT))
            # ordered by how rarely their cause acts: the direction's text changed in 2 of the run's 472 commits, the
            # reasoning inventory's in 6 (with landings that publish a pattern), the catalogue's in 187 (2026-09-23)
            self.assertEqual(manifest.layer_names(path),['direction','inventory','catalogue'] if who!='high' else ['direction','catalogue'])
            self.assertTrue(any(e['part']=='stable' and e['path'].endswith('RRA_Core.thy') for e in es))
            # the owner's words first: everything held rests on the owner's intent, and none of it changed in the run
            self.assertTrue(any(e['part']=='stable' and e['path'].endswith('owner-directions.md') for e in es))
            self.assertTrue(any(e['part']=='direction' and e['path'].endswith('decisions-index.md') for e in es))
            seen={}
            for e in es:
                if e['path'] in seen:
                    self.assertGreater(select_base_load.DEPTH_ORDER[e['level']],select_base_load.DEPTH_ORDER[seen[e['path']]])
                    self.assertIsNotNone(e['deepens'])
                seen[e['path']]=e['level']

    def test_every_base_has_the_whole_vocabulary_and_original_conditions(self):
        for who in ('max','xhigh','high'):
            text=(HERE/manifest.LISTS[who]).read_text()
            for name in (f'theory-map-index-{who}.md',f'tool-index-{who}.md','decisions-index.md','problems.txt'):
                self.assertIn(name,text)
            # the plan's map where the plan itself is not held (high); max and xhigh hold the plan whole
            self.assertEqual('plan-index.md' in text, who=='high')
            self.assertIn('purpose=steering',text)
            self.assertIn('purpose=both',text)

    def test_generated_relations_stand_in_the_inventory_and_nothing_depends_on_the_queue(self):
        # a base holds no task's relations: their union grew with the queue and every change of it rebuilt the base
        # (2026-09-23); the one generated tier is the whole plan's notions, which the plan names and the inventory's
        # reasoning is about: under it, and over the plan (high holds none, its tier empty in the catalogue)
        for who in ('max','xhigh','high'):
            text=(HERE/manifest.LISTS[who]).read_text()
            if who=='high':
                self.assertLess(text.index('# === layer catalogue ==='),text.index('# === relations ==='))
            else:
                self.assertLess(text.index('# === layer inventory ==='),text.index('# === relations ==='))
                self.assertLess(text.index('# === end relations ==='),text.index('\nREASONING_REUSE.md\n'))
                self.assertLess(text.index('\nREASONING_REUSE.md\n'),text.index('# === layer catalogue ==='))
            self.assertNotIn('# === layer working ===',text)
            block=text[text.index('# === relations ==='):text.index('# === end relations ===')]
            self.assertEqual(re.findall(r'^# relation: ([^;]+);',block,re.M),['whole-plan notions'])



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
             "sealed": "2026-09-20T10:00:00", "flags": fakes.LEAN}))

    def py(self, code):
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); import v2\n{code}"],
                             env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        return out.stdout.strip()

    def test_a_session_on_a_layer_marks_its_own_entry_and_never_the_layer(self):
        # a request reads the longest prefix cached — the session's own — and a shorter entry under it is not kept alive
        # by that read: design-171's requests kept the xhigh layer looking warm while its entry expired unpinged, and
        # the next two forks of it wrote 235K each (2026-09-22 13:45); a session on the layer before a refresh would
        # mark the new one besides. The layer is marked by what reads it: a fork's start, and its ping.
        self.w.session("design-1", "designer", "d1", origin="xhigh", origin_sid="layer-1")  # the layer before
        self.w.session("design-2", "designer", "d2", origin="xhigh", origin_sid=self.now)  # the one that stands
        old = 10_000
        (self.w.state / "xhigh-base.hit").write_text("")
        os.utime(self.w.state / "xhigh-base.hit", (time.time() - old, time.time() - old))
        self.py("v2.hit('design-1'); v2.hit('design-2')")
        self.assertGreater(time.time() - (self.w.state / "xhigh-base.hit").stat().st_mtime, old - 60,
                           "a session's request marked the layer under it")
        self.assertTrue((self.w.state / "hits/design-1").exists() and (self.w.state / "hits/design-2").exists())

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
            {"sessionId": "l", "model": "m", "effort": "xhigh", "context": 1, "base": "xhigh-sid", "flags": fakes.LEAN}))
        self.assertEqual(self.layerless({str(self.w.project / "ref.md"): "d"}), "")
