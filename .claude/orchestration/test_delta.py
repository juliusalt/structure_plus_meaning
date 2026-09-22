"""The delta layer (notes/plan-delta-layer.md): what a base holds that has changed since the part holding it loaded,
given in its new form — the text a delta session holds, forked by every role of the base."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
import manifest  # noqa: E402
import test_base_warm  # noqa: E402
import watchdog  # noqa: E402
import v2  # noqa: E402
from digest import held_text  # noqa: E402

LEMMAS = "".join(f'lemma l{i}: "P{i} x"\n  by simp\n\n' for i in range(40))
THEORY = "theory A imports Main begin\n\n{body}end\n"
DOC = "# Notes\n\nIntro.\n\n## One\n\nThe first section.\n\n## Two\n\nThe second section.\n"
INDEX = "Alpha\nBeta\nGamma\n"


class DeltaTextTests(unittest.TestCase):
    """manifest.delta_entries and delta_text over a split list, the loads given as the packs would restore them."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        root = Path(self.temp.name)
        self.root = root
        (root / "theories").mkdir()
        (root / "docs").mkdir()
        self.write("docs/S.md", "# Stable\n\nThe reference.\n")
        self.write("theories/A.thy", THEORY.format(body=LEMMAS))
        self.write("docs/N.md", DOC)
        self.write("docs/theory-names.md", INDEX)
        self.list = root / "list.txt"
        self.list.write_text("# pinned: the stable reference\ndocs/S.md\n# === layer ===\n"
                             "# the working frontier, as statements\ntheories/A.thy\ndocs/N.md\ndocs/theory-names.md\n")
        self.patches = [patch.object(manifest, "PROJECT", str(root)), patch.object(manifest, "load_list",
                                                                                   lambda: str(self.list)),
                        patch.object(manifest, "INDEXES", ("theory-names.md",))]
        for p in self.patches:
            p.start()
        self.loaded = {"stable": self.held(), "layer": self.held()}
        self.loaded["stable"] = {p: t for p, t in self.loaded["stable"].items() if p.endswith("S.md")}
        self.loaded["layer"] = {p: t for p, t in self.loaded["layer"].items() if not p.endswith("S.md")}
        self.patches.append(patch.object(manifest, "loaded_texts", lambda who, part: self.loaded[part]))
        self.patches[-1].start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.temp.cleanup()

    def write(self, rel, text):
        (self.root / rel).write_text(text)

    def held(self):
        """{path: held text now} of every held file, as a part's load would hold it."""
        return {path: held_text(path, manifest.level_of(path))[0] for _, path in manifest.held_files("")}

    def entry(self, name):
        return next(e for e in manifest.delta_entries("high") if e[0].endswith(name))

    def test_one_lemma_changed_is_that_lemma_alone_in_its_new_form(self):
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "Q7 x"')))
        path, part, kind, text, tokens = self.entry("A.thy")
        self.assertEqual((part, kind), ("layer", "changed"))
        self.assertIn('lemma l7: "Q7 x"', text)
        self.assertNotIn("P7", text)                                  # the old form is not repeated
        self.assertNotIn("lemma l8", text)                            # nor any lemma that did not change
        self.assertLess(tokens, manifest.tokens(path) / 10)           # a part of the file, not the file

    def test_a_removed_lemma_is_named_and_an_added_one_given_whole(self):
        body = LEMMAS.replace('lemma l5: "P5 x"\n  by simp\n\n', "") + 'lemma added: "R x"\n  by simp\n\n'
        self.write("theories/A.thy", THEORY.format(body=body))
        text = self.entry("A.thy")[3]
        self.assertIn("removed: lemma l5", text)
        self.assertNotIn("P5", text)
        self.assertIn('lemma added: "R x"', text)

    def test_a_changed_section_is_given_whole_and_the_others_not(self):
        self.write("docs/N.md", DOC.replace("The first section.", "The first section, rewritten."))
        text = self.entry("N.md")[3]
        self.assertIn("## One\n\nThe first section, rewritten.", text)
        self.assertNotIn("The second section", text)

    def test_an_index_moves_by_its_lines(self):
        self.write("docs/theory-names.md", INDEX + "Delta\n")
        self.assertEqual(self.entry("theory-names.md")[3], "Delta")

    def test_a_new_file_is_whole_and_a_gone_one_named(self):
        self.write("theories/B.thy", THEORY.format(body='lemma b: "B x"\n  by simp\n\n').replace("theory A", "theory B"))
        self.list.write_text(self.list.read_text().replace("docs/N.md\n", "theories/B.thy\n"))
        entries = {os.path.basename(e[0]): e for e in manifest.delta_entries("high")}
        self.assertEqual(entries["B.thy"][2], "new")
        self.assertIn('lemma b: "B x"', entries["B.thy"][3])
        self.assertEqual(entries["N.md"][2:4], ("gone", ""))

    def test_the_stable_part_s_changes_are_held_and_counted_apart(self):
        self.write("docs/S.md", "# Stable\n\nThe reference, amended.\n")
        text, layer, stable = manifest.delta_text("high")
        self.assertIn("docs/S.md (the stable reference)", text)
        self.assertIn("The reference, amended.", text)
        self.assertEqual(layer, 0)
        self.assertGreater(stable, 0)

    def test_nothing_changed_is_no_delta(self):
        self.assertEqual(manifest.delta_entries("high"), [])
        self.assertEqual(manifest.delta_text("high"), ("", 0, 0))

    def test_the_header_says_what_it_supersedes_and_a_part_that_cannot_be_read_back(self):
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('"P3 x"', '"Q3 x"')))
        self.loaded["stable"] = {}                                    # the stable base's pack is gone
        text, layer, _ = manifest.delta_text("high")
        self.assertIn("it supersedes what you hold of those parts; everything else you hold is current", text)
        self.assertIn("(The stable part's load cannot be read back, so its changes are not here.)", text)
        self.assertGreater(layer, 0)


PROJECT = HERE.parent.parent
TRANSCRIPTS = str(PROJECT).replace("/", "-").replace("_", "-")
LEAN = " ".join((HERE / "session-flags").read_text().split())
FAKE = """#!/usr/bin/env python3
import json, os, re, sys
args = sys.argv[1:]
calls = os.environ['DELTA_TEST_CALLS']
with open(calls, 'a') as f:
    f.write(json.dumps(args) + chr(10))
started = [a[a.index('-n') + 1] for a in map(json.loads, open(calls)) if '--bg' in a and '-n' in a]
if args[:2] == ['agents', '--json']:
    print(json.dumps([dict(kind='background', id='id-' + n, status='idle', state='done', sessionId='fork-' + n,
                           cwd=os.environ['DELTA_TEST_CWD'], name=n) for n in started]))
elif '--bg' in args:
    name, prompt = args[args.index('-n') + 1], args[-1]
    held = re.search(r'HELD ([0-9a-f]{12})', prompt)
    reply = os.environ.get('DELTA_TEST_REPLY') or ('HELD ' + held.group(1) if held else 'An answer.')
    usage = {'input_tokens': 2, 'cache_read_input_tokens': 578000, 'cache_creation_input_tokens': 9000}
    with open(os.path.join(os.environ['DELTA_TEST_SESSIONS'], 'fork-' + name + '.jsonl'), 'w') as f:
        f.write(json.dumps({'type': 'user', 'message': {'role': 'user', 'content': prompt}}) + chr(10))
        f.write(json.dumps({'type': 'assistant', 'message': {'id': 'm1', 'model': 'claude-opus-5', 'usage': usage,
                            'content': [{'type': 'text', 'text': reply}]}}) + chr(10))
"""


class DeltaScriptTests(unittest.TestCase):
    """base.sh WHO delta: a fork of the recorded layer holding the delta as its one message, verified and recorded."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        root = Path(self.temp.name)
        self.state, home, binary = root / "state", root / "home", root / "bin"
        self.sessions = home / ".claude/projects" / TRANSCRIPTS
        for d in (self.state, binary, self.sessions):
            d.mkdir(parents=True)
        (binary / "claude").write_text(FAKE)
        (binary / "claude").chmod(0o755)
        record = {"model": "claude-opus-5[1m]", "effort": "high", "flags": LEAN}
        (self.state / "high-base.json").write_text(json.dumps(dict(record, sessionId="stable-sid", name="high-base")))
        self.layer_record()
        self.text = root / "delta.md"
        self.text.write_text("What you hold has changed since it loaded.\n\n== theories/A.thy\nlemma l7: Q7\n")
        self.calls = root / "calls.jsonl"
        self.env = {k: v for k, v in os.environ.items() if not k.startswith(("CLAUDE", "ORCH_"))}
        self.env.update(PATH=str(binary) + os.pathsep + os.environ["PATH"], HOME=str(home), ORCH_STATE_DIR=str(self.state),
                        DELTA_TEST_CWD=str(PROJECT), DELTA_TEST_CALLS=str(self.calls),
                        DELTA_TEST_SESSIONS=str(self.sessions), BASE_DELTA_TEXT=str(self.text), LAYER_WAIT="3")

    def tearDown(self):
        self.temp.cleanup()

    def layer_record(self, base="stable-sid"):
        (self.state / "high-layer.json").write_text(json.dumps(
            {"sessionId": "layer-sid", "name": "high-layer-1", "model": "claude-opus-5[1m]", "effort": "high",
             "base": base, "flags": LEAN, "sealed": "2026-09-22T19:26:20", "context": 595000}))

    def delta(self, *extra, env=None):
        return subprocess.run(["sh", str(HERE / "base.sh"), "high", "delta", *extra], env=dict(self.env, **(env or {})),
                              capture_output=True, text=True, timeout=60)

    def calls_made(self):
        return [json.loads(line) for line in self.calls.read_text().splitlines()] if self.calls.exists() else []

    def forks(self):
        return [(a[a.index("--resume") + 1], a[a.index("-n") + 1]) for a in self.calls_made() if "--bg" in a]

    def test_a_build_that_fails_says_why_where_the_run_is_read(self):
        # a build started by the watchdog is read by nobody: what it refuses to do goes to warm.log, timestamped, so
        # that a refresh which leaves nothing behind but a pack (the high layer, 2026-09-22 21:36) says why
        self.layer_record(base="a-base-that-is-gone")                   # its layer stands on a base that is gone
        out = self.delta()
        self.assertEqual(out.returncode, 1)
        self.assertIn("no sealed high base with a layer to hold a delta over", out.stderr)
        said = (self.state / "warm.log").read_text().splitlines()
        self.assertEqual(len(said), 1, said)
        self.assertRegex(said[0], r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d no sealed high base with a layer")
        # started with warm.log for its stderr (the daemon's `2>> warm.log`), it says it there once, not twice
        warm = self.state / "warm.log"
        warm.write_text("")
        subprocess.run(f"sh {HERE / 'base.sh'} high delta >/dev/null 2>> {warm}", shell=True, env=self.env, timeout=60)
        self.assertEqual(len(warm.read_text().splitlines()), 1, warm.read_text())

    def test_the_delta_is_a_fork_of_the_layer_verified_snapshotted_and_recorded(self):
        out = self.delta()
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        ((resumed, name),) = self.forks()
        self.assertEqual(resumed, "layer-sid")                          # the layer, not the stable base under it
        record = json.loads((self.state / "high-delta.json").read_text())
        self.assertEqual((record["sessionId"], record["layer"], record["base"]), ("fork-" + name, "layer-sid",
                                                                                   "stable-sid"))
        self.assertEqual(record["flags"], LEAN)
        self.assertGreater(record["tokens"], 0)
        self.assertTrue(Path(record["text"]).read_text().startswith("What you hold has changed"))
        snapshot = json.loads((self.state / f"layer-{record['sessionId']}-manifest.json").read_text())
        self.assertTrue(snapshot["delta"])                               # a stale line measures from the delta
        for mark in ("high-base.hit", "high-base.used", "high-layer.hit"):
            self.assertTrue((self.state / mark).exists(), mark)
        self.assertIn(["stop", "id-" + name], self.calls_made())        # sealed: stopped, not removed
        self.assertNotIn(["rm", "id-" + name], self.calls_made())
        self.assertIn("delta high:", (self.state / "warm.log").read_text())
        # a second build replaces it, and the one it replaces is stopped, never removed (the fake lists every session
        # it started, so its calls are kept and read from here on)
        before = len(self.calls_made())
        time.sleep(1.1)                                                 # a delta is named by its second
        self.assertEqual(self.delta().returncode, 0)
        later = self.calls_made()[before:]
        self.assertIn(["stop", "id-" + name], later)
        self.assertFalse(any(c[:1] == ["rm"] for c in later))

    def test_a_delta_not_held_is_not_recorded(self):
        out = self.delta(env={"DELTA_TEST_REPLY": "I will look at the files first."})
        self.assertEqual(out.returncode, 3, out.stdout + out.stderr)
        self.assertFalse((self.state / "high-delta.json").exists())
        self.assertIn("not recorded", (self.state / "warm.log").read_text())
        ((_, name),) = self.forks()
        self.assertIn(["stop", "id-" + name], self.calls_made())

    def test_nothing_changed_starts_nothing(self):
        self.text.write_text("")
        out = self.delta()
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("no delta", out.stdout)
        self.assertEqual(self.forks(), [])

    def test_a_build_over_the_layer_holds_it_off(self):
        (self.state / "high-layer.building").write_text("123")
        out = self.delta()
        self.assertEqual(out.returncode, 3)
        self.assertIn("is being built", out.stderr)
        self.assertEqual(self.forks(), [])

    def test_a_layer_on_a_base_that_is_gone_holds_no_delta(self):
        self.layer_record(base="a-base-rebuilt-away")
        self.assertEqual(self.delta().returncode, 1)
        self.assertEqual(self.forks(), [])

    def test_a_delta_over_the_argument_limit_is_loaded_by_chunks(self):
        out = self.delta(env={"DELTA_ARG": "10"})                        # the text is longer than 10 bytes
        ((_, name),) = self.forks()
        prompt = next(a[-1] for a in self.calls_made() if "--bg" in a)
        self.assertIn("Load the reference library", prompt)              # the pack's bootstrap, not the text
        self.assertNotIn("lemma l7", prompt)
        self.assertEqual(out.returncode, 3)                              # the fake loads no chunks: refused, as it must

    def test_the_canary_asks_a_fork_of_the_delta_and_keeps_its_answer(self):
        self.assertEqual(self.delta().returncode, 0)
        record = json.loads((self.state / "high-delta.json").read_text())
        out = self.delta("--ask", "What does lemma l7 state?")
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        resumed, name = self.forks()[-1]
        self.assertEqual(resumed, record["sessionId"])
        self.assertEqual((self.state / "high-delta-answer.txt").read_text().strip(), "An answer.")
        self.assertIn(["rm", "id-" + name], self.calls_made())          # the canary's fork is removed


class StableListedTests(unittest.TestCase):
    """manifest.py stable-listed: whether the stable base recorded loaded what the list's stable part names now."""

    def test_the_recorded_stable_base_is_the_list_s_only_while_it_loaded_the_same_files(self):
        with tempfile.TemporaryDirectory() as temp:
            state, lst = Path(temp) / "state", Path(temp) / "list.txt"
            state.mkdir()
            lst.write_text(f"# reference\n{HERE / 'README.md'}\n# === layer === below\n# direction\n{HERE / 'v2.py'}\n")
            env = dict({k: v for k, v in os.environ.items() if not k.startswith("ORCH_")},
                       ORCH_STATE_DIR=str(state), ORCH_LOAD_LIST=str(lst))
            listed = lambda: subprocess.run([sys.executable, str(HERE / "manifest.py"), "stable-listed", "high"], env=env,
                                            capture_output=True, text=True)
            self.assertEqual(listed().returncode, 1)                     # no snapshot of a stable base at all
            (state / "high-manifest.json").write_text(json.dumps({"files": {str(HERE / "README.md"): "x"}}))
            self.assertEqual(listed().returncode, 0)                     # its contents may have moved: the delta's
            lst.write_text(lst.read_text().replace("# === layer", f"{HERE / 'base.sh'}\n# === layer"))
            out = listed()
            self.assertEqual(out.returncode, 1)                          # the list names another reference now
            self.assertIn("names 1 file(s) the high stable base did not load and leaves out 0", out.stdout)


class DeltaCostTests(unittest.TestCase):
    """What a delta has cost since its layer sealed (carried), and what a refresh costs (refresh_cost)."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.state = Path(self.temp.name)
        (self.state / "high-base.json").write_text(json.dumps({"sessionId": "stable-sid", "context": 276_298}))
        (self.state / "high-layer.json").write_text(json.dumps(
            {"sessionId": "layer-sid", "base": "stable-sid", "context": 601_541, "sealed": "2026-09-22T22:18:14"}))
        self.sealed = time.mktime(time.strptime("2026-09-22T22:18:14", "%Y-%m-%dT%H:%M:%S"))
        self.patches = [patch.object(watchdog, "STATE", str(self.state)), patch.object(v2, "STATE", str(self.state))]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def test_what_every_fork_of_the_delta_carried_and_every_build_wrote(self):
        after, before = self.sealed + 600, self.sealed - 600
        sessions = {"fix-1": dict(origin="high", started=after, delta_tokens=5000, sid="a"),
                    "fix-2": dict(origin="high", started=before, delta_tokens=5000, sid="b"),   # forked the old layer
                    "review-3": dict(origin="xhigh", started=after, delta_tokens=5000, sid="c"),  # another base's
                    "fix-4": dict(origin="high", started=after, sid="d")}                        # forked no delta
        (self.state / "v2.json").write_text(json.dumps({"sessions": sessions, "tasks": {}, "queue": [], "events": []}))
        (self.state / "warm.log").write_text(
            "2026-09-22T22:36:26 delta high: OK   session fork 00bbf073 of base bf471854: first own request "
            "cache_read=601539 cache_write=6451 uncached=2 (98% read)\n"
            "2026-09-22T21:15:09 delta high: OK   session fork 72dc01e5 of base e3a1676c: first own request "
            "cache_read=600393 cache_write=4000 uncached=2 (99% read)\n"                   # before the layer sealed
            "2026-09-22T22:40:00 delta xhigh: OK   session fork 11111111 of base 22222222: first own request "
            "cache_read=500000 cache_write=9000 uncached=2 (99% read)\n")
        with patch.object(watchdog, "own_requests", lambda s: 20):
            self.assertAlmostEqual(watchdog.carried("high"), 0.1 * 5000 * 20 + 2 * 6451)

    def test_a_session_s_own_requests_are_its_turns_from_its_launch(self):
        launched = self.sealed + 60
        stamp = lambda t: time.strftime("%Y-%m-%dT%H:%M:%S.000Z", time.gmtime(t))
        turn = lambda mid, t: {"type": "assistant", "timestamp": stamp(t), "message": {"id": mid, "usage": {"input_tokens": 1}}}
        path = self.state / "fork.jsonl"
        path.write_text("".join(json.dumps(r) + "\n" for r in (turn("copied", launched - 3600), turn("m1", launched + 10),
                                                                turn("m1", launched + 11), turn("m2", launched + 20))))
        with patch.object(v2, "transcript", lambda sid: str(path)):
            self.assertEqual(watchdog.own_requests({"sid": "x", "started": launched}), 2)

    def test_a_refresh_costs_its_layer_written_over_a_read_of_the_stable_base(self):
        self.assertAlmostEqual(watchdog.refresh_cost("high"), 2 * (601_541 - 276_298) + 0.1 * 276_298)
        (self.state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-sid"}))
        self.assertIsNone(watchdog.refresh_cost("high"))


class DeltaForkTests(unittest.TestCase):
    """What a role of the base forks once a delta stands on its layer, and what it is told has changed since."""

    def setUp(self):
        self.w = fakes.World()
        rec = {"model": "claude-opus-5[1m]", "effort": "high", "flags": fakes.LEAN}
        self.standing = self.w.state / "high-delta-20260922T190000.md"
        (self.w.state / "high-base.json").write_text(json.dumps(dict(rec, sessionId="stable-sid")))
        self.layer("layer-sid")
        (self.w.state / "high-delta.json").write_text(json.dumps(dict(
            rec, sessionId="delta-sid", layer="layer-sid", base="stable-sid", text=str(self.standing))))

    def tearDown(self):
        self.w.close()

    def layer(self, sid, base="stable-sid"):
        (self.w.state / "high-layer.json").write_text(json.dumps(
            {"sessionId": sid, "base": base, "model": "claude-opus-5[1m]", "effort": "high", "flags": fakes.LEAN}))

    def py(self, code, **env):
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); import v2\n{code}"],
                             env=dict(self.w.env, **env), capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        return out.stdout.strip()

    def test_a_fork_of_the_delta_records_what_the_delta_adds_to_its_layer(self):
        # what the watchdog weighs against a refresh (carried): each of its requests carries that many tokens
        for name, context in (("high-layer.json", 601_541), ("high-delta.json", 607_992)):
            rec = json.loads((self.w.state / name).read_text())
            (self.w.state / name).write_text(json.dumps(dict(rec, context=context)))
        start = ("n = v2.launch('implementer', '7', lambda n: 'You are implement-7, working on task 7.', tree=None)\n"
                 "print(v2.peek()['sessions'][n].get('delta_tokens'))")
        self.assertEqual(self.py(start), "None")                       # the layer is what its roles fork
        (self.w.state / "deltas").write_text("high\n")
        self.assertEqual(self.py(start.replace("'7'", "'8'").replace("-7", "-8").replace("task 7", "task 8")), "6451")

    def test_the_roles_fork_the_delta_once_the_base_is_switched_to_it(self):
        forked = "print(v2.base_record('high')[1]['sid'])"
        self.assertEqual(self.py(forked), "layer-sid")                 # built, not switched on: asked first (canary)
        (self.w.state / "deltas").write_text("high\n")
        self.assertEqual(self.py(forked), "delta-sid")
        self.assertEqual(self.py(forked, ORCH_DELTAS="xhigh"), "layer-sid")  # another base's switch is not this one's
        self.layer("layer-2")                                          # the layer refreshed: the delta is an orphan
        self.assertEqual(self.py(forked), "layer-2")
        self.assertEqual(self.py("print(v2.delta_record('high'))"), "None")

    def test_a_fork_that_missed_its_origin_marks_its_base(self):
        # a fork that missed wrote its own prefix, which no later fork reads: the base is marked, and the watchdog
        # makes what its roles fork anew (2026-09-22 21:04, three entries evicted within four minutes)
        base = test_base_warm.assistant("base-1", 0, 0, 500000)
        # session_fork_check reads the transcripts of the project it stands in, under the world's HOME
        where = Path(self.w.home) / ".claude/projects" / str(HERE.parent.parent).replace("/", "-").replace("_", "-")
        where.mkdir(parents=True, exist_ok=True)
        (where / "delta-sid.jsonl").write_text(json.dumps(base) + "\n")
        for sid, own in (("fork-miss", test_base_warm.assistant("own-1", 2, 0, 500062)),
                         ("fork-hit", test_base_warm.assistant("own-1", 2, 500000, 62))):
            (where / f"{sid}.jsonl").write_text(json.dumps(base) + "\n" + json.dumps(own) + "\n")
        mark = self.w.state / f"high-{v2.FORK_MISSED}"
        self.w.session("fix-9", "fixer", "fork-hit", task="9", origin="high")
        self.py("v2.cache_check('fork-hit', 'delta-sid', 'fix-9')")
        self.assertFalse(mark.exists())                                 # read from cache: nothing to make anew
        self.w.session("fix-9", "fixer", "fork-miss", task="9", origin="high")
        self.py("v2.cache_check('fork-miss', 'delta-sid', 'fix-9')")
        self.assertTrue(mark.exists())
        self.assertIn("cache of fix-9:", (self.w.state / "v2.log").read_text())

    def test_the_standing_delta_s_snapshot_and_text_are_kept_and_the_rest_swept(self):
        for sid in ("delta-sid", "delta-old"):
            (self.w.state / f"layer-{sid}-manifest.json").write_text(json.dumps({"taken": "t", "delta": True, "files": {}}))
        self.standing.write_text("the standing delta")
        old = self.w.state / "high-delta-20260922T120000.md"
        old.write_text("an older delta")
        for path in (self.standing, old):
            then = os.path.getmtime(path) - 5 * 3600
            os.utime(path, (then, then))
        gone = self.py("print(sorted(v2.tidied()))")
        self.assertIn("layer-delta-old-manifest.json", gone)
        self.assertNotIn("layer-delta-sid-manifest.json", gone)        # the delta standing, whether forked or not
        self.assertIn("high-delta-20260922T120000.md", gone)
        self.assertNotIn(self.standing.name, gone)                     # the next build reads it

    def test_a_fork_of_the_delta_is_told_only_what_changed_after_it(self):
        project = self.w.project
        (project / "stable.md").write_text("the reference\n")
        (project / "frontier.md").write_text("the frontier\n")
        listing = project / "list.txt"
        listing.write_text("# pinned: the stable reference\nstable.md\n# === layer ===\n# the working frontier\n"
                           "frontier.md\n")
        env = dict(self.w.env, ORCH_LOAD_LIST=str(listing))
        run = lambda *a: subprocess.run([sys.executable, str(HERE / "manifest.py"), *a], env=env, capture_output=True,
                                        text=True).stdout.strip()
        run("snapshot", "high")                                        # the stable load
        (self.w.state / "high-layer-manifest.json").write_text((self.w.state / "high-manifest.json").read_text())
        (project / "stable.md").write_text("the reference, amended before the delta\n")
        run("snapshot-delta", "high", str(self.w.state / "layer-delta-sid-manifest.json"))
        (project / "frontier.md").write_text("the frontier, changed after the delta\n")
        line = run("changed", "high", "--since-layer", "delta-sid")
        self.assertIn("since the high delta load", line)
        self.assertIn("frontier", line)
        self.assertNotIn("stable", line)                               # the delta holds that change already
        self.assertIn("stable", run("changed", "high"))                # a session on the layer is told of it


class DeltaWarmTests(unittest.TestCase):
    """What the daemon keeps warm under a delta: the delta the roles fork, and the layer under it, which only the
    delta's builds read (base.sh WHO warm, test_base_warm's harness)."""

    W = test_base_warm.WarmVerdictTests
    setUp, tearDown, warm, log, resumed, layer = W.setUp, W.tearDown, W.warm, W.log, W.resumed, W.layer

    def delta(self, layer="warm-test-layer"):
        (self.state / "max-delta.json").write_text(json.dumps(
            {"sessionId": "warm-test-delta", "layer": layer, "base": "warm-test-base", "model": "claude-opus-5",
             "effort": "max", "name": "max-delta-1", "flags": test_base_warm.LEAN}))
        sessions = Path(self.temp.name) / "home/.claude/projects" / test_base_warm.TRANSCRIPTS
        for sid in ("warm-test-delta", "warm-test-layer"):  # each pinged session's own requests, as the base's
            (sessions / f"{sid}.jsonl").write_text((sessions / "warm-test-base.jsonl").read_text())

    def stable_warm(self):
        return subprocess.run(["sh", str(HERE / "base.sh"), "max", "stable-warm"], env=self.env,
                              capture_output=True, text=True, timeout=60).returncode == 0

    def test_a_stable_base_whose_entry_was_missed_is_cold_whatever_its_last_read_says(self):
        # the max layer's refresh of 2026-09-22 21:28 forked a stable base evicted twelve minutes before, whose hit was
        # 51 minutes old, and wrote its 341K inside the layer's own prefix: no stable entry for the refreshes after it
        hit = self.state / "max-stable.hit"
        hit.write_text("")
        then = time.time() - 51 * 60
        os.utime(hit, (then, then))
        self.assertTrue(self.stable_warm())                             # read within the hour: its entry is there
        (self.state / "max-stable.miss").write_text("x\n")
        self.assertFalse(self.stable_warm())                            # missed since: it is not, and is loaded again
        (self.state / "max-stable.miss").unlink()
        then = time.time() - 70 * 60
        os.utime(hit, (then, then))
        self.assertFalse(self.stable_warm())                            # nor when its last read is past the hour

    def test_a_miss_recorded_before_the_base_was_sealed_is_not_its_entry_s(self):
        # a base that has just been loaded and sealed has its entry: `seal` marks it warm and the miss of the base
        # before it stayed behind, and stable_warm reading that would send every layer refresh from here on through a
        # fifteen-minute reload of the stable base (found 2026-09-22 21:55, with three stable misses standing)
        hit, miss = self.state / "max-stable.hit", self.state / "max-stable.miss"
        record = self.state / "max-base.json"
        hit.write_text("")
        miss.write_text("x\n")
        then = time.time() - 36 * 3600                                  # before any midnight: a record with no seal
        os.utime(miss, (then, then))                                    # time is no seal (`date -d ""` is midnight)
        self.assertFalse(self.stable_warm())                            # nothing says the base was loaded since
        held = json.loads(record.read_text())
        held["sealed"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        record.write_text(json.dumps(held))
        self.assertTrue(self.stable_warm())                             # sealed since the miss: the entry is its load's
        self.assertFalse(miss.exists())                                 # and the miss is taken, not read again

    def test_the_ping_goes_to_the_delta_the_roles_fork(self):
        self.layer()
        self.delta()
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-layer"])             # built, not switched on: the layer
        (self.state / "deltas").write_text("max\n")
        self.calls.write_text("")
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-delta"])
        self.delta(layer="a-layer-refreshed-away")                         # an orphan: the layer again
        self.calls.write_text("")
        self.warm()
        self.assertEqual(self.resumed(), ["warm-test-layer"])

    def test_the_layer_under_a_delta_is_pinged_on_its_own_when_due(self):
        self.layer()
        self.delta()
        ping = f"sh {HERE / 'base.sh'} max warm layer --if-due"
        hit = self.state / "max-layer.hit"
        hit.write_text("")
        then = time.time() - 45 * 60
        os.utime(hit, (then, then))
        self.warm(shell=ping)
        self.assertEqual(self.resumed(), [])                               # no delta forked: the layer's own ping does it
        (self.state / "deltas").write_text("max\n")
        self.warm(shell=ping)
        self.assertEqual(self.resumed(), ["warm-test-layer"])
        self.assertIn("warm max layer: OK", self.log())
        self.assertGreater(hit.stat().st_mtime, then + 60)                 # its own time, refreshed
        self.calls.write_text("")
        (self.state / "max-layer.pinging").write_text("")                  # one going already: not a second
        then = time.time() - 45 * 60
        os.utime(hit, (then, then))
        self.warm(shell=ping)
        self.assertEqual(self.resumed(), [])
        (self.state / "max-layer.pinging").unlink()
        for ago in (10 * 60, 70 * 60):                                     # early; cold, left alone
            self.calls.write_text("")
            then = time.time() - ago
            os.utime(hit, (then, then))
            self.warm(shell=ping)
            self.assertEqual(self.resumed(), [], ago)


class DeltaTriggerTests(unittest.TestCase):
    """When the watchdog builds a delta (deltas) and when it refreshes the layer under one (layers)."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.state = Path(self.temp.name)
        rec = {"model": "claude-opus-5[1m]", "effort": "high", "flags": LEAN}
        (self.state / "high-base.json").write_text(json.dumps(dict(rec, sessionId="stable-sid")))
        (self.state / "high-layer.json").write_text(json.dumps(dict(rec, sessionId="layer-sid", base="stable-sid")))
        (self.state / "high-delta.json").write_text(json.dumps(dict(
            rec, sessionId="delta-sid", layer="layer-sid", base="stable-sid", sealed="2026-09-22T19:30:00")))
        self.touch("high-layer.hit")                                    # the layer's entry, read by the delta's build
        self.touch("high-base.hit")                                     # what the roles fork, read by their forks
        self.started, self.said, self.once, self.errs = [], [], [], []
        self.moved = watchdog.DELTA_MIN + 1000                          # enough has moved for a build, whatever the rule's line
        self.measure, self.whole, self.owed, self.cost = (0.01, 0, 5000), 0.3, 0.0, 700_000.0
        self.patches = [
            patch.object(watchdog, "STATE", str(self.state)), patch.object(v2, "STATE", str(self.state)),
            patch.dict(os.environ, {"ORCH_DELTAS": "high"}),
            patch.object(watchdog, "moved_since_delta", lambda who: self.moved),
            patch.object(watchdog, "carried", lambda who: self.owed),
            patch.object(watchdog, "refresh_cost", lambda who: self.cost),
            patch.object(watchdog, "delta_measure", lambda who: self.measure),
            patch.object(watchdog, "stale_share", lambda who: self.whole),
            patch.object(watchdog.subprocess, "Popen", self.launch),
            patch.object(v2, "log", self.said.append),
            patch.object(v2, "say_once", lambda key, text, **kw: self.once.append(text))]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def touch(self, name, ago=0):
        path = self.state / name
        path.write_text(path.read_text() if path.exists() else "")
        then = time.time() - ago
        os.utime(path, (then, then))

    def launch(self, args, **kw):
        self.started.append(args[2:])
        self.errs.append(getattr(kw.get("stderr"), "name", kw.get("stderr")))

    def test_what_the_builds_it_starts_say_is_kept_where_the_run_is_read(self):
        # the high layer refresh of 2026-09-22 21:36 was started with its stderr on /dev/null: it left a fresh pack,
        # no layer, no session and no reason anywhere, and the run showed only that a refresh had begun
        self.touch("high-layer.hit", ago=45 * 60)                       # due a ping of its own as well
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "warm", "layer", "--if-due"], ["high", "delta"]])
        self.touch("high-layer.looked", ago=watchdog.LAYER_EVERY + 60)
        self.owed = self.cost
        watchdog.layers()
        self.assertEqual(self.started[-1], ["high", "layer"])
        self.assertEqual(len(self.errs), 3)
        for stream in self.errs:
            self.assertTrue(str(stream).endswith("warm.log"), self.errs)

    def test_a_layer_whose_entry_was_missed_holds_no_delta_over_it(self):
        # the high layer's own ping missed at 2026-09-22 21:56 and wrote 593K: a delta built over the layer after
        # that would fork a session whose entry is gone and write the whole prefix again, for a delta nothing reads
        self.touch("high-layer.hit")                                    # read just now, as far as its reads say
        self.touch("high-layer.miss", ago=600)                          # and missed ten minutes ago: it is gone
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("cold", (self.state / "high-layer.refresh").read_text())
        # the layer sealed since answers the miss: its load wrote the entry
        (self.state / "high-layer.refresh").unlink()
        self.touch("high-delta.looked", ago=watchdog.DELTA_EVERY + 60)
        record = json.loads((self.state / "high-layer.json").read_text())
        (self.state / "high-layer.json").write_text(json.dumps(dict(record, sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))))
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])

    def test_a_delta_is_built_when_enough_has_moved_and_not_too_often(self):
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])
        self.assertIn(f"the high delta is rebuilt: about {self.moved:,} tokens moved since 19:30", self.said)
        self.started.clear()
        watchdog.deltas()                                               # within DELTA_EVERY: not looked at again
        self.assertEqual(self.started, [])
        self.touch("high-delta.looked", ago=watchdog.DELTA_EVERY + 60)
        self.moved = watchdog.DELTA_MIN - 1
        watchdog.deltas()                                               # below DELTA_MIN: nothing
        self.assertEqual(self.started, [])

    def test_no_delta_is_built_over_a_build_or_for_a_base_not_switched_to_it(self):
        self.touch("high-layer.building")
        watchdog.deltas()
        self.assertEqual(self.started, [])
        (self.state / "high-layer.building").unlink()
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            watchdog.deltas()
        self.assertEqual(self.started, [])

    def test_a_cold_layer_is_refreshed_instead_of_a_delta_built_over_it(self):
        self.touch("high-layer.hit", ago=2 * 3600)                      # the layer's own entry is cold
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("cold", (self.state / "high-layer.refresh").read_text())
        watchdog.layers()                                               # which the layer's look takes up, saying why
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertIn("the high layer is refreshed: its own cache entry is cold, so a delta over it would write it again",
                      self.said)

    def test_a_delta_asked_for_or_asked_a_question_is_built_or_asked_at_once(self):
        self.touch("high-delta.looked")
        self.moved = 0
        self.touch("high-delta.build")
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):               # by hand, before its base is switched to it
            watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])
        self.assertFalse((self.state / "high-delta.build").exists())
        (self.state / "high-delta.ask").write_text("What does lemma l7 state?")
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            watchdog.deltas()
        self.assertEqual(self.started[-1], ["high", "delta", "--ask", "What does lemma l7 state?"])

    def test_the_layer_under_a_delta_is_refreshed_once_its_delta_has_carried_a_refresh_s_cost(self):
        # rent against purchase (D7): a share of the layer (8%) and a count of theories the frontier would take in (5)
        # asked a refresh 1h24m after the last on 2026-09-22, where the day's costs put it every 3.5 to 5 hours
        self.whole, self.measure = 0.5, (0.3, 0, 90000)                 # a large share alone refreshes nothing now
        self.owed = self.cost - 1
        watchdog.layers()
        self.assertEqual(self.started, [])
        self.touch("high-layer.looked", ago=watchdog.LAYER_EVERY + 60)
        self.owed = self.cost
        watchdog.layers()
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertIn("the high layer is refreshed: its delta has cost the forks that carried it 700K since the layer "
                      "sealed, what a refresh costs (700K)", self.said)
        # the stable reference's drift, which a refresh does not take back, is said to the owner
        self.touch("high-layer.looked", ago=watchdog.LAYER_EVERY + 60)
        self.measure, self.owed = (0.01, watchdog.STABLE_DELTA_MAX, 20000), 0.0
        watchdog.layers()
        self.assertTrue(any("tokens of the stable reference's changes" in t for t in self.once))

    def test_the_layer_under_a_standing_delta_is_pinged_when_due(self):
        # its entry is read by the delta's builds alone; the daemon's own ping waits for its restart (2026-09-22 20:55)
        self.moved, pings = 0, lambda: [a for a in self.started if a[1:2] == ["warm"]]
        for ago, due in ((10 * 60, False), (45 * 60, True), (70 * 60, False)):  # early; due; cold, left alone
            self.started.clear()
            self.touch("high-layer.hit", ago=ago)
            self.touch("high-delta.looked")
            watchdog.deltas()
            self.assertEqual(pings() == [["high", "warm", "layer", "--if-due"]], due, ago)
        self.started.clear()
        self.touch("high-layer.hit", ago=45 * 60)
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):                   # not forked: the daemon pings the layer
            watchdog.deltas()
        self.assertEqual(pings(), [])

    def test_a_fork_that_missed_its_entry_has_it_made_anew(self):
        # three entries were evicted within four minutes on 2026-09-22 (21:04 the high delta, 21:05 the xhigh layer):
        # a fork that missed wrote its own prefix, which no later fork reads, so every fork after it wrote 600K
        self.moved = 0
        self.touch("high-delta.looked")                                 # within DELTA_EVERY, nothing moved
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])
        self.assertFalse((self.state / f"high-{v2.FORK_MISSED}").exists())   # taken, once
        self.started.clear()
        watchdog.deltas()
        self.assertEqual(self.started, [])
        # a delta sealed since the miss holds the entry it missed: not made again for it
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        rec = json.loads((self.state / "high-delta.json").read_text())
        (self.state / "high-delta.json").write_text(json.dumps(dict(rec, sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))))
        watchdog.deltas()
        self.assertEqual(self.started, [])
        # a ping of what the roles fork missed it too: the entry is gone, and the next fork would write 600K before
        # anything made it again (the max layer, pinged twice at 21:23, 486K a ping)
        (self.state / "high-delta.json").write_text(json.dumps(dict(rec, sealed="2026-09-22T19:30:00")))
        (self.state / "high-base.miss").write_text("x\n")
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])
        self.assertTrue((self.state / "high-base.miss").exists())       # the load that makes the entry clears it
        (self.state / "high-base.miss").unlink()
        self.started.clear()
        # a base whose roles fork the layer has its layer refreshed instead
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            watchdog.layers()
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertTrue(any(x.startswith("the high layer is refreshed: a fork missed its entry") for x in self.said),
                        self.said)

    def test_the_stable_part_s_drift_is_the_owner_s_and_refreshes_nothing(self):
        self.measure = (0.01, watchdog.STABLE_DELTA_MAX, 20000)
        watchdog.layers()
        self.assertEqual(self.started, [])
        self.assertTrue(any("restable) is the owner's" in t for t in self.once), self.once)

    def test_a_base_not_switched_to_deltas_keeps_the_whole_file_rule(self):
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            self.whole = 0.25
            watchdog.layers()
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertIn("the high layer is refreshed: 25% of what it holds has changed since it loaded", self.said)


if __name__ == "__main__":
    unittest.main()
