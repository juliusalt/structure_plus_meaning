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

    def test_an_increment_holds_only_what_changed_since_the_chain_s_last_message_and_counts_what_it_supersedes(self):
        # the owner, 2026-09-23: "should the delta not be layered" — each message written once
        state = self.root / "state"
        state.mkdir()
        path = str(self.root / "theories/A.thy")
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "Q7 x"')))
        (state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-2"}))
        (state / "high-delta.json").write_text(json.dumps({"sessionId": "d1", "layer": "layer-2"}))
        stacked = self.held()[path]                                     # l7 as the chain's first message gave it
        (state / "high-delta-held.json").write_text(json.dumps({"top": "d1", "files": {path: stacked}}))
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "R7 x"')
                                                   .replace('lemma l8: "P8 x"', 'lemma l8: "Q8 x"')))
        with patch.object(manifest, "STATE", str(state)):
            entries = manifest.increment_entries("high")
            text = manifest.increment_text("high")[0]
            (a,) = [e for e in entries if e[0].endswith("A.thy")]
            self.assertIn('lemma l7: "R7 x"', a[3])
            self.assertIn('lemma l8: "Q8 x"', a[3])
            self.assertNotIn("Q7", a[3])                                    # its own earlier form is not given again
            self.assertGreater(a[5], 0)                                     # l7's form the chain held is superseded
            self.assertEqual(a[5], int(len(manifest.units(path, stacked)['lemma l7']) / manifest.RATIO[".thy"]))
            self.assertTrue(text.startswith("What you hold has changed since the last message of this kind"))
            (state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-2"}))
            (state / "high-delta.json").write_text(json.dumps({"sessionId": "d1", "layer": "layer-2"}))
            self.assertIn(path, manifest.stack_held("high"))
            (state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-3"}))   # parts refreshed since
            self.assertEqual(manifest.stack_held("high"), {})                            # the chain is orphaned
            (state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-2"}))
            (state / "high-delta.json").write_text(json.dumps({"sessionId": "d2", "layer": "layer-2"}))  # another top
            self.assertEqual(manifest.stack_held("high"), {})

    def test_a_holder_reads_what_changed_since_it_took_the_files_in_and_nothing_it_holds_again(self):
        # the owner, 2026-09-24: "the goal is to not duplicate information and use changes when possible" — a fork told
        # a file changed read it again whole
        state = self.root / "state"
        state.mkdir()
        path = str(self.root / "theories/A.thy")
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "Q7 x"')))
        at_text = self.held()[path]                                     # l7 as the chain's text t1 gave it
        (state / "layer-high-text-1-held.json").write_text(json.dumps({"top": "high-text-1", "files": {path: at_text}}))
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "Q7 x"')
                                                   .replace('lemma l8: "P8 x"', 'lemma l8: "Q8 x"')))
        self.write("docs/N.md", DOC.replace("The second section.", "The second section, rewritten."))
        with patch.object(manifest, "STATE", str(state)):
            since_load = manifest.held_changes("high", "-")
            self.assertIn('lemma l7: "Q7 x"', since_load)                 # a holder of the loads alone lacks both
            self.assertIn('lemma l8: "Q8 x"', since_load)
            self.assertNotIn("lemma l9", since_load)                     # the unchanged units: held, not again
            since_text = manifest.held_changes("high", "high-text-1")
            self.assertIn('lemma l8: "Q8 x"', since_text)
            self.assertNotIn("Q7", since_text)                           # the text it holds gave that already
            only_n = manifest.held_changes("high", "high-text-1", ["N"])  # by name, as its stale line names it
            self.assertIn("rewritten", only_n)
            self.assertNotIn("lemma", only_n)
            self.assertIn("nothing of those", manifest.held_changes("high", "high-text-1", ["S"]))

    def test_a_part_s_old_forms_are_what_it_loaded_that_is_held_anew(self):
        # what a fork carries for nothing once the delta holds the current forms, and a refresh of the part ends
        path = str(self.root / "theories/A.thy")
        with patch.object(manifest, "loaded_parts", lambda who: self.loaded):
            self.assertEqual(manifest.old_forms("high"), {})
            self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l3: "P3 x"', 'lemma l3: "Q3 x"')
                                                       + 'lemma added: "R x"\n  by simp\n\n'))
            was = manifest.units(path, self.loaded["layer"][path])["lemma l3"]
            self.assertEqual(manifest.old_forms("high"), {"layer": int(len(was) / manifest.RATIO[".thy"])})
            self.list.write_text(self.list.read_text().replace("docs/N.md\n", ""))   # no longer held: all of it
            gone = self.loaded["layer"][str(self.root / "docs/N.md")]
            self.assertEqual(manifest.old_forms("high")["layer"], int(len(was) / manifest.RATIO[".thy"])
                             + int(len(gone) / manifest.RATIO[".md"]))

    def test_one_lemma_changed_is_that_lemma_alone_in_its_new_form(self):
        self.write("theories/A.thy", THEORY.format(body=LEMMAS.replace('lemma l7: "P7 x"', 'lemma l7: "Q7 x"')))
        path, part, kind, text, tokens = self.entry("A.thy")
        self.assertEqual((part, kind), ("layer", "changed"))
        self.assertIn('lemma l7: "Q7 x"', text)
        self.assertNotIn("P7", text)                                  # the old form is not repeated
        self.assertNotIn("lemma l8", text)                            # nor any lemma that did not change
        self.assertLess(tokens, manifest.tokens(path) / 10)           # a part of the file, not the file
        whole = manifest.delta_text("high")[0]                         # named by where it is held: no working frontier
        self.assertIn("theories/A.thy (the parts over it)", whole)     # has stood since the named parts (2026-09-23)
        # the delta counted by the part holding each change: the watchdog keeps each part's account by it
        self.write("docs/S.md", "# S\n\nThe stable part, rewritten.\n")
        manifest.delta_text("high")
        parts = manifest.delta_parts("high")
        self.assertEqual(sorted(parts), ["layer", "stable"])
        self.assertTrue(all(v > 0 for v in parts.values()))

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
        self.assertIn("docs/S.md (the stable part)", text)
        self.assertNotIn("working frontier", text)  # there has been none since the named parts (2026-09-23)
        self.assertIn("The reference, amended.", text)
        self.assertEqual(layer, 0)
        self.assertGreater(stable, 0)

    def test_the_stable_part_drifts_too_and_what_it_holds_unlisted_is_counted(self):
        # the owner, 2026-09-23: "base layers also drift but we expect less but that needs to also be available"
        state = self.root / "state"
        state.mkdir()
        s_md = str(self.root / "docs/S.md")
        with patch.object(manifest, "STATE", str(state)):
            self.assertIsNone(manifest.stable_share("high"))                  # no snapshot of a stable base
            (state / "high-manifest.json").write_text(json.dumps({"files": {s_md: manifest.digest(s_md)}}))
            self.assertEqual(manifest.stable_share("high")[:2], (0.0, 0))     # nothing moved
            self.write("docs/S.md", "# Stable\n\nThe reference, amended at some length.\n")
            share, moved, total, unlisted = manifest.stable_share("high")
            self.assertEqual((share, moved, unlisted), (1.0, total, 0))       # its one file moved: whole
            self.loaded["stable"][str(self.root / "docs/Old.md")] = "x" * 305  # loaded, and the list names it no more
            self.assertEqual(manifest.stable_share("high")[3], int(305 / 3.05))

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
        # the canary, which base.sh answers itself, says why the same way
        warm.write_text("")
        out = self.delta("--ask", "What does lemma l7 state?")
        self.assertEqual(out.returncode, 1)
        self.assertIn("no sealed high base with a layer to hold a delta over", out.stderr)
        self.assertRegex(warm.read_text(), r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d no sealed high base with a layer")
        warm.write_text("")
        subprocess.run(f"sh {HERE / 'base.sh'} high delta --ask Q >/dev/null 2>> {warm}", shell=True, env=self.env,
                       timeout=60)
        self.assertEqual(len(warm.read_text().splitlines()), 1, warm.read_text())

    def cut(self, *extra, env=None):
        return self.delta("--text", *extra, env=env)

    def test_texts_are_cut_without_a_session_and_a_session_is_made_of_them_on_demand(self):
        # the owner, 2026-09-24: "write the text on every change, as now, but build the session only when something is
        # about to start from it" — a cut starts nothing; a session holds what the one before it does not
        out = self.cut()
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        self.assertEqual(self.forks(), [])                               # a text, and no session
        first = json.loads((self.state / "high-delta.json").read_text())
        (node,) = first["stack"]
        self.assertNotIn("sessionId", first)
        self.assertEqual((first["top"], node["kind"], first["layer"], first["base"]),
                         (node["id"], "delta", "layer-sid", "stable-sid"))
        self.assertTrue(json.loads((self.state / f"layer-{node['id']}-manifest.json").read_text())["delta"])
        self.assertEqual(json.loads((self.state / "high-delta-held.json").read_text())["top"], node["id"])
        # kept with the text: what a holder of the chain to it holds of each file (v2.py read changes)
        self.assertEqual(json.loads((self.state / f"layer-{node['id']}-held.json").read_text())["top"], node["id"])
        # the session is made when asked for: what changed is cut first, and it holds both texts over the layer
        self.text.write_text("What you hold has changed since the last message of this kind you hold.\n\n"
                             "== theories/A.thy\nlemma l8: Q8\n")
        out = self.delta()
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        ((resumed, name),) = self.forks()
        self.assertEqual(resumed, "layer-sid")
        prompt = next(a for a in reversed(self.calls_made()) if "--bg" in a)[-1]
        self.assertIn("lemma l7", prompt)
        self.assertIn("lemma l8", prompt)
        record = json.loads((self.state / "high-delta.json").read_text())
        self.assertEqual([n["kind"] for n in record["stack"]], ["delta", "increment"])
        self.assertEqual(record["tokens"], first["tokens"] + record["stack"][1]["tokens"])
        self.assertEqual((record["sessionId"], record["session_len"], record["stack"][1]["sessionId"]),
                         ("fork-" + name, 2, "fork-" + name))
        self.assertIn(f"HELD {record['stack'][1]['digest']}", prompt)   # the top text's digest
        self.assertTrue(json.loads((self.state / f"layer-fork-{name}-manifest.json").read_text())["delta"])
        # the next session forks this one, warm, and holds the new text alone
        self.text.write_text("What you hold has changed since the last message of this kind you hold.\n\n"
                             "== theories/A.thy\nlemma l9: Q9\n")
        time.sleep(1.1)                                                 # a session is named by its second
        self.assertEqual(self.delta().returncode, 0)
        resumed, later = self.forks()[-1]
        self.assertEqual(resumed, "fork-" + name)
        prompt = next(a for a in reversed(self.calls_made()) if "--bg" in a)[-1]
        self.assertIn("lemma l9", prompt)
        self.assertNotIn("lemma l7", prompt)
        record = json.loads((self.state / "high-delta.json").read_text())
        self.assertEqual((record["sessionId"], record["session_len"], len(record["stack"])), ("fork-" + later, 3, 3))
        self.assertIn(["stop", "id-" + name], self.calls_made())        # replaced: stopped, never removed
        # every text cut and every session made, with its kind: one over the layer writes every text again
        builds = [json.loads(x) for x in (self.state / "high-delta-builds.jsonl").read_text().splitlines()]
        self.assertEqual([b["kind"] for b in builds],
                         ["text-delta", "text-increment", "session-whole", "text-increment", "session"])
        # begun anew as one whole text: no session until one is made for it, and the roles fork the layer meanwhile
        self.assertEqual(self.cut("--whole").returncode, 0)
        record = json.loads((self.state / "high-delta.json").read_text())
        self.assertEqual((len(record["stack"]), record["stack"][0]["kind"]), (1, "delta"))
        self.assertNotIn("sessionId", record)

    def test_a_session_is_made_over_the_layer_when_the_one_standing_is_cold(self):
        self.assertEqual(self.delta().returncode, 0)
        ((_, name),) = self.forks()
        then = time.time() - 2 * 3600                                   # its entry gone cold since
        os.utime(self.state / "high-base.hit", (then, then))
        time.sleep(1.1)
        self.assertEqual(self.delta().returncode, 0)
        resumed, _ = self.forks()[-1]
        self.assertEqual(resumed, "layer-sid")                          # a fork of it would write its whole prefix
        record = json.loads((self.state / "high-delta.json").read_text())
        self.assertEqual(record["session_len"], len(record["stack"]))  # every text again, over the layer

    def test_no_text_is_cut_while_a_build_holds_the_chain(self):
        (self.state / "high-layer.building").write_text(str(os.getpid()))   # a build that is running
        out = self.cut()
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertFalse((self.state / "high-delta.json").exists())     # its end would orphan it: cut after

    def test_a_session_that_holds_its_chain_to_its_top_is_not_made_again(self):
        empty = self.text.with_name("empty.md")
        empty.write_text("")
        self.assertEqual(self.delta().returncode, 0)
        before = len(self.forks())
        out = self.delta(env={"BASE_DELTA_TEXT": str(empty)})            # nothing changed since
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("holds its chain to its top", out.stdout)
        self.assertEqual(len(self.forks()), before)

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
        self.assertNotIn("sessionId", json.loads((self.state / "high-delta.json").read_text()))  # its text stands
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
        (self.state / "high-layer.building").write_text(str(os.getpid()))   # a build that is running
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
                    "fix-4": dict(origin="high", started=after, sid="d"),                        # forked no delta
                    "layer-fixer": dict(origin="high", role="role-layer", started=after, sid="e"),   # a role layer
                    "fix-5": dict(origin="layer-fixer", started=after, delta_tokens=5000, sid="f"),  # its fork: carries it
                    "churn-fixer": dict(origin="layer-fixer", role="role-churn", started=after, delta_tokens=3000,
                                        sid="g")}                                   # a role's churn: wrote it once
        (self.state / "v2.json").write_text(json.dumps({"sessions": sessions, "tasks": {}, "queue": [], "events": []}))
        (self.state / "warm.log").write_text(
            "2026-09-22T22:36:26 delta high: OK   session fork 00bbf073 of base bf471854: first own request "
            "cache_read=601539 cache_write=6451 uncached=2 (98% read)\n"
            "2026-09-22T21:15:09 delta high: OK   session fork 72dc01e5 of base e3a1676c: first own request "
            "cache_read=600393 cache_write=4000 uncached=2 (99% read)\n"                   # before the layer sealed
            "2026-09-22T22:40:00 delta xhigh: OK   session fork 11111111 of base 22222222: first own request "
            "cache_read=500000 cache_write=9000 uncached=2 (99% read)\n")
        with patch.object(watchdog, "own_requests", lambda s: 30):  # not 20: 0.1 × 20 would equal a write's 2
            self.assertAlmostEqual(watchdog.carried("high"), 2 * 0.1 * 5000 * 30 + 2 * 6451 + 2 * 3000)

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
        # and the role layers standing on it, which a refresh builds again (role_layer_due)
        (self.state / "v2.json").write_text(json.dumps({"sessions": {
            "layer-fixer": {"role": "role-layer", "origin": "high:layer", "layer_state": "sealed", "build_cost": 210_000,
                            "flags": " ".join(v2.session_flags())}}, "tasks": {}, "queue": [], "events": [],
            "role_layers": {"fixer": {"name": "layer-fixer"}}}))
        (self.state / "hits").mkdir()
        (self.state / "hits" / "layer-fixer").write_text("")                  # warm: it serves
        with patch.dict(os.environ, {"ORCH_ROLE_LAYERS": "fixer"}):
            self.assertAlmostEqual(watchdog.refresh_cost("high"), 2 * (601_541 - 276_298) + 0.1 * 276_298 + 210_000)
        (self.state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-sid"}))
        self.assertIsNone(watchdog.refresh_cost("high"))


class ChainScheduleTests(unittest.TestCase):
    """Each part of a chain on its own schedule (the owner, 2026-09-23: "the layers must be ordered by churn and
    dependency and so update schedules also should differ"; "sometimes consolidation for the lower parts rather than
    carrying their changes in a higher layer"): each part's account of what carrying its changes has cost since it
    loaded, and the lowest part whose account, with those over it, has paid for loading them again."""

    T0, T1, T2 = "2026-09-23T10:00:00", "2026-09-23T12:00:00", "2026-09-23T14:00:00"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.state = Path(self.temp.name)
        at = lambda s: time.mktime(time.strptime(s, "%Y-%m-%dT%H:%M:%S"))
        self.t0, self.t1, self.t2 = at(self.T0), at(self.T1), at(self.T2)
        (self.state / "high-base.json").write_text(json.dumps({"sessionId": "stable-sid", "context": 100_000,
                                                               "sealed": self.T0}))
        parts = [{"part": "stable", "sessionId": "stable-sid", "context": 100_000, "sealed": self.T0},
                 {"part": "reasoning", "kind": "reasoning", "sessionId": "r", "parent": "stable-sid", "context": 120_000,
                  "sealed": self.T0},
                 {"part": "direction", "kind": "material", "sessionId": "d", "parent": "r", "context": 150_000,
                  "sealed": self.T1},
                 {"part": "inventory", "kind": "material", "sessionId": "i", "parent": "d", "context": 230_000,
                  "sealed": self.T1},
                 {"part": "catalogue", "kind": "material", "sessionId": "c", "parent": "i", "context": 300_000,
                  "sealed": self.T2}]
        (self.state / "high-layer.json").write_text(json.dumps({"sessionId": "c", "base": "stable-sid",
                                                                "context": 300_000, "sealed": self.T2, "parts": parts}))
        self.patches = [patch.object(watchdog, "STATE", str(self.state)), patch.object(v2, "STATE", str(self.state)),
                        patch.object(v2, "role_layers", lambda: [])]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def test_each_part_s_account_is_what_its_old_forms_and_whole_rewrites_cost_since_it_loaded(self):
        # the arithmetic review of 2026-09-23 (C): a refresh does not end the carrying of a part's changes — their
        # current forms move from the delta into the part — only of the part's own superseded old forms, and the
        # writing of its changes again at each whole rewrite of the chain
        sessions = {"a": dict(origin="high", started=self.t2 + 60, sid="a", delta_tokens=9000,
                              old_forms={"direction": 300, "catalogue": 1000}),
                    "b": dict(origin="high", started=self.t1 + 60, sid="b", old_forms={"direction": 500}),
                    # before the catalogue loaded: the direction's alone counts
                    "c": dict(origin="high", started=self.t0 + 60, sid="c", old_forms={"direction": 500}),
                    # before the direction loaded: nobody's now
                    "d": dict(origin="high", started=self.t2 + 60, sid="d", delta_tokens=1000),
                    # it carries changes, and no old forms: nothing a refresh would spare
                    "layer-x": dict(origin="high:layer", role="role-layer", started=self.t2, sid="x"),
                    "churn-x": dict(origin="layer-x", role="role-churn", started=self.t2 + 60, sid="g",
                                    whole_parts={"catalogue": 700}),                  # built whole: it wrote them again
                    "churn-y": dict(origin="churn-x", role="role-churn", started=self.t2 + 90, sid="h")}  # grown
        (self.state / "v2.json").write_text(json.dumps({"sessions": sessions, "tasks": {}, "queue": [], "events": []}))
        (self.state / "high-delta-builds.jsonl").write_text(
            json.dumps({"at": "2026-09-23T14:30:00", "kind": "delta", "parts": {"catalogue": 400, "direction": 100}})
            + "\n" + json.dumps({"at": "2026-09-23T14:40:00", "kind": "increment", "parts": {"catalogue": 999}}) + "\n"
            + json.dumps({"at": "2026-09-23T11:00:00", "kind": "delta", "parts": {"catalogue": 50}}) + "\n")
        with patch.object(watchdog, "own_requests", lambda s: 50):
            owed = watchdog.carried_parts("high")
        self.assertAlmostEqual(owed["direction"], 0.1 * 300 * 50 + 0.1 * 500 * 50 + 2 * 100)
        self.assertAlmostEqual(owed["catalogue"], 0.1 * 1000 * 50 + 2 * 700 + 2 * 400)   # not the increment's
        self.assertEqual((owed["inventory"], owed["stable"]), (0.0, 0.0))

    def test_the_part_whose_accounts_most_exceed_its_refresh_is_refreshed_and_the_parts_under_it_keep_carrying(self):
        # suffix costs over the fixture's chain: from the catalogue 2 × 70K + 0.1 × 230K, the inventory 2 × 150K +
        # 0.1 × 150K, the direction 2 × 180K + 0.1 × 120K, the stable part 2 × 300K
        catalogue, direction, stable = 163_000.0, 372_000.0, 600_000.0
        owed = {"stable": 0.0, "direction": 10_000.0, "inventory": 0.0, "catalogue": catalogue}
        with patch.object(watchdog, "carried_parts", lambda who: owed):
            self.assertEqual(watchdog.refresh_plan("high"), ("catalogue", catalogue, catalogue))
            # the arithmetic review of 2026-09-23 (D): a large account higher up pays for a refresh from lower parts
            # too, but a lower part is loaded again only where its own account covers what it adds
            owed.update(direction=0.0, catalogue=500_000.0)
            self.assertEqual(watchdog.refresh_plan("high"), ("catalogue", 500_000.0, catalogue))
            owed.update(direction=250_000.0)                     # its own changes cover what it adds (209K)
            self.assertEqual(watchdog.refresh_plan("high"), ("direction", 750_000.0, direction))
            owed.update(direction=0.0, catalogue=0.0, stable=2 * 300_000 + 100_000)
            self.assertEqual(watchdog.refresh_plan("high"), ("stable", 700_000.0, stable))   # one candidate among them
            owed.update(stable=1.0, catalogue=1.0)
            self.assertIsNone(watchdog.refresh_plan("high"))

class DeltaChainRuleTests(unittest.TestCase):
    """The delta as a chain of messages each written once (the owner, 2026-09-23: "should the delta not be layered";
    "the 4k number needs to somehow depend on the size of the delta"): what the pending changes have cost the forks
    against a message holding them, and what the chain's superseded forms have cost against writing it anew."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.state = Path(self.temp.name)
        self.sealed = "2026-09-23T12:00:00"
        self.t = time.mktime(time.strptime(self.sealed, "%Y-%m-%dT%H:%M:%S"))
        (self.state / "high-base.json").write_text(json.dumps({"sessionId": "stable-sid", "context": 300_000}))
        (self.state / "high-layer.json").write_text(json.dumps({"sessionId": "layer-sid", "base": "stable-sid",
                                                                "context": 400_000, "sealed": "2026-09-23T10:00:00"}))
        self.patches = [patch.object(watchdog, "STATE", str(self.state)), patch.object(v2, "STATE", str(self.state))]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def sessions(self, **sessions):
        (self.state / "v2.json").write_text(json.dumps({"sessions": sessions, "tasks": {}, "queue": [], "events": []}))

    def test_what_is_pending_has_cost_each_fork_since_the_last_message_its_write(self):
        top = {"sessionId": "d2", "context": 450_000, "sealed": self.sealed, "layer": "layer-sid", "base": "stable-sid",
               "top": "t2", "session_len": 1, "stack": [{"id": "t1", "sessionId": "d2"}, {"id": "t2", "tokens": 1000}]}
        (self.state / "high-delta.json").write_text(json.dumps(top))
        self.sessions(a=dict(origin="high", started=self.t + 60, pending_tokens=3000, sid="a"),
                      b=dict(origin="high", started=self.t - 60, pending_tokens=3000, sid="b"),   # before the session
                      c=dict(origin="high", started=self.t + 90, sid="c"))                        # nothing pending
        with patch.dict(os.environ, {"ORCH_DELTAS": "high"}), patch.object(watchdog, "own_requests", lambda s: 20):
            (self.state / "high-base.hit").write_text("")               # the session standing, warm: made over it
            owed, cost = watchdog.pending_paid("high", top, 3000)
            # its write alone: carried after, a change costs the same in the fork's context and in the session's
            # prefix (the arithmetic review of 2026-09-23, A)
            self.assertAlmostEqual(owed, 3000 * 2)
            self.assertAlmostEqual(cost, 2 * 3000 + 0.1 * 450_000)      # a larger prefix asks more to be lacked
            os.utime(self.state / "high-base.hit", (0, 0))              # gone cold: made over the layer
            self.assertAlmostEqual(watchdog.pending_paid("high", top, 3000)[1], 2 * 3000 + 0.1 * 400_000)
            (self.state / "high-delta.json").unlink()
            _, over_the_layer = watchdog.pending_paid("high", None, 3000)
            self.assertAlmostEqual(over_the_layer, 2 * 3000 + 0.1 * 400_000)

    def test_the_knowledge_base_is_built_again_for_max_s_parts_alone(self):
        # the owner, 2026-09-24: "the knowledge base is rebuilt on every max session make this lzay too" — it takes the
        # texts in by integration (v2.kb_texts): a session of max's delta costs nothing of it, the chain begun anew its
        # taking the whole text, a refresh of max's parts its build
        (self.state / "max-base.json").write_text(json.dumps({"sessionId": "max-stable", "context": 300_000}))
        (self.state / "max-layer.json").write_text(json.dumps({"sessionId": "max-layer", "base": "max-stable",
                                                               "context": 500_000, "sealed": "2026-09-23T10:00:00"}))
        self.sessions(**{"kb-1": dict(role="kb", origin="max", kb_state="sealed", build_cost=150_000, sid="k",
                                      context=560_000, stack_len=2, stack_base="t1")})
        state = json.loads((self.state / "v2.json").read_text())
        (self.state / "v2.json").write_text(json.dumps(dict(state, kb="kb-1")))
        top = {"sessionId": "d2", "context": 520_000, "sealed": self.sealed, "tokens": 20_000, "superseded": 2000,
               "stack": [{"id": "t1", "sealed": self.sealed}, {"id": "t2", "sessionId": "d2"}]}
        with patch.object(v2, "role_layers", lambda: []):
            self.assertAlmostEqual(watchdog.pending_paid("max", top, 1000)[1], 2 * 1000 + 0.1 * 500_000)
            # begun anew: the knowledge base takes the whole text over itself, and the chain's session over the layer
            self.assertAlmostEqual(watchdog.stack_waste("max", top)[1],
                                   (2 * 18_000 + 0.1 * 560_000) + (2 * 18_000 + 0.1 * 500_000))
            self.assertAlmostEqual(watchdog.refresh_cost("max"), 2 * (500_000 - 300_000) + 0.1 * 300_000 + 150_000)
            self.assertAlmostEqual(watchdog.pending_paid("high", None, 1000)[1], 2 * 1000 + 0.1 * 400_000)  # not high's
            # and a refresh of max's parts, from its top part, the knowledge base with the role layers
            parts = [{"part": "stable", "sessionId": "max-stable", "context": 300_000},
                     {"part": "direction", "kind": "material", "sessionId": "md", "parent": "max-stable", "context": 400_000},
                     {"part": "catalogue", "kind": "material", "sessionId": "mc", "parent": "md", "context": 500_000}]
            (self.state / "max-layer.json").write_text(json.dumps({"sessionId": "mc", "base": "max-stable",
                                                                   "context": 500_000, "parts": parts}))
            with patch.object(watchdog, "carried_parts", lambda who: {"catalogue": 10_000_000.0}):
                self.assertEqual(watchdog.refresh_plan("max")[2], 2 * 100_000 + 0.1 * 400_000 + 150_000)

    def test_the_chain_s_superseded_forms_are_weighed_against_writing_it_anew(self):
        top = {"sessionId": "d3", "tokens": 30_000, "superseded": 4000,
               "stack": [{"sessionId": "d1", "sealed": self.sealed}, {"sessionId": "d2"}, {"sessionId": "d3"}]}
        self.sessions(a=dict(origin="high", started=self.t + 60, superseded_tokens=4000, sid="a"),
                      b=dict(origin="high", started=self.t - 60, superseded_tokens=4000, sid="b"))
        with patch.object(watchdog, "own_requests", lambda s: 50):
            owed, cost = watchdog.stack_waste("high", top)
        self.assertAlmostEqual(owed, 0.1 * 4000 * 50)
        self.assertAlmostEqual(cost, 2 * (30_000 - 4000) + 0.1 * 400_000)
        self.assertEqual(watchdog.stack_waste("high", dict(top, stack=top["stack"][:1])), (0.0, 0.0))  # one message


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
        # and whose changes it carries, by part: each part's account is its own (watchdog.carried_parts)
        rec = json.loads((self.w.state / "high-delta.json").read_text())
        (self.w.state / "high-delta.json").write_text(json.dumps(dict(rec, parts={"direction": 300, "catalogue": 900})))
        shares = start.replace("'7'", "'9'").replace("-7", "-9").replace("task 7", "task 9").replace(
            "get('delta_tokens')", "get('delta_shares')")
        self.assertEqual(self.py(shares), "{'direction': 0.25, 'catalogue': 0.75}")
        (self.w.state / "high-delta.json").write_text(json.dumps(dict(json.loads((self.w.state / "high-delta.json")
                                                                                .read_text()), superseded=120)))
        (self.w.state / "high-delta-pending.json").write_text(json.dumps({"top": "delta-sid", "tokens": 700}))
        both = start.replace("'7'", "'10'").replace("-7", "-10").replace("task 7", "task 10").replace(
            "get('delta_tokens')", "get('pending_tokens'), v2.peek()['sessions'][n].get('superseded_tokens')")
        self.assertEqual(self.py(both), "700 120")

    def test_only_a_fork_of_the_base_itself_awaits_its_session_and_every_session_standing_on_it_uses_it(self):
        # the owner, 2026-09-24: sessions only when something is about to start from them — the knowledge base, the
        # roles' reasoning layers and churns take the texts in themselves, and a session relieves none of them
        sessions = {"kb-1": {"role": "kb", "origin": "max"},
                    "layer-reviewer": {"role": "role-layer", "layer_of": "reviewer", "origin": "xhigh"},
                    "layer-implementer": {"role": "role-layer", "layer_of": "implementer", "origin": "high:layer"},
                    "churn-implementer": {"role": "role-churn", "origin": "layer-implementer"}}
        forks = [("high", "designer"), ("high:layer", "implementer"), ("xhigh", "role-layer"), ("max", "kb"),
                 ("kb-1", "planner"), ("churn-implementer", "implementer"), ("high:stable", "base-reasoning"),
                 ("high:catalogue", None), ("nobody", None)]
        self.assertEqual([v2.top_rider(o, sessions, r) for o, r in forks],
                         ["high", "high", None, None, None, None, None, None, None])
        # the base is in use while any session standing on it starts (warm_daemon.sh's idle rule)
        self.assertEqual([v2.stands_on(o, sessions) for o in ("high", "kb-1", "layer-reviewer", "layer-implementer",
                                                               "churn-implementer", "nobody")],
                         ["high", "max", "xhigh", "high", "high", None])

    def test_a_session_standing_on_a_base_is_a_use_of_it_whatever_it_forks(self):
        # the simulation of 09-21/22: planners reach max through the knowledge base alone, max counted as unused, its
        # pings stopped after twelve hours (warm_daemon.sh), and its whole chain was built again for the next message
        self.w.session("kb-1", "kb", "kb-sid", origin="max")
        used = self.w.state / "max-base.used"
        self.assertFalse(used.exists())
        self.py("v2.launch('planner', '1', lambda n: 'You are plan-1.', tree=None, origin='kb-1')")
        self.assertTrue(used.exists())
        self.assertLess(time.time() - used.stat().st_mtime, 60)

    def test_a_fork_of_any_session_carrying_the_delta_carries_it_and_awaits_what_is_pending(self):
        self.w.session("kb-1", "kb", "kb-sid", origin="high", delta_tokens=5000, delta_shares={"catalogue": 1.0},
                       superseded_tokens=10)
        for name, context in (("high-layer.json", 601_541), ("high-delta.json", 607_992)):
            rec = json.loads((self.w.state / name).read_text())
            (self.w.state / name).write_text(json.dumps(dict(rec, context=context)))
        (self.w.state / "deltas").write_text("high\n")
        child = ("n = v2.launch('implementer', '13', lambda n: 'You are implement-13, working on task 13.', tree=None, "
                 "origin='kb-1')\ns = v2.peek()['sessions'][n]\n"
                 "print(s.get('delta_tokens'), s.get('delta_shares'), s.get('superseded_tokens'))")
        self.assertEqual(self.py(child), "5000 {'catalogue': 1.0} 10")    # a planner of the knowledge base, say

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
        for sid in ("delta-sid", "delta-old", "delta-first", "delta-mid"):
            (self.w.state / f"layer-{sid}-manifest.json").write_text(json.dumps({"taken": "t", "delta": True, "files": {}}))
        self.standing.write_text("the standing delta")
        old = self.w.state / "high-delta-20260922T120000.md"
        old.write_text("an older delta")
        gone = self.py("print(sorted(v2.tidied()))")                   # a delta recorded as one message, no chain
        self.assertNotIn("layer-delta-sid-manifest.json", gone)        # the delta standing, whether forked or not
        self.assertIn("layer-delta-first-manifest.json", gone)         # no message of anything standing
        (self.w.state / "tidied").unlink()                             # the sweep's own pace: at most hourly
        # the chain's first message: a churn built whole reads every message of the chain
        first = self.w.state / "high-delta-20260922T150000.md"
        first.write_text("the chain's first message")
        for sid in ("delta-first", "delta-mid", "delta-old"):
            (self.w.state / f"layer-{sid}-manifest.json").write_text(json.dumps({"taken": "t", "delta": True, "files": {}}))
        rec = json.loads((self.w.state / "high-delta.json").read_text())
        rec["stack"] = [{"sessionId": "delta-first", "text": str(first)},
                        {"sessionId": "delta-sid", "text": str(self.standing)}]
        (self.w.state / "high-delta.json").write_text(json.dumps(rec))
        # a judging role's layer that reasoned over a message no longer of the chain (a test's state: its forks are
        # told what changed since it, while it stands)
        st = self.w.st() or {}
        self.w.set_st(sessions=dict(st.get("sessions") or {}, **{"layer-reviewer": dict(
            role="role-layer", layer_of="reviewer", layer_state="sealed", origin="high", origin_sid="delta-mid",
            state="done")}))
        for path in (self.standing, old, first):
            then = os.path.getmtime(path) - 5 * 3600
            os.utime(path, (then, then))
        gone = self.py("print(sorted(v2.tidied()))")
        self.assertIn("layer-delta-old-manifest.json", gone)
        self.assertNotIn("layer-delta-sid-manifest.json", gone)        # the delta standing, whether forked or not
        self.assertIn("high-delta-20260922T120000.md", gone)
        self.assertNotIn(self.standing.name, gone)                     # the next build reads it
        self.assertNotIn(first.name, gone)                             # and every message of its chain
        self.assertNotIn("layer-delta-first-manifest.json", gone)      # whose snapshots a judging layer's forks read
        self.assertNotIn("layer-delta-mid-manifest.json", gone)        # the message a standing layer forked
        # a chain of texts: each text's snapshot stays with it, what a holder of the chain to it is told from
        (self.w.state / "tidied").unlink()
        (self.w.state / "layer-high-text-1-manifest.json").write_text(json.dumps({"taken": "t", "delta": True, "files": {}}))
        rec["stack"] = [{"id": "high-text-1", "text": str(first)}, {"id": "high-text-2", "text": str(self.standing)}]
        (self.w.state / "high-delta.json").write_text(json.dumps(rec))
        gone = self.py("print(sorted(v2.tidied()))")
        self.assertNotIn("layer-high-text-1-manifest.json", gone)

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
        self.started, self.said, self.once, self.errs, self.cuts = [], [], [], [], []
        # what is pending since the delta's last message, what that has cost the forks against a message holding it,
        # and what the chain's superseded forms have cost against writing it anew (the rules' own tests are apart)
        self.pending, self.paid, self.waste = 5000, (1.0, 1.0), (0.0, 0.0)
        self.measure, self.whole, self.owed, self.cost = (0.01, 0, 5000), 0.3, 0.0, 700_000.0
        self.patches = [
            patch.object(watchdog, "STATE", str(self.state)), patch.object(v2, "STATE", str(self.state)),
            patch.dict(os.environ, {"ORCH_DELTAS": "high"}),
            patch.object(watchdog, "pending_tokens", lambda who: self.pending),
            patch.object(watchdog, "pending_paid", lambda who, top, pending: self.paid),
            patch.object(watchdog, "stack_waste", lambda who, top: self.waste),
            patch.object(watchdog, "carried", lambda who: self.owed),
            patch.object(watchdog, "refresh_cost", lambda who: self.cost),
            patch.object(watchdog, "delta_measure", lambda who: self.measure),
            patch.object(watchdog, "stale_share", lambda who: self.whole),
            patch.object(watchdog.subprocess, "Popen", self.launch),
            patch.object(watchdog, "cut_text", lambda who, whole=False: self.cuts.append((who, whole))),
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

    def texts_only(self):
        """The chain as texts with no session made of them: the roles fork the layer."""
        rec = json.loads((self.state / "high-delta.json").read_text())
        rec.pop("sessionId")
        (self.state / "high-delta.json").write_text(json.dumps(dict(
            rec, top="high-text-1", stack=[{"id": "high-text-1", "digest": "t1", "tokens": 5000}])))

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

    def test_a_chain_s_layer_entry_is_its_top_part_read_under_its_own_marks(self):
        # the simulation of the run of 09-21/22: with every role of high on a layer of its own nothing forked the base,
        # its mark aged while the top part's pings answered, and the layer was refreshed as cold with its stable base
        (self.state / "high-delta.json").unlink()
        rec = json.loads((self.state / "high-layer.json").read_text())
        rec["parts"] = [{"part": "stable", "sessionId": "stable-sid"},
                        {"part": "catalogue", "kind": "material", "sessionId": "layer-sid", "parent": "stable-sid"}]
        (self.state / "high-layer.json").write_text(json.dumps(rec))
        self.touch("high-base.hit", ago=2 * v2.WARM_MAX)                    # nothing forks the base itself
        self.assertGreaterEqual(watchdog.layer_entry_age("high"), 2 * v2.WARM_MAX - 5)
        (self.state / "high-catalogue.hit").write_text("layer-sid")
        self.touch("high-catalogue.hit", ago=600)                          # the top part's ping, ten minutes ago
        self.assertLess(watchdog.layer_entry_age("high"), 700)
        (self.state / "high-catalogue.hit").write_text("another-sid")      # a mark of another session's
        self.touch("high-catalogue.hit", ago=600)
        self.assertGreaterEqual(watchdog.layer_entry_age("high"), 2 * v2.WARM_MAX - 5)
        (self.state / "entry-hits").mkdir()
        self.touch("entry-hits/layer-sid", ago=300)                         # its own mark, a fork's read
        self.assertLess(watchdog.layer_entry_age("high"), 400)

    def test_a_layer_whose_entry_was_missed_holds_no_delta_over_it(self):
        # the high layer's own ping missed at 2026-09-22 21:56 and wrote 593K: a delta built over the layer after
        # that would fork a session whose entry is gone and write the whole prefix again, for a delta nothing reads
        self.touch("high-delta.build")                                  # asked for: a session over the layer
        self.touch("high-layer.hit")                                    # read just now, as far as its reads say
        self.touch("high-layer.miss", ago=600)                          # and missed ten minutes ago: it is gone
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("cold", (self.state / "high-layer.refresh").read_text())
        # the layer sealed since answers the miss: its load wrote the entry
        (self.state / "high-layer.refresh").unlink()
        record = json.loads((self.state / "high-layer.json").read_text())
        (self.state / "high-layer.json").write_text(json.dumps(dict(record, sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))))
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta", "--whole"]])
        # with texts alone the roles fork the layer: its reads and its miss are the base's marks, and the miss is a
        # fork's, which has the layer refreshed
        self.started.clear()
        self.texts_only()
        (self.state / "high-layer.json").write_text(json.dumps(record))       # sealed long before the miss
        self.touch("high-base.miss", ago=600)
        self.touch("high-delta.looked", ago=watchdog.DELTA_EVERY + 60)
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("missed its entry", (self.state / "high-layer.refresh").read_text())

    def test_a_delta_message_is_built_once_what_is_pending_has_paid_for_it_and_not_measured_too_often(self):
        watchdog.deltas()                                               # its session holds the chain; 5,000 uncut
        self.assertEqual(self.started, [["high", "delta"]])
        self.assertTrue(any("the high delta's session is made: what the forks of the base lacked of 5,000 tokens" in x
                            for x in self.said), self.said)
        self.started.clear()
        watchdog.deltas()                                               # within DELTA_EVERY: not measured again
        self.assertEqual(self.started, [])
        self.touch("high-delta.looked", ago=watchdog.DELTA_EVERY + 60)
        self.paid = (0.9, 1.0)                                          # not yet paid for: nothing
        watchdog.deltas()
        self.assertEqual(self.started, [])
        pending = json.loads((self.state / "high-delta-pending.json").read_text())
        self.assertEqual((pending["top"], pending["tokens"]), ("delta-sid", 5000))   # what forks record meanwhile

    def test_the_chain_s_session_is_made_by_its_rule_and_the_chain_begun_anew_as_one_text_by_its_own(self):
        rec = json.loads((self.state / "high-delta.json").read_text())
        (self.state / "high-delta.json").write_text(json.dumps(dict(
            rec, top="high-text-2", superseded=500, session_len=1,
            stack=[{"id": "high-text-1", "sessionId": "delta-sid", "tokens": 4000},
                   {"id": "high-text-2", "tokens": 1000, "superseded": 500}])))
        (self.state / "high-delta-held.json").write_text(json.dumps({"top": "high-text-2", "files": {}}))
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta"]])             # over its session: the texts after it
        self.assertTrue(any("session is made" in x for x in self.said), self.said)
        self.assertEqual(self.cuts, [])                                 # the session's build cuts what it takes
        self.started.clear()
        self.touch("high-delta.looked", ago=watchdog.DELTA_EVERY + 60)
        self.pending, self.waste = 0, (3.0, 2.0)                       # nothing uncut, and the chain's waste paid
        watchdog.deltas()
        self.assertEqual(self.started, [])                              # a cut, local: no session for it
        self.assertEqual(self.cuts, [("high", True)])
        self.assertTrue(any("its superseded forms have cost its holders" in x for x in self.said), self.said)

    def test_no_delta_is_built_over_a_build_or_for_a_base_not_switched_to_it(self):
        self.touch("high-layer.building")
        watchdog.deltas()
        self.assertEqual(self.started, [])
        (self.state / "high-layer.building").unlink()
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            watchdog.deltas()
        self.assertEqual(self.started, [])

    def test_a_cold_layer_is_refreshed_instead_of_a_delta_built_over_it(self):
        self.texts_only()                                               # the session would be made over the layer
        self.touch("high-layer.hit", ago=2 * 3600)
        self.touch("high-base.hit", ago=2 * 3600)                       # which the roles fork: its reads marked there                      # the layer's own entry is cold
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("cold", (self.state / "high-layer.refresh").read_text())
        watchdog.layers()                                               # which the layer's look takes up, saying why
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertIn("the high layer is refreshed: its own cache entry is cold, so a delta over it would write it again",
                      self.said)

    def test_a_delta_asked_for_or_asked_a_question_is_built_or_asked_at_once(self):
        self.touch("high-delta.looked")
        self.pending = 0
        self.touch("high-delta.build")
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):               # by hand, before its base is switched to it
            watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta", "--whole"]])  # the chain one text, and a session of it
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
        self.pending, pings = 0, lambda: [a for a in self.started if a[1:2] == ["warm"]]
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

    def test_a_fork_s_miss_is_marked_on_the_base_it_forked(self):
        # cache_check is what marks it: the test below writes the mark itself, and a mutation of the marking passed
        # the whole mutation check (2026-09-23)
        said = lambda v: subprocess.CompletedProcess([], 0, v, "")
        sessions = {"sessions": {"implement-9": {"origin": "high"}, "ask-q1": {"origin": "kb-1"}}}
        with patch.object(v2, "peek", lambda: sessions):
            with patch.object(v2.subprocess, "run", lambda *a, **k: said("OK first own request read 500000 (written 300)")):
                v2.cache_check("sid", "base-sid", "implement-9")
            self.assertFalse((self.state / f"high-{v2.FORK_MISSED}").exists())         # a read: nothing to mark
            with patch.object(v2.subprocess, "run", lambda *a, **k: said("MISS first own request read 0 (written 500000)")):
                v2.cache_check("sid", "base-sid", "implement-9")
                v2.cache_check("sid", "kb-sid", "ask-q1")                               # a session's fork: no base's
        self.assertTrue((self.state / f"high-{v2.FORK_MISSED}").exists())
        self.assertFalse((self.state / f"kb-1-{v2.FORK_MISSED}").exists())

    def test_a_fork_that_missed_its_entry_has_it_made_anew(self):
        # three entries were evicted within four minutes on 2026-09-22 (21:04 the high delta, 21:05 the xhigh layer):
        # a fork that missed wrote its own prefix, which no later fork reads, so every fork after it wrote 600K
        self.pending = 0
        self.touch("high-delta.looked")                                 # within DELTA_EVERY, nothing moved
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        watchdog.deltas()
        self.assertEqual(self.started, [["high", "delta", "--over-layer"]])  # its session made again, over the layer
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
        self.assertEqual(self.started, [["high", "delta", "--over-layer"]])
        self.assertTrue((self.state / "high-base.miss").exists())       # the load that makes the entry clears it
        (self.state / "high-base.miss").unlink()
        self.started.clear()
        # texts with no session made of them: the roles fork the layer, whose entry the fork missed
        self.texts_only()
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        watchdog.deltas()
        self.assertEqual(self.started, [])
        self.assertIn("a fork missed its entry", (self.state / "high-layer.refresh").read_text())
        (self.state / "high-layer.refresh").unlink()
        # a base whose roles fork the layer has its layer refreshed instead
        (self.state / f"high-{v2.FORK_MISSED}").write_text(str(time.time()))
        with patch.dict(os.environ, {"ORCH_DELTAS": ""}):
            watchdog.layers()
        self.assertEqual(self.started, [["high", "layer"]])
        self.assertTrue(any(x.startswith("the high layer is refreshed: a fork missed its entry") for x in self.said),
                        self.said)

    def test_a_chain_refreshes_from_the_lowest_part_that_has_paid_the_stable_part_by_the_same_rule(self):
        rec = json.loads((self.state / "high-layer.json").read_text())
        rec["parts"] = [{"part": "stable", "sessionId": "stable-sid"},
                        {"part": "direction", "kind": "material", "sessionId": "layer-sid", "parent": "stable-sid"}]
        (self.state / "high-layer.json").write_text(json.dumps(rec))
        self.touch("high-layer.looked", ago=watchdog.LAYER_EVERY + 60)
        plan = ("inventory", 200_000.0, 150_000.0)
        with patch.object(watchdog, "refresh_plan", lambda who: plan):
            watchdog.layers()
        self.assertEqual(self.started[-1], ["high", "layer", "--from", "inventory"])
        self.assertTrue(any("the high parts from inventory up are refreshed" in x for x in self.said), self.said)
        self.started.clear()
        plan = ("stable", 700_000.0, 600_000.0)
        self.touch("high-layer.looked", ago=watchdog.LAYER_EVERY + 60)
        with patch.object(watchdog, "refresh_plan", lambda who: plan):
            watchdog.layers()
        self.assertEqual(self.started, [["high", "layer", "--from", "stable"]])   # its reload, once paid, by the rule
        self.assertTrue(any("the high parts from stable up are refreshed" in x for x in self.said), self.said)

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
