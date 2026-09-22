"""Preservation and incomplete/corrupt-load controls; no Claude sessions launched."""
import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import base_pack as p
from digest import thy_digest
import manifest
import pack_notation as notation


class StaleShareTests(unittest.TestCase):
    """What of a layer has moved since it loaded (manifest.moved_tokens): a generated index by the lines that changed,
    anything else whole, and nothing where what the layer holds is the same."""

    def test_an_index_moves_by_its_changed_lines_and_a_theory_whole(self):
        # the theory names and the decision index, 34.5K of the max layer's 148K tokens, counted whole put it past
        # the refresh line after nearly every landing (refreshed 22:24 and 22:39 on 2026-09-21)
        with tempfile.TemporaryDirectory() as temp:
            index = Path(temp) / "theory-names.md"
            old = "".join(f"Theory_{i}\n" for i in range(800))
            index.write_text(old + "Theory_new\n")
            doc = Path(temp) / "NOTES.md"
            doc.write_text("a changed note\n" * 50)
            thy = Path(temp) / "A.thy"
            before = "theory A imports Main begin\nlemma l: \"True\" by simp\nend\n"
            thy.write_text(before.replace("by simp", "by auto"))     # a proof changed, the statement not
            recorded = {str(index): "old", str(doc): "old", str(thy): "old"}
            loaded = {str(index): old, str(doc): "a note\n" * 50,
                      str(thy): manifest.held_text(str(thy), manifest.level_of(str(thy)))[0]}
            moved = manifest.moved_tokens(str(index), recorded, loaded)
            self.assertGreater(moved, 0)
            self.assertLess(moved, manifest.tokens(str(index)) / 50)       # one line of 801, not the file
            self.assertEqual(manifest.moved_tokens(str(doc), recorded, loaded), manifest.tokens(str(doc)))
            self.assertEqual(manifest.moved_tokens(str(thy), recorded, loaded), 0)  # what it holds is the same
            # names wrapped many to a line: one put in re-wraps every line after it, and it is still one name
            import textwrap
            names = [f"Theory_{i}" for i in range(1500)]
            wrapped = lambda xs: textwrap.fill(" ".join(xs), 100) + "\n"
            index.write_text(wrapped(names[:10] + ["Theory_inserted"] + names[10:]))
            moved = manifest.moved_tokens(str(index), recorded, {str(index): wrapped(names)})
            self.assertLess(moved, manifest.tokens(str(index)) / 100)
            # without the layer's own text, the digests decide, as before
            self.assertEqual(manifest.moved_tokens(str(index), recorded, {}), manifest.tokens(str(index)))
            self.assertEqual(manifest.moved_tokens(str(index), {str(index): manifest.digest(str(index))}, {}), 0)


class AcknowledgementTests(unittest.TestCase):
    """The load's final line: what it shows is that the session read to the end, not that it copies well."""

    ID = "ad30832f993fef053894f978fc63de2caf65ced842e7f438fee7cd62ee8c2744"

    def test_an_id_copied_with_slips_says_the_session_read_to_the_end(self):
        # every chunk of the high base's reload was complete on 2026-09-22 21:56 and the load was thrown away for
        # four stuttered characters, as it had been at 21:36: 270K each time, and no layer refresh could finish
        self.assertTrue(p.acknowledges("LOADED " + self.ID, self.ID))
        self.assertTrue(p.acknowledges("LOADED ad30832f993f993fef053894f978fc63de2caf65ced842e7f438fee7cd"
                                       "62ee8c2744", self.ID))                  # stuttered, 68 characters
        self.assertTrue(p.acknowledges("LOADED " + self.ID[:20] + self.ID[21:], self.ID))   # one dropped, 63
        self.assertFalse(p.acknowledges("LOADED " + self.ID[:30], self.ID))     # half of it: it did not copy the id
        self.assertTrue(p.acknowledges("PART 6/6 all complete\n\nLOADED " + self.ID[:-1] + "0", self.ID))
        self.assertFalse(p.acknowledges("LOADED " + "f" * 64, self.ID))  # another pack's id: it read nothing
        self.assertFalse(p.acknowledges("LOADED", self.ID))
        self.assertFalse(p.acknowledges("done", self.ID))
        self.assertFalse(p.acknowledges("LOADED " + self.ID + "\nstill loading", self.ID))  # not its last line


class PackingTests(unittest.TestCase):
    def test_fact_prefixes_preserve_names_duplicates_and_order(self):
        for names in [
            ["long_family_sound", "long_family_complete", "long_family_exact", "other", "long_family_sound"],
            ["foo_1", "foo_2", "foo_bar_x", "foo_bar_y", "foo'"],
            ["_x", "_y", "name_with_underscore_", "name_with_underscore"],
        ]:
            packed = notation.fact_groups(names)
            self.assertEqual(notation.expand_fact_body(packed), ", ".join(names))

    def test_fact_compression_changes_no_declaration_or_premise(self):
        text = ('definition long_declaration_name :: "bool" where "long_declaration_name = True"\n'
                'locale complete_contract = fixes x assumes requirement: "P x"\nbegin\n'
                '(* proved here: long_family_sound, long_family_complete, long_family_exact *)\nend\n')
        packed, edits = p.apply_edits(text, notation.fact_edits(text))
        self.assertIn("long_family_{sound,complete,exact}", packed)
        self.assertEqual(notation.expand_facts(packed), text)
        self.assertEqual(p.restore_text(packed, edits), text)
        self.assertEqual(notation.FACTS.sub("", packed), notation.FACTS.sub("", text))
        self.assertNotIn("@self", packed)

    def test_literal_fact_example_is_not_reinterpreted(self):
        note = "(* proved here: family_{one,two} *)"
        self.assertEqual(notation.fact_edits(note, [note]), [])
        self.assertEqual(notation.expand_facts(note, [note]), note)

    def test_compact_header_requires_exact_source_path_identity(self):
        source = dict(label="theories/Example.thy", level="definitions")
        self.assertEqual(p.source_header(source, "theory Example imports Main begin\n", True),
                         "\n=== [definitions] ===\n")
        self.assertIn("theories/Example.thy", p.source_header(source, "theory Other begin\n", True))
        self.assertIn("elsewhere/Example.thy", p.source_header(
            dict(label="elsewhere/Example.thy", level="definitions"), "theory Example begin\n", True))

    def test_literal_omission_note_is_not_abbreviated(self):
        note = "(* proof omitted: 28 lines *)"
        original = 'lemma text_value: "s = \'\'' + note + '\'\'"\n'
        packed, edits = p.pack_theory(original, {}, 3, [note])
        self.assertEqual(packed, original)
        self.assertEqual(p.restore_text(packed, edits), original)

    def test_symbols_and_markers_roundtrip_with_existing_unicode(self):
        original = 'lemma a: "x \\<and> y ∧ z"\\n  (* proof omitted: 28 lines *)\\n'.replace("\\n", "\n")
        packed, edits = p.pack_theory(original, {"\\<and>": "∧"}, 3)
        self.assertIn('x ∧ y ∧ z', packed)
        self.assertIn("(* proof:28 *)", packed)
        self.assertEqual(p.restore_text(packed, edits), original)

    def test_signatures_keep_the_type_and_shorten_the_equations_note(self):
        source = ('theory T imports Main begin\n'
                  'definition f ::\n  "nat \\<Rightarrow> nat" where\n  "f n = n + 1"\n'
                  'fun g :: "nat \\<Rightarrow> nat" where\n  "g 0 = 0"\n| "g (Suc n) = g n"\n'
                  'lemma f_pos: "0 < f n"\n  by (simp add: f_def)\n'
                  'end\n')
        held = thy_digest(source, "signatures")
        self.assertIn('"nat \\<Rightarrow> nat" where', held)
        self.assertNotIn("n + 1", held)
        self.assertIn("(* equations omitted: 1 lines *)", held)
        self.assertIn("(* equations omitted: 2 lines *)", held)
        self.assertIn("(* proved here: f_pos *)", held)
        packed, edits = p.pack_theory(held, {"\\<Rightarrow>": "⇒"}, 3)
        self.assertIn("(* equations:2 *)", packed)
        self.assertEqual(p.restore_text(packed, edits), held)

    def test_tier_header_names_the_digest_level(self):
        with tempfile.TemporaryDirectory() as temp:
            listed = Path(temp) / "list.txt"
            thy = Path(temp) / "T.thy"
            thy.write_text("theory T imports Main begin\nend\n")
            listed.write_text(f"# founding, as signatures\n{thy}\n# central, as definitions\n{temp}/U.thy\n")
            (Path(temp) / "U.thy").write_text("theory U imports Main begin\nend\n")
            with patch.dict(os.environ, {"ORCH_LOAD_LIST": str(listed)}):
                manifest.held_files()
            self.assertEqual(manifest.level_of(str(thy)), "signatures")
            self.assertEqual(manifest.level_of(f"{temp}/U.thy"), "definitions")

    def test_opaque_contents_keep_whitespace(self):
        original = ('theory T imports Main begin\n\n'
                    '  definition s where "s = \'\'a  b\'\'"\n'
                    '  lemma x: "P \\"quoted\\"\n    Q"\n'
                    '  text ‹\n    prose and nested ‹cartouche›\n\n  ›\n'
                    '  (* outer\n    (* nested *)\n  *)\n'
                    'end\n')
        packed, edits = p.pack_theory(original, {}, 3)
        self.assertIn("s = ''a  b''", packed)
        self.assertIn('P \\"quoted\\"\n    Q', packed)
        self.assertIn("‹\n    prose and nested ‹cartouche›\n\n  ›", packed)
        self.assertIn("(* outer\n    (* nested *)\n  *)", packed)
        self.assertEqual(p.restore_text(packed, edits), original)

    def test_unclosed_opaque_fragment_gets_no_layout_guess(self):
        self.assertEqual(p.outer_layout_edits('ML ‹\n  partial body\n'), [])
        self.assertEqual(p.outer_layout_edits('lemma x: "partial\n'), [])

    def test_theory_index_preserves_order_and_every_name(self):
        original = "# names\n" + " ".join(["Factor_Example_" + str(i) for i in range(20)] +
                                         ["RRA_Core", "Factor_Other", "Factor_Example_0"]) + "\n"
        packed, edits = p.pack_index(original)
        self.assertLess(len(packed), len(original))
        self.assertEqual(p.expand_index(packed), p.index_names(original))
        self.assertEqual(p.restore_text(packed, edits), original)

    def test_theory_index_keeps_registration_section_boundaries(self):
        first = ["Registered_Long_Family_" + str(i) for i in range(20)]
        second = ["Unregistered_Long_Family_" + str(i) for i in range(20)]
        original = "# ROOT order\n" + " ".join(first) + "\n# Additional source files\n" + " ".join(second) + "\n"
        packed, edits = p.pack_index(original)
        before, after = packed.split("# Additional source files\n")
        self.assertEqual(p.expand_index(before), first)
        self.assertEqual(p.expand_index(after), second)
        self.assertEqual(p.restore_text(packed, edits), original)

    def test_map_index_leaves_out_what_the_list_holds(self):
        import select_base_load as selector
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "theories").mkdir()
            for name in ("A", "B"):
                (root / "theories" / (name + ".thy")).write_text("theory " + name + " begin end\n")
            (root / "ROOT").write_text("session Test = HOL +\n  theories\n    A\n    B\n")
            (root / "THEORY_MAP.md").write_text("| Theory | Imports | Content |\n|---|---|---|\n"
                                                "| A | Main | What A holds; more |\n| B | A | What B holds. More |\n")
            (root / "DECISIONS.md").write_text("# Decisions\n\n## One\n\nThe first. Then more.\n")
            listed = root / "list.txt"
            listed.write_text(f"# founding\n{root}/theories/A.thy\n# index\n{root}/state/held/theory-map-index.md\n")
            with patch.object(selector, "PROJECT", str(root)), patch.object(selector, "HERE", str(root)), \
                    patch.dict(os.environ, {"ORCH_LOAD_LIST": str(listed)}):
                selector.refresh_indexes()
            index = (root / "state/held/theory-map-index.md").read_text()
            self.assertIn("B: What B holds", index)
            self.assertNotIn("A: ", index)
            self.assertIn("## One — The first.", (root / "state/held/decisions-index.md").read_text())

    def test_catalogue_includes_sources_missing_from_the_map(self):
        import select_base_load as selector
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "theories").mkdir()
            for name in ("A", "B", "New"):
                (root / "theories" / (name + ".thy")).write_text("theory " + name + " begin end\n")
            (root / "ROOT").write_text("session Test = HOL +\n  theories\n    B\n    A\n")
            with patch.object(selector, "PROJECT", str(root)), patch.object(selector, "HERE", str(root)):
                self.assertEqual(selector.theory_names(), 3)
            text = (root / "state/held/theory-names.md").read_text()
            self.assertEqual(p.index_names(text), ["B", "A", "New"])
            self.assertIn("Additional source files not listed in ROOT", text)

    def test_selector_measures_implementers_not_bases_or_orchestration(self):
        import select_base_load as selector
        def session(*texts_and_commands):
            records = []
            for kind, value in texts_and_commands:
                if kind == "user":
                    records.append({"type": "user", "message": {"role": "user", "content": value}})
                else:
                    records.append({"type": "assistant", "message": {"model": "claude-opus-5", "content": [
                        {"type": "tool_use", "name": "Bash", "input": {"command": value}}]}})
            return "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records)
        load = ("user", p.BOOTSTRAP_PREFIX + " For PART=1 through 2, run the command below.")
        emit = ("tool", "/usr/bin/python3 .claude/orchestration/base_pack.py emit /pack 1")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "base.jsonl").write_text(session(load, emit))
            (root / "impl.jsonl").write_text(session(load, emit, ("user", "You are impl-3, a working copy."),
                                                     ("tool", "cat .claude/orchestration/state/v2.json"),
                                                     ("tool", "sed -n 1,40p theories/RRA_Selection.thy")))
            (root / "orch.jsonl").write_text(session(("user", "Review the orchestrator."),
                                                     ("tool", "cat .claude/orchestration/watchdog.py"),
                                                     ("tool", "sed -n 1,40p theories/RRA_Selection.thy")))
            with patch.object(selector, "TRANSCRIPTS", str(root)):
                self.assertEqual([Path(f).name for f in selector.implementer_sessions()], ["impl.jsonl"])

    def test_utf8_chunks_handle_long_lines_without_loss(self):
        original = "⇒" * 1000 + "\n" + "x\n" * 400
        chunks = p.split_bytes(original, 256)
        self.assertEqual("".join(chunks), original)
        self.assertTrue(all(len(c.encode()) <= 256 for c in chunks))

    def test_changed_packed_symbol_refuses_restoration(self):
        packed, edits = p.pack_theory('x \\<and> y', {"\\<and>": "∧"}, 1)
        with self.assertRaises(ValueError):
            p.restore_text(packed.replace("∧", "∨"), edits)

    def make_pack(self, root):
        path = root / "symbols"
        path.write_text("\\<and> code: 0x002227\n")
        prose = "> " + "The owner's repeated words must remain recoverable. " * 10
        sources = [
            {"path": "/example/A.thy", "label": "A.thy", "tier": "pinned", "level": "statements",
             "text": 'theory A imports Main begin\n  lemma a: "P \\<and> Q"\n  (* proof omitted: 2 lines *)\nend\n',
             "source_sha256": "fixture", "source_sha1": "fixture"},
            {"path": "/example/words.md", "label": "words.md", "tier": "owner", "level": "statements",
             "text": prose + "\n\nDifferent surrounding context.\n\n" + prose + "\n",
             "source_sha256": "fixture", "source_sha1": "fixture"}]
        destination = root / "pack"
        with patch.object(p, "frozen_sources", return_value=sources):
            p.build(destination, path, 256)
        return destination

    def test_every_source_and_tier_roundtrips_in_full_pack(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = self.make_pack(Path(temp))
            meta = p.verify(directory)
            text = "".join(p.checked_chunks(directory, meta))
            self.assertIn("\n# Pinned\n", text)
            self.assertIn("\n# Owner\n", text)
            self.assertNotIn("Tier:", text)
            # the loaded form: glyphs and short notes, but no prose reuse and no fact-name groups
            self.assertIn("P ∧ Q", text)
            self.assertNotIn("\\<and>", text)
            self.assertIn("(* proof:2 *)", text)
            self.assertNotIn("[REPEAT ", text)
            self.assertIn("[REPEAT ", (directory / "exact-prose-reuse.txt").read_text())
            self.assertEqual(meta["selected_variant"], "all-but-fact-groups")
            self.assertEqual(len(meta["sources"]), 2)

    def test_loaded_form_keeps_lemma_names_written_out(self):
        text = ('theory B imports Main begin\ndefinition b :: bool where "b = True"\n'
                '(* proved here: long_family_sound, long_family_complete, long_family_exact *)\nend\n')
        source = {"path": "/example/B.thy", "label": "theories/B.thy", "tier": "every other founding theory, as definitions",
                  "level": "definitions", "text": text, "source_sha256": "fixture", "source_sha1": "fixture"}
        loaded, records, _ = p.render([source], {}, p.SELECTED_LAYERS)
        self.assertIn("long_family_sound, long_family_complete, long_family_exact", loaded)
        self.assertNotIn("{", loaded[loaded.index("=== ["):])
        self.assertEqual(p.restore_source(loaded[records[0]["start"]:records[0]["start"] + records[0]["length"]],
                                          records[0]), text)

    def test_tier_headings_keep_the_subject_and_drop_curation_notes(self):
        cases = {
            "pinned: the plan (the basis of nearly every correction the first run's implementers needed)": "The plan",
            "pinned idea: index notions that exist (the first run reached for these only after being told)":
                "Idea: index notions that exist",
            "pinned: current development additions since the sealed base (2026-09-18 refresh; statements)":
                "Current development additions",
            "every other founding theory, as definitions (generated: commentary)": "Every other founding theory, as definitions",
            "measured (generated 2026-09-18 from 7 implementer sessions; K chars pulled)":
                "Working frontier: theories and tools in current use",
        }
        for tier, subject in cases.items():
            self.assertEqual(p.tier_heading(tier), "\n# " + subject + "\n")

    def test_only_digested_sources_show_a_digest_level(self):
        self.assertEqual(p.source_header(dict(label="notes.md", level="statements"), "text"), "\n=== notes.md ===\n")
        self.assertEqual(p.source_header(dict(label="tools/x.py", level="statements"), "text"),
                         "\n=== tools/x.py [statements] ===\n")

    def test_missing_truncated_or_sidechain_chunk_is_not_a_complete_load(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            meta = p.load(directory)
            chunks = p.checked_chunks(directory, meta)
            transcript = root / "session.jsonl"
            entries = [{"type": "user", "message": {"content": [
                {"type": "tool_result", "content": p.envelope(meta, i, text)}]}}
                       for i, text in enumerate(chunks, 1)]
            entries += [{"type": "assistant", "message": {"content": [
                {"type": "text", "text": "LOADED " + meta["id"]}]}}]

            def write(records):
                transcript.write_text("".join(json.dumps(r) + "\n" for r in records))

            write(entries)
            self.assertEqual(p.check_load(directory, transcript)["complete_chunks"], len(chunks))
            # Claude Code stores a Bash result without its trailing newline; such a load is complete
            stored = json.loads(json.dumps(entries))
            for entry in stored[:-1]:
                entry["message"]["content"][0]["content"] = entry["message"]["content"][0]["content"].rstrip("\n")
            write(stored)
            self.assertEqual(p.check_load(directory, transcript)["complete_chunks"], len(chunks))
            write(entries[1:])
            with self.assertRaises(ValueError):
                p.check_load(directory, transcript)
            broken = json.loads(json.dumps(entries))
            broken[0]["message"]["content"][0]["content"] = p.envelope(meta, 1, chunks[0][:-1])
            write(broken)
            with self.assertRaises(ValueError):
                p.check_load(directory, transcript)
            broken = json.loads(json.dumps(entries))
            broken[0]["isSidechain"] = True
            write(broken)
            with self.assertRaises(ValueError):
                p.check_load(directory, transcript)

    def test_a_slip_in_the_echoed_id_does_not_refuse_a_complete_load(self):
        # the max layer of 2026-09-21 loaded all four of its chunks and replied its 64-character id with one character
        # wrong: the chunks are what is checked exactly, the reply only that the session read to the end
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            meta = p.load(directory)
            loaded = [{"type": "user", "message": {"content": [{"type": "tool_result", "content": p.envelope(meta, i, t)}]}}
                      for i, t in enumerate(p.checked_chunks(directory, meta), 1)]
            transcript = root / "session.jsonl"

            def reply(text):
                return {"type": "assistant", "message": {"content": [{"type": "text", "text": text}]}}

            def slipped(pack_id, *at):
                return "".join(("0" if c != "0" else "1") if k in at else c for k, c in enumerate(pack_id))

            def complete(records):
                transcript.write_text("".join(json.dumps(r) + "\n" for r in records))
                try:
                    return bool(p.check_load(directory, transcript))
                except ValueError:
                    return False

            self.assertTrue(complete(loaded + [reply("LOADED " + slipped(meta["id"], 12))]))
            self.assertTrue(complete(loaded + [reply("LOADED " + slipped(meta["id"], 12, 13))]))   # two: a copy still
            self.assertFalse(complete(loaded + [reply("LOADED " + slipped(meta["id"], *range(12, 20)))]))  # eight: no
            self.assertFalse(complete([reply("LOADED " + meta["id"])] + loaded))  # said before the chunks arrived
            self.assertFalse(complete(loaded + [reply("LOADED")]))
            # the right line last, after a garbled one: the high layer of 2026-09-22 15:07, all seven chunks loaded
            short = meta["id"][:12]
            self.assertTrue(complete(loaded + [reply(f"LOADED {short} PART 7/7 all complete — LOADED {short}{short[-4:]}… "
                                                     f"correction:\n\nLOADED {meta['id']}")]))
            self.assertFalse(complete(loaded + [reply(f"LOADED {meta['id']}\nand something after it")]))  # not the last

    def test_altered_chunk_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = self.make_pack(Path(temp))
            first = directory / "chunks/0001.txt"
            text = first.read_text()
            first.write_text(("#" if text[0] != "#" else "!") + text[1:])  # same size, different content
            with self.assertRaises(ValueError):
                p.verify(directory)

    def test_existing_output_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(ValueError, "already exists"):
                p.build(Path(temp), Path("/not/read"), 256)

    def test_repack_keeps_the_original_frozen_inputs_and_compares_spellings(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first = self.make_pack(root)
            second = root / "second"
            with patch.object(p, "frozen_sources", side_effect=AssertionError("must not refresh inputs")):
                meta = p.build(second, root / "symbols", 256, first)
            self.assertEqual(meta["frozen_from_pack"], p.load(first)["id"])
            self.assertEqual([r["digest_sha256"] for r in meta["sources"]],
                             [r["digest_sha256"] for r in p.load(first)["sources"]])
            self.assertTrue({"escaped-symbols", "common-unicode"}.issubset(
                {row["name"] for row in meta["variants"]}))
            self.assertEqual(p.verify(second)["selected_variant"], "all-but-fact-groups")

    def test_count_filters_variants_and_binds_results_to_the_exact_payload(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = self.make_pack(Path(temp))
            requested = []

            def response(request, timeout):
                body = json.loads(request.data)
                self.assertEqual(body["model"], "test-model")
                self.assertEqual(len(body["messages"]), 1)
                requested.append(body["messages"][0]["content"])
                return io.BytesIO(json.dumps({"input_tokens": 100 + len(requested)}).encode())

            stdout = io.StringIO()
            with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "packing-test-key"}), \
                    patch.object(p.urllib.request, "urlopen", side_effect=response), \
                    contextlib.redirect_stdout(stdout):
                p.count(directory, "test-model", ["compact-theory-headers", "escaped-symbols"])
            self.assertEqual(len(requested), 2)
            result = json.loads((directory / "token-counts.json").read_text())
            self.assertEqual(result["model"], "test-model")
            self.assertEqual([row["payload_sha256"] for row in result["counts"]],
                             [p.sha(text) for text in requested])
            self.assertEqual([row["input_tokens"] for row in result["counts"]], [101, 102])
            self.assertNotIn("packing-test-key", stdout.getvalue())

    def test_count_needs_an_api_key_and_never_reads_the_claude_login(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = self.make_pack(Path(temp))
            environment = {k: v for k, v in os.environ.items() if k != "ANTHROPIC_API_KEY"}
            with patch.dict(os.environ, environment, clear=True), \
                    patch.object(p.Path, "home", side_effect=AssertionError("must not read the Claude login")), \
                    patch.object(p.urllib.request, "urlopen", side_effect=AssertionError("must not call")):
                with self.assertRaisesRegex(ValueError, "ANTHROPIC_API_KEY"):
                    p.count(directory, "test-model")

    def test_a_cold_stable_base_is_loaded_again_and_replaces_the_old_with_its_layer(self):
        # a fork of a stable base whose own entry is gone writes it whole, and so would every refresh after it: a fork
        # that misses never makes that entry again (each fork's first turn names the fork). The harness loads it again
        # (the owner, 2026-09-21), the old base and layer serving until the new pair is sealed.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            meta = p.load(directory)
            home, state, binary = root / "home", root / "state", root / "bin"
            project = p.HERE.parent.parent
            sessions = home / ".claude/projects" / str(project).replace("/", "-").replace("_", "-")
            for d in (sessions, state, binary):
                d.mkdir(parents=True)
            flags = " ".join((p.HERE / "session-flags").read_text().split())

            def request(rid, read, write, text="."):
                return {"type": "assistant", "message": {"id": rid, "content": [{"type": "text", "text": text}],
                        "usage": {"input_tokens": 2, "cache_read_input_tokens": read,
                                  "cache_creation_input_tokens": write}}}

            def write(sid, records):
                (sessions / f"{sid}.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))

            (state / "xhigh-base.json").write_text(json.dumps(
                {"sessionId": "old-base-sid", "model": "claude-opus-5[1m]", "effort": "xhigh", "name": "xhigh-base",
                 "flags": flags}))
            (state / "xhigh-layer.json").write_text(json.dumps(
                {"sessionId": "old-layer-sid", "base": "old-base-sid", "name": "xhigh-layer-old", "flags": flags}))
            (state / "xhigh-manifest.json").write_text(json.dumps({"taken": "t0", "files": {"/example/A.thy": "old"}}))
            (state / "layer-old-layer-sid-manifest.json").write_text(json.dumps({"taken": "t0", "files": {"L": "l0"}}))
            loaded = [{"type": "user", "message": {"content": [{"type": "tool_result", "content": p.envelope(meta, i, t)}]}}
                      for i, t in enumerate(p.checked_chunks(directory, meta), 1)]
            base = loaded + [request("req-newbase", 0, 1300, "LOADED " + meta["id"])]
            write("new-layer-sid", base + loaded + [request("req-layer", 1300, 300, "LOADED " + meta["id"])])
            fake = binary / "claude"
            fake.write_text("""#!/usr/bin/env python3
import json, os, sys
log = os.environ['REBUILD_TEST_LOG']
open(log, 'a').write(json.dumps(sys.argv[1:]) + '\\n')
calls = [json.loads(l) for l in open(log)]
if sys.argv[1:] == ['agents', '--json']:
    names = [a[a.index('-n') + 1] for a in calls if '--bg' in a and '-n' in a]
    print(json.dumps([dict(name=n, id='id-' + n, sessionId='new-base-sid', kind='background', status='idle',
                           state='done', cwd=os.environ['REBUILD_TEST_PROJECT']) for n in names]
                     + [dict(name='xhigh-layer-1', id='id-layer', sessionId='new-layer-sid', kind='background',
                             status='idle', state='done', cwd=os.environ['REBUILD_TEST_PROJECT'])]))
elif '--bg' in sys.argv and '--resume' not in sys.argv:  # the base loads: its transcript, as a complete load leaves it
    open(os.environ['REBUILD_TEST_BASE'], 'w').write(os.environ['REBUILD_TEST_RECORDS'])
""")
            fake.chmod(0o755)
            calls = root / "calls.log"
            env = {k: v for k, v in os.environ.items() if not k.startswith(("ORCH_", "CLAUDE"))}
            env.update(HOME=str(home), PATH=str(binary) + os.pathsep + os.environ["PATH"], ORCH_CONTROL="1",
                       ORCH_STATE_DIR=str(state), REBUILD_TEST_LOG=str(calls),
                       REBUILD_TEST_PROJECT=str(project), BASE_PACK_DIR=str(directory),
                       REBUILD_TEST_BASE=str(sessions / "new-base-sid.jsonl"),
                       REBUILD_TEST_RECORDS="".join(json.dumps(r) + "\n" for r in base))

            def base_sh(*args):
                return subprocess.run(["sh", str(p.HERE / "base.sh"), "xhigh", *args], env=env, capture_output=True,
                                      text=True, timeout=120)
            try:
                again = base_sh("restable")
                self.assertEqual(again.returncode, 0, again.stdout + again.stderr)
                started = [json.loads(l) for l in calls.read_text().splitlines() if '"--bg"' in l]
                self.assertEqual(len(started), 1)
                self.assertNotIn("--resume", started[0])                 # loaded anew, not a fork of the cold base
                self.assertIn("its entry is cold, so the base is loaded again", (state / "warm.log").read_text())
                self.assertEqual(json.loads((state / "xhigh-base.json").read_text())["sessionId"], "old-base-sid")
                self.assertEqual(json.loads((state / "xhigh-base-next.json").read_text())["sessionId"], "new-base-sid")
                self.assertTrue((state / "xhigh-manifest-next.json").exists())  # the old pair serves meanwhile
                done = base_sh("layer", "--adopt", "xhigh-layer-1", str(directory))
                self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
                self.assertEqual(json.loads((state / "xhigh-base.json").read_text())["sessionId"], "new-base-sid")
                layer = json.loads((state / "xhigh-layer.json").read_text())
                self.assertEqual((layer["sessionId"], layer["base"]), ("new-layer-sid", "new-base-sid"))
                self.assertFalse((state / "xhigh-base-next.json").exists())
                self.assertFalse((state / "xhigh-manifest-next.json").exists())
                self.assertNotIn("/example/A.thy\": \"old", (state / "xhigh-manifest.json").read_text())
                # a session of the old layer is still told what changed against the stable load it holds
                kept = json.loads((state / "layer-old-layer-sid-manifest.json").read_text())
                self.assertEqual(kept["files"], {"/example/A.thy": "old", "L": "l0"})
                self.assertTrue((state / "xhigh-stable.hit").exists())    # the layer read it: warm, and pinged
                self.assertIn("its read of the base: OK", done.stdout)
                self.assertNotIn("over the", (state / "warm.log").read_text())  # a base within the target says nothing
                env["ORCH_BASE_TARGET"] = "1000"
                again = base_sh("layer", "--adopt", "xhigh-layer-1", str(directory))
                self.assertEqual(again.returncode, 0, again.stdout + again.stderr)  # said, not refused
                self.assertIn("over the 1000 target", (state / "warm.log").read_text())
            finally:
                for _ in range(30):  # seal_layer starts the keep-warm daemon, which outlives the command
                    if (state / "warm.pid").exists():
                        with contextlib.suppress(OSError, ValueError):
                            os.kill(int((state / "warm.pid").read_text()), 15)
                        break
                    time.sleep(0.1)

    def test_a_layer_is_not_built_over_a_stable_base_the_list_no_longer_names(self):
        # the founding tier chosen by use (2026-09-22) changed what the stable part lists; a layer built over the
        # recorded stable base, its entry still warm, would have held the old reference under a layer chosen for the
        # new one (about 665K against the 530K target). The base is loaded again from the list, and says why.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            home, state, binary = root / "home", root / "state", root / "bin"
            for d in (state, binary, home):
                d.mkdir(parents=True, exist_ok=True)
            flags = " ".join((p.HERE / "session-flags").read_text().split())
            (state / "xhigh-base.json").write_text(json.dumps(
                {"sessionId": "old-base-sid", "model": "claude-opus-5[1m]", "effort": "xhigh", "name": "xhigh-base",
                 "flags": flags}))
            (state / "xhigh-layer.json").write_text(json.dumps(
                {"sessionId": "old-layer-sid", "base": "old-base-sid", "name": "xhigh-layer-old", "flags": flags}))
            (state / "xhigh-manifest.json").write_text(json.dumps({"taken": "t0", "files": {"/example/A.thy": "old"}}))
            (state / "xhigh-stable.hit").write_text("")                  # its entry warm: read a minute ago
            calls = root / "calls.log"
            fake = binary / "claude"
            fake.write_text("#!/bin/sh\necho \"$*\" >> \"$REBUILD_TEST_LOG\"\n"
                            "[ \"$1 $2\" = \"agents --json\" ] && echo '[]'\nexit 0\n")
            fake.chmod(0o755)
            env = {k: v for k, v in os.environ.items() if not k.startswith(("ORCH_", "CLAUDE"))}
            env.update(HOME=str(home), PATH=str(binary) + os.pathsep + os.environ["PATH"], ORCH_CONTROL="1",
                       ORCH_STATE_DIR=str(state), REBUILD_TEST_LOG=str(calls), BASE_PACK_DIR=str(directory),
                       STABLE_WAIT="2", LAYER_WAIT="2")
            out = subprocess.run(["sh", str(p.HERE / "base.sh"), "xhigh", "layer"], env=env, capture_output=True,
                                 text=True, timeout=120)
            self.assertNotEqual(out.returncode, 0)                       # the fake base never starts: it stops there
            said = (state / "warm.log").read_text()
            self.assertIn("stable xhigh: the list's stable part names", said)
            started = [l for l in calls.read_text().splitlines() if "--bg" in l]
            self.assertTrue(started and all("--resume" not in l for l in started), started)  # loaded, not forked

    def test_a_layer_that_loaded_but_was_not_recorded_is_adopted_without_a_second_load(self):
        # the max layer of 2026-09-21 was complete and refused for a slip in its reply; loading it again would have
        # written 135K. `layer --adopt` records it through the same steps as a new layer's, and only a fork of the base.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            meta = p.load(directory)
            home, state, binary = root / "home", root / "state", root / "bin"
            project = p.HERE.parent.parent
            sessions = home / ".claude/projects" / str(project).replace("/", "-").replace("_", "-")
            for d in (sessions, state, binary):
                d.mkdir(parents=True)
            flags = " ".join((p.HERE / "session-flags").read_text().split())
            (state / "max-base.json").write_text(json.dumps(
                {"sessionId": "base-sid", "model": "claude-opus-5[1m]", "effort": "max", "name": "max-base",
                 "flags": flags}))

            def request(rid, read, write, text="."):
                return {"type": "assistant", "message": {"id": rid, "content": [{"type": "text", "text": text}],
                        "usage": {"input_tokens": 2, "cache_read_input_tokens": read,
                                  "cache_creation_input_tokens": write}}}

            def write(sid, records):
                (sessions / f"{sid}.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))

            base = [request("req-base", 0, 1000)]
            loaded = [{"type": "user", "message": {"content": [{"type": "tool_result", "content": p.envelope(meta, i, t)}]}}
                      for i, t in enumerate(p.checked_chunks(directory, meta), 1)]
            slipped = meta["id"][:12] + ("0" if meta["id"][12] != "0" else "1") + meta["id"][13:]
            write("base-sid", base)
            write("layer-sid", base + loaded + [request("req-layer", 1000, 300, "LOADED " + slipped)])
            write("other-sid", loaded + [request("req-other", 0, 1300, "LOADED " + meta["id"])])  # not a fork of it
            write("missed-sid", base + loaded + [request("req-missed", 0, 1300, "LOADED " + meta["id"])])  # wrote it
            fake = binary / "claude"
            fake.write_text("""#!/usr/bin/env python3
import json, os, sys
open(os.environ['ADOPT_TEST_LOG'], 'a').write(' '.join(sys.argv[1:]) + '\\n')
if sys.argv[1:] == ['agents', '--json']:
    print(json.dumps([dict(name=n, id=i, sessionId=s, kind='background', status='idle', state='done',
                           cwd=os.environ['ADOPT_TEST_PROJECT'])
                      for n, i, s in (('max-layer-1', 'abcd1234', 'layer-sid'), ('max-other-1', 'ef567890', 'other-sid'),
                                      ('max-layer-2', 'aa11bb22', 'missed-sid'))]))
""")
            fake.chmod(0o755)
            calls = root / "calls.log"
            env = {k: v for k, v in os.environ.items() if not k.startswith(("ORCH_", "CLAUDE"))}
            env.update(HOME=str(home), PATH=str(binary) + os.pathsep + os.environ["PATH"], ORCH_CONTROL="1",
                       ORCH_STATE_DIR=str(state), ADOPT_TEST_LOG=str(calls), ADOPT_TEST_PROJECT=str(project))

            def adopt(name):
                return subprocess.run(["sh", str(p.HERE / "base.sh"), "max", "layer", "--adopt", name, str(directory)],
                                      env=env, capture_output=True, text=True, timeout=60)
            try:
                refused = adopt("max-other-1")
                self.assertEqual(refused.returncode, 3, refused.stdout + refused.stderr)
                self.assertIn("is not a fork of the max base", refused.stderr)
                self.assertFalse((state / "max-layer.json").exists())
                done = adopt("max-layer-1")
                self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
                record = json.loads((state / "max-layer.json").read_text())
                self.assertEqual((record["sessionId"], record["base"], record["pack"], record["context"], record["flags"]),
                                 ("layer-sid", "base-sid", str(directory), 1302, flags))
                said = calls.read_text()
                self.assertIn("stop abcd1234", said)  # sealed, as a new layer is
                self.assertNotIn("--bg", said)         # and nothing was loaded again
                # and every sealed layer says whether it read its base from cache: only the layer is pinged
                self.assertIn("layer max: OK   session fork layer-si of base base-sid", (state / "warm.log").read_text())
                self.assertIn("its read of the base: OK", done.stdout)
                # the stable base's own entry is warm after a layer that read it, and not after one that missed: a
                # fork that missed wrote its own prefix, which no later fork reads (the max refreshes of 2026-09-21)
                self.assertTrue((state / "max-stable.hit").exists())
                (state / "max-stable.hit").unlink()
                missed = adopt("max-layer-2")
                self.assertEqual(missed.returncode, 0, missed.stdout + missed.stderr)
                self.assertIn("its read of the base: MISS", missed.stdout)
                self.assertFalse((state / "max-stable.hit").exists())
            finally:
                for _ in range(30):  # seal_layer starts the keep-warm daemon, which outlives the command
                    if (state / "warm.pid").exists():
                        with contextlib.suppress(OSError, ValueError):
                            os.kill(int((state / "warm.pid").read_text()), 15)
                        break
                    time.sleep(0.1)

    def test_build_packed_launches_the_frozen_pack_with_isolated_state(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = self.make_pack(root)
            binary = root / "bin"
            binary.mkdir()
            fake = binary / "claude"
            fake.write_text("""#!/usr/bin/env python3
import json, os, pathlib, sys
record = pathlib.Path(os.environ['PACK_TEST_AGENT'])
if sys.argv[1:] == ['agents', '--json']:
    print('[' + record.read_text() + ']' if record.exists() else '[]')
elif '--bg' in sys.argv:
    record.write_text(json.dumps(dict(kind='background', id='test123', status='idle',
        sessionId='00000000-0000-0000-0000-000000000001', state='done',
        cwd=os.getcwd(), name=sys.argv[sys.argv.index('-n')+1])))
    pathlib.Path(os.environ['PACK_TEST_ARGS']).write_text(json.dumps(sys.argv))
else:
    sys.exit('unexpected test command')
""")
            fake.chmod(0o755)
            state = root / "state"
            # the fake claude stands in for the real one, so what the real one could do here (v2.py control: not
            # from inside Claude Code's sandbox) is not this test's subject
            env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], ORCH_CONTROL="1",
                       ORCH_STATE_DIR=str(state), BASE_PACK_DIR=str(directory),
                       BASE_NAME="packed-test", PACK_TEST_AGENT=str(root / "agent.json"),
                       PACK_TEST_ARGS=str(root / "args.json"))
            result = subprocess.run(["sh", str(p.HERE / "base.sh"), "max", "build-packed"],
                                    env=env, capture_output=True, text=True, timeout=15)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            record = json.loads((state / "max-base-building.json").read_text())
            self.assertEqual(record["pack"], str(directory))
            self.assertEqual(record["name"], "packed-test")
            args = json.loads((root / "args.json").read_text())
            self.assertIn("emit", args[-1])
            self.assertIn(p.load(directory)["id"], args[-1])
            self.assertFalse((state / "max-base.json").exists())
            (state / "max-base.json").write_text(json.dumps(record))
            before = (root / "args.json").read_text()
            self.assertEqual(record["flags"], " ".join((p.HERE / "session-flags").read_text().split()))  # its tools
            # the pack is the one loader: `extend` read a file with the Read tool, which no base has (2026-09-21)
            extension = subprocess.run(["sh", str(p.HERE / "base.sh"), "max", "extend", str(fake)],
                                       env=env, capture_output=True, text=True, timeout=5)
            self.assertEqual(extension.returncode, 2)
            self.assertIn("usage", extension.stderr)
            self.assertEqual((root / "args.json").read_text(), before)

class StaleInATreeTests(unittest.TestCase):
    def test_a_tree_s_files_are_compared_to_the_load_by_their_place_in_the_tree(self):
        # the load is recorded in the one tree; review-79, in a tree of its own, was told 664 files were stale since
        # the xhigh load, of 362 it holds: every one read as changed and again as new (2026-09-21)
        from unittest.mock import patch
        recorded = {"/one/theories/A.thy": "a", "/one/theories/B.thy": "b", "/state/held/names.md": "n"}
        now = {"/one/.build/trees/79/theories/A.thy": "a", "/one/.build/trees/79/theories/B.thy": "B2",
               "/one/.build/trees/79/theories/C.thy": "c", "/state/held/names.md": "n"}
        with patch.object(manifest, "ONE", "/one"), patch.object(manifest, "PROJECT", "/one/.build/trees/79"):
            self.assertEqual(manifest.changed_since(recorded, now), (["theories/B.thy"], ["theories/C.thy"]))
        with patch.object(manifest, "ONE", "/one"), patch.object(manifest, "PROJECT", "/one"):  # the one tree itself
            self.assertEqual(manifest.changed_since(recorded, {"/one/theories/A.thy": "a"}),
                             (["theories/B.thy", "/state/held/names.md"], []))

    def test_what_is_stale_is_said_by_the_load_that_holds_it_and_the_tree_s_own_apart(self):
        # task 145's session, its tree made before #144's tools landed, was told the tools a layer loaded eight minutes
        # before were "stale since xhigh load 02:00:38" — the stable load's time over both parts (2026-09-22 15:00)
        import json, tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as d:
            one, tree, state = Path(d) / "one", Path(d) / "one/.build/trees/145", Path(d) / "state"
            for root in (one, tree):
                (root / "theories").mkdir(parents=True)
                (root / "tools").mkdir(parents=True)
            state.mkdir()
            write = lambda p, text: (p.write_text(text), manifest.digest(str(p)))[1]
            loaded_stable = write(one / "theories/S.thy", "stable as loaded")
            write(one / "theories/S.thy", "stable changed in main")
            write(tree / "theories/S.thy", "stable changed in main")
            loaded_tool = write(one / "tools/t.py", "tool as the layer loaded it")
            write(tree / "tools/t.py", "the tool as the older tree holds it")
            loaded_index = write(state / "names.md", "an index only the one tree has")
            (state / "stable.json").write_text(json.dumps({"taken": "2026-09-22T02:00:38", "files": {
                str(one / "theories/S.thy"): loaded_stable}}))
            (state / "layer.json").write_text(json.dumps({"taken": "2026-09-22T14:55:59", "files": {  # and, as a
                str(one / "theories/S.thy"): loaded_stable,                    # kept layer record does, the stable's
                str(one / "tools/t.py"): loaded_tool, str(one / "names.md"): loaded_index}}))
            (one / "names.md").write_text("an index only the one tree has")
            files = [("", str(tree / "theories/S.thy")), ("", str(tree / "tools/t.py"))]
            with patch.object(manifest, "ONE", str(one)), patch.object(manifest, "PROJECT", str(tree)), \
                    patch.object(manifest, "WHO", "xhigh"):
                line = manifest.stale_line([("stable", str(state / "stable.json")), ("layer", str(state / "layer.json"))],
                                           files)
        self.assertIn("since the xhigh stable load of 2026-09-22T02:00:38 (1): S", line)
        self.assertIn("since the xhigh layer load of 2026-09-22T14:55:59 (0): none", line)   # the index is the one tree's
        self.assertIn("differing in your own tree alone (1", line)
        self.assertIn("brings main in with `v2.py bring-main`): t", line)


if __name__ == "__main__":
    unittest.main()
