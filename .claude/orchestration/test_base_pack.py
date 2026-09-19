"""Preservation and incomplete/corrupt-load controls; no Claude sessions launched."""
import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import base_pack as p
from digest import thy_digest
import manifest
import pack_notation as notation


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
            env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
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
            extension = subprocess.run(["sh", str(p.HERE / "base.sh"), "max", "extend", str(fake)],
                                       env=env, capture_output=True, text=True, timeout=5)
            self.assertEqual(extension.returncode, 3)
            self.assertIn("frozen", extension.stdout)
            self.assertEqual((root / "args.json").read_text(), before)


if __name__ == "__main__":
    unittest.main()
