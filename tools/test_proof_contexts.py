"""Refuse stale or conflated proof providers before any reusable context is used."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import execution_support as investigate
import proof_contexts as contexts


class ProviderGraphTests(unittest.TestCase):
    def setUp(self):
        self.parent = {'sources': {'A': 'a1', 'B': 'b1', 'C': 'c1', 'D': 'd1'},
                       'imports': {'A': ['Main'], 'B': ['A'], 'C': ['B'], 'D': ['Main']},
                       'providers': {n: {'session': 'Old', 'directory': '/old', 'theory': 'Old.' + n}
                                     for n in ('A', 'B', 'C', 'D')}}

    def test_changed_ancestor_invalidates_unchanged_descendants(self):
        sources, graph, providers = contexts.extend_providers(
            self.parent, {'A': 'a2'}, {'A': ['Main']}, {'A'}, Path('/new'), 'New')
        self.assertEqual(sources, {'A': 'a2', 'D': 'd1'})
        self.assertEqual(providers['A']['theory'], 'New.A')
        self.assertEqual(providers['D']['theory'], 'Old.D')

    def test_rebuilt_descendant_uses_its_new_provider(self):
        sources, _, providers = contexts.extend_providers(
            self.parent, {'A': 'a2', 'B': 'b1'}, {'A': ['Main'], 'B': ['A']},
            {'A', 'B'}, Path('/new'), 'New')
        self.assertEqual(set(sources), {'A', 'B', 'D'})
        self.assertEqual(providers['B']['theory'], 'New.B')

    def test_changed_leaf_preserves_unrelated_contexts(self):
        sources, _, providers = contexts.extend_providers(
            self.parent, {'A': 'a1', 'B': 'b1', 'C': 'c2'}, self.parent['imports'],
            {'C'}, Path('/new'), 'New')
        self.assertEqual(set(sources), {'A', 'B', 'C', 'D'})
        self.assertEqual(providers['B']['theory'], 'Old.B')
        self.assertEqual(providers['C']['theory'], 'New.C')


class RetainedContextTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix='proof-context-test-')
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / 'proof'
        self.project = Path(tmp.name) / 'project'
        for p in (self.root / 'theories', self.root / 'original-sources', self.root / 'helper-sources',
                  self.project / 'theories'):
            p.mkdir(parents=True)
        self.source = 'theory Fixture\n imports Main\nbegin\nlemma accepted: True by simp\nend\n'
        self.effective = contexts.rewritten_source(self.source, 'Fixture', set(), {})
        (self.root / 'original-sources/Fixture.thy').write_text(self.source)
        (self.root / 'theories/Fixture.thy').write_text(self.effective)
        (self.project / 'theories/Fixture.thy').write_text(self.source)
        (self.project / 'ROOT').write_text('session Project = HOL +\n  theories\n    Fixture\n')
        (self.root / 'ROOT').write_text('session Fixture_Proof = HOL +\n options [document=false]\n directories theories\n theories Fixture\n')
        self.sources = {'Fixture': investigate.file_hash(self.root / 'original-sources/Fixture.thy')}
        self.proof = {'status': 'accepted', 'exit_code': 0, 'sources_unchanged': True,
                      'sources': self.sources, 'effective_source_hashes': {'Fixture': investigate.file_hash(self.root / 'theories/Fixture.thy')},
                      'roots': ['Fixture'], 'checked_theories': 1, 'parent_theories_reused': 0,
                      'command': ['isabelle', 'build', '-b', '-D', str(self.root)]}
        helpers = {}
        for n in ('build.py', 'investigate.py', 'proved_code.py', 'observation_contracts.py', 'prove_context.py'):
            p = self.root / 'helper-sources' / n
            p.write_text('# retained fixture helper\n')
            helpers['/original/tools/' + n] = investigate.file_hash(p)
        self.parent = {'project': None, 'session': 'HOL', 'inputs': {}, 'helper_inputs': helpers,
                       'reused_complete_contexts': [], 'rebuilt_contexts': ['Fixture']}
        self.stored = {'heap': '/fixture/heap', 'heap_sha256': 'heap', 'database': '/fixture/database', 'database_sha256': 'db'}
        self.save()

    def save(self):
        for n, d in [('result.json', self.proof), ('parent.json', self.parent), ('manifest.json', self.sources)]:
            (self.root / n).write_text(json.dumps(d))

    def adopt(self):
        with patch.object(contexts, 'verify_currency', return_value=self.stored), \
                patch.object(contexts, 'heap_identity', return_value=self.stored):
            return contexts.adopt_proof_context(self.root, self.project)

    def load(self):
        with patch.object(contexts, 'heap_identity', return_value=self.stored):
            return contexts.load_parent(self.root)

    def test_current_context_records_actual_provider(self):
        c = self.adopt()
        self.assertEqual(c['providers']['Fixture']['theory'], 'Fixture_Proof.Fixture')
        self.assertEqual(c['sources'], self.sources)
        self.assertEqual(self.load()['sources'], self.sources)

    def test_modified_original_or_checked_source_is_rejected(self):
        self.adopt()
        for name in ('original-sources/Fixture.thy', 'theories/Fixture.thy', 'ROOT', 'helper-sources/build.py'):
            with self.subTest(name=name):
                p = self.root / name
                original = p.read_bytes()
                p.write_bytes(original + b'changed\n')
                with self.assertRaises(AssertionError): self.load()
                p.write_bytes(original)

    def test_forged_provider_is_rejected(self):
        self.adopt()
        p = self.root / contexts.CONTEXT_FILE
        d = json.loads(p.read_text())
        d['providers']['Fixture']['theory'] = 'Wrong.Fixture'
        p.write_text(json.dumps(d))
        with self.assertRaises(AssertionError): self.load()

    def test_missing_helper_inventory_is_rejected(self):
        self.parent['helper_inputs'].pop('/original/tools/build.py')
        self.save()
        with self.assertRaises(AssertionError): self.adopt()

    def test_replaced_heap_is_rejected(self):
        self.adopt()
        self.stored = self.stored | {'heap_sha256': 'replacement'}
        with self.assertRaises(AssertionError): self.load()

    def test_failed_or_incomplete_proof_is_rejected(self):
        for key, bad in [('status', 'failed'), ('exit_code', 1), ('sources_unchanged', False),
                         ('checked_theories', 0), ('effective_source_hashes', {})]:
            with self.subTest(key=key):
                old = self.proof[key]
                self.proof[key] = bad
                self.save()
                with self.assertRaises(AssertionError): self.adopt()
                self.proof[key] = old
                self.save()

    def test_dependency_requalification_cannot_change_a_body(self):
        source = self.root / 'theories/Fixture.thy'
        source.write_text(self.effective.replace('True', 'False'))
        self.proof['effective_source_hashes']['Fixture'] = investigate.file_hash(source)
        self.save()
        with self.assertRaises(AssertionError): self.adopt()

    def test_changed_project_configuration_is_rejected(self):
        self.proof['project_session_declaration'] = contexts.session_declaration(self.project)
        self.save()
        p = self.project / 'ROOT'
        p.write_text(p.read_text().replace('= HOL +', '= Pure +'))
        with self.assertRaises(AssertionError): self.adopt()

    def test_retained_original_configuration_is_checked(self):
        p = self.root / 'original-ROOT'
        p.write_bytes((self.project / 'ROOT').read_bytes())
        self.proof['original_root_sha256'] = investigate.file_hash(p)
        self.proof['project_session_declaration'] = contexts.session_declaration(self.project)
        self.save()
        self.adopt()
        p.write_text(p.read_text().replace('= HOL +', '= Pure +'))
        with self.assertRaises(AssertionError): self.load()

    def test_heapless_context_is_identified_by_its_database(self):
        self.proof['command'] = ['isabelle', 'build', '-D', str(self.root)]
        self.proof['stored_heap'] = False
        self.save()
        stored = {'database': '/fixture/database', 'database_sha256': 'db'}
        with patch.object(contexts, 'verify_currency', return_value=stored), \
                patch.object(contexts, 'session_identity', return_value=stored):
            adopted = contexts.adopt_proof_context(self.root, self.project)
            loaded = contexts.load_parent(self.root)
        self.assertFalse(adopted['stored_heap'])
        self.assertEqual(loaded['inputs']['/fixture/database'], 'db')
        self.assertNotIn('/fixture/heap', loaded['inputs'])

    def test_recorded_heap_storage_must_match_the_build(self):
        self.proof['stored_heap'] = False
        self.save()
        with self.assertRaises(AssertionError): self.adopt()

    def test_heapless_context_cannot_be_a_parent(self):
        parent = contexts._empty_context() | {'stored_heap': False}
        with self.assertRaises(AssertionError):
            contexts._proof_claims(self.root, parent, contexts.session_declaration(self.project))

    def test_optimized_adoption_rejects_before_reading_inputs(self):
        result = subprocess.run([sys.executable, '-B', '-O', '-c',
            "import proof_contexts; proof_contexts.adopt_proof_context('/missing-proof', '/missing-project')"],
            cwd=Path(__file__).parent, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires Python assertions', result.stderr)


if __name__ == '__main__':
    unittest.main()
