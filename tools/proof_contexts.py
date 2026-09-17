"""Reuse exact Isabelle proof contexts at their immutable source paths.

A context records the actual provider of each unchanged import context. Replacing
an ancestor invalidates its old dependents even when their own text is unchanged.
Stored hashes identify accepted proof artifacts; they do not confer new semantics.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

import execution_support as investigate
import proved_code

USER_HOME = Path('/tmp/structural-isabelle')
ENV = {**os.environ, 'USER_HOME': str(USER_HOME)}
CONTEXT_FILE = 'accepted-context.json'


def session_declaration(project):
    return session_declaration_text((project / 'ROOT').read_text())


def session_declaration_text(text):
    return re.sub(r'^    [A-Za-z_][A-Za-z_0-9]*\s*\n', '', text, flags=re.M)


class VerificationPass:
    """What one verification of accepted lineages has read.

    Each distinct file is read and digested once. A retained theory text whose digest was checked is
    scanned for proof escapes and imports once per name and digest, since equal digests are equal texts.
    """

    def __init__(self):
        self.digests, self.theories = {}, {}

    def digest(self, path):
        key = str(path)
        if key not in self.digests:
            self.digests[key] = investigate.file_hash(Path(path))
        return self.digests[key]

    def present_digest(self, path):
        key = str(path)
        if key in self.digests:
            return self.digests[key]
        return self.digest(path) if Path(path).is_file() else None

    def retained_theory(self, name, sha, path):
        assert self.digest(path) == sha
        if (name, sha) not in self.theories:
            text = Path(path).read_text()
            assert not re.search(r'\b(sorry|oops|axiomatization)\b', text), 'Proof escape in retained source: ' + name
            self.theories[(name, sha)] = (text, investigate.theory_imports(text, name))
        return self.theories[(name, sha)]


def new_lineage():
    """Verified contexts by directory, and the verification pass that established them."""
    return {}, VerificationPass()


def heap_identity(session, verification=None):
    heaps = sorted(USER_HOME.glob('.isabelle/*/heaps/*/' + session))
    databases = sorted(USER_HOME.glob('.isabelle/*/heaps/*/log/' + session + '.db'))
    assert len(heaps) == len(databases) == 1, 'Accepted heap/database missing: ' + session
    digest = verification.digest if verification is not None else investigate.file_hash
    return {'heap': str(heaps[0]), 'heap_sha256': digest(heaps[0]),
            'database': str(databases[0]), 'database_sha256': digest(databases[0])}


def session_identity(session, stored_heap=True, verification=None):
    """A session with a stored heap is its heap and database; one without a heap is its database alone."""
    if stored_heap:
        return heap_identity(session, verification)
    heaps = sorted(USER_HOME.glob('.isabelle/*/heaps/*/' + session))
    databases = sorted(USER_HOME.glob('.isabelle/*/heaps/*/log/' + session + '.db'))
    assert not heaps and len(databases) == 1, 'Accepted database missing or unexpected heap: ' + session
    digest = verification.digest if verification is not None else investigate.file_hash
    return {'database': str(databases[0]), 'database_sha256': digest(databases[0])}


def _checked_hashes(paths, verification=None):
    verification = verification or VerificationPass()
    assert all(verification.present_digest(p) == h for p, h in paths.items()), \
        'Accepted context input changed or disappeared.'


def rewritten_source(text, name, reused, providers):
    header = re.match(r'(\s*theory\s+\S+\s+imports\s+)([\s\S]*?)(\s+begin\b)', text)
    assert header, 'Unrecognized theory header: ' + name
    imports = investigate.theory_imports(text, name)
    names = [providers[n]['theory'] if n in reused else n for n in imports]
    return header[1] + ' '.join('"' + n + '"' for n in names) + header[3] + text[header.end():]


def extend_providers(parent, sources, imports, rebuilt, directory, session):
    """Discard an old provider whenever any part of its original context changed."""
    changed = {n for n, h in sources.items() if parent['sources'].get(n) != h}
    unchanged = investigate.contexts_satisfying(parent['imports'], lambda n: n not in changed)
    keep = {n for n in parent['sources'] if unchanged.get(n, True)}
    complete = {n: parent['sources'][n] for n in keep}
    graph = {n: parent['imports'][n] for n in keep}
    providers = {n: parent['providers'][n] for n in keep}
    for n in rebuilt:
        complete[n] = sources[n]
        graph[n] = imports[n]
        providers[n] = {'session': session, 'directory': str(directory), 'theory': session + '.' + n}
    assert set(sources) <= set(complete), 'A reused context lost its actual provider.'
    assert all(complete[n] == h for n, h in sources.items())
    return complete, graph, providers


def _empty_context():
    return {'session': 'HOL', 'sources': {}, 'imports': {}, 'providers': {}, 'stored_heap': True,
            'directories': [], 'inputs': {}, 'project_declaration': None, 'receipt': None}


def accepted_main_parent(project):
    if not __debug__:
        raise ValueError("Parent proof checks require Python assertions.")
    receipt_path = project / 'validation/build.json'
    check_path = project / 'validation/check.json'
    receipt = json.loads(receipt_path.read_text())
    checked = json.loads(check_path.read_text())
    assert receipt['status'] == checked['status'] == 'accepted'
    assert receipt['exit_code'] == checked['exit_code'] == 0
    assert receipt['sources_unchanged'] and receipt['tools_unchanged']
    assert checked['sources_and_tools_unchanged'] and checked['build_evidence'] == receipt
    assert receipt['invocation'] == checked['invocation']
    assert all(not checked[k] for k in ['missing_theory_files', 'unlisted_theories', 'proof_escape_matches'])
    command = receipt['command']
    assert '-D' in command and Path(command[command.index('-D') + 1]).resolve() == project
    names = set(re.findall(r'^    ([A-Za-z_][A-Za-z_0-9]*)\s*$', (project/'ROOT').read_text(), re.M))
    expected = {'ROOT'} | {'theories/' + name + '.thy' for name in names}
    assert set(receipt['sources']) == expected
    assert set(receipt['tools']) == {'tools/build.py', 'tools/check.py'}
    assert checked['theory_count'] == len(names)
    inputs = {str(project/path): sha for path, sha in receipt['sources'].items()}
    inputs.update({str(project/path): sha for path, sha in receipt['tools'].items()})
    inputs.update({str(receipt_path): investigate.file_hash(receipt_path),
                   str(check_path): investigate.file_hash(check_path),
                   str(project/'validation/build.log'): receipt['log_sha256']})
    assert all(investigate.file_hash(Path(path)) == sha for path, sha in inputs.items())
    session = re.search(r'^session (\S+) =', (project/'ROOT').read_text()).group(1)
    return session, {Path(path).stem: sha for path, sha in receipt['sources'].items() if path != 'ROOT'}, inputs



def _proof_claims(directory, parent, project_declaration, verification=None):
    verification = verification or VerificationPass()
    proof_path = directory / 'result.json'
    proof = json.loads(proof_path.read_text())
    evidence = json.loads((directory / 'parent.json').read_text())
    assert proof['status'] == 'accepted' and proof['exit_code'] == 0 and proof['sources_unchanged']
    if 'project_session_declaration' in proof:
        assert proof['project_session_declaration'] == project_declaration, 'Project session configuration changed.'
    if parent['project_declaration'] is not None:
        assert parent['project_declaration'] == project_declaration, 'Parent session configuration changed.'
    assert evidence['session'] == parent['session']
    assert set(evidence['inputs']) <= set(parent['inputs'])
    assert all(parent['inputs'][p] == h for p, h in evidence['inputs'].items())
    sources = proof['sources']
    assert json.loads((directory / 'manifest.json').read_text()) == sources
    roots = proof['roots']
    assert set(roots) <= set(sources)
    command = proof['command']
    assert '-D' in command and Path(command[command.index('-D') + 1]).resolve() == directory
    # A proof that stored no heap exports its theories but supplies no import context.
    stored_heap = proof.get('stored_heap', True)
    assert stored_heap == ('-b' in command), 'Recorded heap storage differs from the build command.'
    assert parent.get('stored_heap', True), 'A context without a stored heap cannot be a parent.'
    root_text = (directory / 'ROOT').read_text()
    match = re.match(r'session (\w+) = (\w+) \+', root_text)
    assert match and match[2] == parent['session']
    session = match[1]
    if 'root_sha256' in proof:
        assert verification.digest(directory / 'ROOT') == proof['root_sha256']
    tracked = {str(directory / f): verification.digest(directory / f)
               for f in ('ROOT', 'result.json', 'parent.json', 'manifest.json')}
    if 'original_root_sha256' in proof:
        original_root = directory / 'original-ROOT'
        assert verification.digest(original_root) == proof['original_root_sha256']
        assert session_declaration_text(original_root.read_text()) == project_declaration
        tracked[str(original_root)] = proof['original_root_sha256']
    graph, texts = {}, {}
    for n, sha in sources.items():
        assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n)
        source = directory / 'original-sources' / (n + '.thy')
        texts[n], graph[n] = verification.retained_theory(n, sha, source)
        tracked[str(source)] = sha
    closure = investigate.import_contexts(graph, roots)
    assert closure == set(sources), 'Incomplete or extraneous proof source closure.'
    reused, rebuilt = proved_code.proved_context_partition(
        {n: {'sha256': h} for n, h in sources.items()}, graph, parent['sources'])
    assert set(evidence['reused_complete_contexts']) == reused
    assert set(evidence['rebuilt_contexts']) == rebuilt
    assert proof['checked_theories'] == len(rebuilt)
    assert proof['parent_theories_reused'] == len(reused)
    assert set(proof['effective_source_hashes']) == rebuilt
    for n in rebuilt:
        path = directory / 'theories' / (n + '.thy')
        assert path.read_text() == rewritten_source(texts[n], n, reused, parent['providers'])
        sha = proof['effective_source_hashes'][n]
        assert verification.digest(path) == sha
        tracked[str(path)] = sha
    helper_names = {Path(name).name for name in evidence['helper_inputs']}
    assert {'build.py', 'proved_code.py', 'observation_contracts.py', 'prove_context.py'} <= helper_names \
        and helper_names & {'investigate.py', 'execution_support.py'}, 'Incomplete retained proof-tool inventory.'
    for name, sha in evidence['helper_inputs'].items():
        path = directory / 'helper-sources' / Path(name).name
        assert verification.digest(path) == sha
        tracked[str(path)] = sha
    complete, imports, providers = extend_providers(parent, sources, graph, rebuilt, directory, session)
    return {'kind': 'proof_context', 'session': session, 'sources': complete, 'imports': imports,
            'providers': providers, 'stored_heap': stored_heap, 'directories': [*parent['directories'], str(directory)],
            'inputs': parent['inputs'] | tracked, 'project_declaration': project_declaration,
            'receipt': str(proof_path)}


def load_parent(project, _active=None, _memo=None, _verification=None):
    """Verify an accepted lineage once: every level's claims, and every distinct input read once.

    A caller that continues with the same lineage passes the same memo and digests, so a later load
    in that process does not repeat the verification of levels it has already verified.
    """
    if not __debug__:
        raise ValueError('Parent proof checks require Python assertions.')
    project = Path(project).resolve()
    active = set() if _active is None else _active
    memo = {} if _memo is None else _memo
    verification = VerificationPass() if _verification is None else _verification
    assert project not in active, 'Cyclic proof context lineage.'
    if project in memo:
        return memo[project]
    active.add(project)
    path = project / CONTEXT_FILE
    if path.exists():
        saved = json.loads(path.read_text())
        assert saved['version'] == 1
        parent = load_parent(saved['parent'], active, memo, verification) if saved['parent'] else _empty_context()
        current = _proof_claims(project, parent, saved['project_declaration'], verification)
        for key in ('session', 'sources', 'imports', 'providers', 'directories', 'inputs', 'receipt'):
            assert current[key] == saved[key], 'Context claim changed: ' + key
        assert saved['stored'] == session_identity(current['session'], current['stored_heap'], verification), \
            'Accepted heap/database changed.'
        _checked_hashes(current['inputs'], verification)
        current['inputs'] = current['inputs'] | {str(path): verification.digest(path)} | {
            saved['stored'][part]: saved['stored'][part + '_sha256'] for part in ('heap', 'database')
            if part in saved['stored']}
        current['receipt'] = str(path)
    else:
        session, sources, inputs = accepted_main_parent(project)
        stored = json.loads((project / 'base.json').read_text()) if (project / 'base.json').is_file() else None
        if stored:
            assert stored['session'] == session and stored['stored'] == heap_identity(session, verification)
            inputs |= {str(project / 'base.json'): investigate.file_hash(project / 'base.json'),
                       stored['stored']['heap']: stored['stored']['heap_sha256'],
                       stored['stored']['database']: stored['stored']['database_sha256']}
        graph = {n: investigate.theory_imports((project / 'theories' / (n + '.thy')).read_text(), n)
                 for n in sources}
        current = {'kind': 'main', 'session': session, 'sources': sources, 'imports': graph, 'stored_heap': True,
                   'providers': {n: {'session': session, 'directory': str(project), 'theory': session + '.' + n}
                                 for n in sources}, 'directories': [str(project)], 'inputs': inputs,
                   'project_declaration': session_declaration(project),
                   'receipt': str(project / 'validation/build.json')}
    active.remove(project)
    memo[project] = current
    return current


def accepted_parent(project):
    # Preserve the legacy API and its exact traditional input inventory.
    if not (Path(project) / CONTEXT_FILE).exists():
        return accepted_main_parent(project)
    context = load_parent(project)
    return context['session'], context['sources'], context['inputs']


def _verify_session_payload(stored, session, stored_heap):
    import sqlite3
    if not stored_heap:
        with sqlite3.connect('file:' + stored['database'] + '?mode=ro', uri=True) as connection:
            rows = connection.execute('select session_name, return_code, output_heap from isabelle_session_info').fetchall()
        assert rows == [(session, 0, '')], 'Database does not record a successful build without a heap.'
        return
    path = Path(stored['heap'])
    size = path.stat().st_size
    with path.open('rb') as f:
        f.seek(-45, 2)
        footer = f.read(45)
        assert footer.startswith(b'SHA1:')
        expected = footer[5:].decode('ascii')
        f.seek(0)
        digest = hashlib.sha1()
        remaining = size - 45
        while remaining:
            block = f.read(min(1 << 20, remaining))
            assert block
            digest.update(block)
            remaining -= len(block)
    assert digest.hexdigest() == expected, 'Stored heap payload is corrupt.'
    with sqlite3.connect('file:' + stored['database'] + '?mode=ro', uri=True) as connection:
        rows = connection.execute('select session_name, return_code, output_heap from isabelle_session_info').fetchall()
    assert rows == [(session, 0, expected + ' ' + session + '\n')], 'Heap does not match the successful build.'


def verify_currency(directory, context):
    """Explicitly select the session and require its stored heap, if it stored one; never build it."""
    proof = json.loads((directory / 'result.json').read_text())
    stored_heap = context['stored_heap']
    before = session_identity(context['session'], stored_heap)
    _verify_session_payload(before, context['session'], stored_heap)
    command = ['isabelle', 'build', '-n'] + (['-b'] if stored_heap else [])
    for i, value in enumerate(proof['command'][:-1]):
        if value == '-o':
            option = proof['command'][i + 1]
            assert option.startswith(('threads=', 'parallel_proofs=', 'build_timing_threshold='))
            command += ['-o', option]
    for parent in context['directories']:
        command += ['-d', parent]
    command += [context['session']]
    run = subprocess.run(command, env=ENV, capture_output=True, text=True, timeout=120)
    (directory / 'context-currency.log').write_text(run.stdout + run.stderr)
    assert run.returncode == 0, 'Stored context is not current; see context-currency.log.'
    assert before == session_identity(context['session'], stored_heap), \
        'Read-only currency check changed the heap/database.'
    return before


def adopt_proof_context(directory, project, _memo=None, _verification=None):
    if not __debug__:
        raise ValueError('Proof-context adoption requires Python assertions.')
    directory, project = Path(directory).resolve(), Path(project).resolve()
    assert not (directory / CONTEXT_FILE).exists(), 'An accepted context is immutable.'
    verification = VerificationPass() if _verification is None else _verification
    evidence = json.loads((directory / 'parent.json').read_text())
    parent_dir = evidence.get('project')
    parent = load_parent(parent_dir, None, _memo, verification) if parent_dir else _empty_context()
    declaration = session_declaration(project)
    if parent['project_declaration'] is not None:
        assert declaration == parent['project_declaration'], 'Project session configuration changed.'
    current = _proof_claims(directory, parent, declaration, verification)
    # Bind the original project configuration and actual provided original files.
    proof = json.loads((directory / 'result.json').read_text())
    assert all(verification.digest(project / 'theories' / (n + '.thy')) == h
               for n, h in proof['sources'].items()), 'The accepted source project changed.'
    stored = verify_currency(directory, current)
    _checked_hashes(current['inputs'], verification)
    saved = {'version': 1, 'parent': parent_dir, **current, 'stored': stored}
    (directory / CONTEXT_FILE).write_text(json.dumps(saved, sort_keys=True, separators=(',', ':')) + '\n')
    return load_parent(directory, None, _memo, verification)
