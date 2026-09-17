#!/usr/bin/env python3
"""Check an isolated source context, optionally reusing immutable proof providers."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import build
import investigate
import proved_code
import proof_contexts
from proof_contexts import accepted_parent


def main():
    if not __debug__:
        raise ValueError('Proof-context checks require Python assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent-project', type=Path)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--session', required=True)
    parser.add_argument('--threads', type=int, default=12)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('roots', nargs='+')
    args = parser.parse_args()
    assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', args.session)
    assert args.threads > 0 and args.timeout > 0
    parent_project = args.parent_project.resolve() if args.parent_project else None
    project, output = args.project.resolve(), args.output.resolve()
    assert not output.exists(), 'Retain previous proof contexts and use a fresh directory.'
    parent = proof_contexts.load_parent(parent_project) if parent_project else proof_contexts._empty_context()
    parent_session, parent_sources, parent_inputs = parent['session'], parent['sources'], parent['inputs']
    original_root = (project / 'ROOT').read_bytes()
    original_root_digest = investigate.digest(original_root)
    project_declaration = proof_contexts.session_declaration_text(original_root.decode())
    if parent['project_declaration'] is not None:
        assert project_declaration == parent['project_declaration'], 'Project session configuration changed.'
    sources, parents = investigate.source_graph(project, [], args.roots)
    reused, rebuilt = proved_code.proved_context_partition(sources, parents, parent_sources)
    assert set(args.roots) & rebuilt
    (output/'theories').mkdir(parents=True)
    (output/'original-sources').mkdir()
    (output/'helper-sources').mkdir()
    (output/'original-ROOT').write_bytes(original_root)
    helper_inputs = {str(Path(module.__file__).resolve()): investigate.file_hash(Path(module.__file__))
                     for module in [build, investigate, proved_code, proof_contexts, investigate.observation_contracts]}
    helper_inputs[str(Path(__file__).resolve())] = investigate.file_hash(Path(__file__))
    for path in helper_inputs:
        (output/'helper-sources'/Path(path).name).write_bytes(Path(path).read_bytes())
    effective = {}
    for name, source in sources.items():
        (output/'original-sources'/(name+'.thy')).write_text(source['text'])
        if name not in rebuilt:
            continue
        text = proof_contexts.rewritten_source(source['text'], name, reused, parent['providers'])
        target = output/'theories'/(name+'.thy')
        target.write_text(text)
        effective[name] = investigate.file_hash(target)
    (output/'ROOT').write_text('session ' + args.session + ' = ' + parent_session + ' +\n'
        '  options [document = false, timeout = ' + str(args.timeout) + ']\n'
        '  sessions "HOL-Library"\n  directories "theories"\n  theories '
        + ' '.join(name for name in args.roots if name in rebuilt) + '\n')
    root_digest = investigate.file_hash(output/'ROOT')
    manifest = {name: source['sha256'] for name, source in sources.items()}
    (output/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    parent_evidence = ({'project':str(parent_project), 'receipt':parent['receipt'],
        'receipt_sha256':parent_inputs[parent['receipt']]}
        if parent_project else {'project':None})
    (output/'parent.json').write_text(json.dumps({'session':parent_session, **parent_evidence,
        'inputs':parent_inputs, 'reused_complete_contexts':sorted(reused),
        'rebuilt_contexts':sorted(rebuilt), 'helper_inputs':helper_inputs}, indent=2)+'\n')
    command = ['isabelle','build','-b','-o','threads='+str(args.threads),'-o','parallel_proofs=0',
               '-o','build_timing_threshold=0']
    for directory in parent['directories']:
        command += ['-d', directory]
    command += ['-D',str(output)]
    started = build.utc_now()
    with (output/'build.log').open('w') as log:
        process = subprocess.run(command, env={**os.environ,'USER_HOME':'/tmp/structural-isabelle'},
                                 stdout=log, stderr=subprocess.STDOUT)
    stable = all(investigate.file_hash(Path(path)) == sha for path, sha in (parent_inputs|helper_inputs).items())
    stable = stable and investigate.current_sources(sources) and investigate.file_hash(output/'ROOT') == root_digest
    stable = stable and (project/'ROOT').read_bytes() == (output/'original-ROOT').read_bytes() == original_root
    stable = stable and all(investigate.file_hash(output/'theories'/(n+'.thy')) == sha for n,sha in effective.items())
    stable = stable and all(investigate.file_hash(output/'original-sources'/(n+'.thy')) == sha for n,sha in manifest.items())
    stable = stable and all(investigate.file_hash(output/'helper-sources'/Path(path).name) == sha for path,sha in helper_inputs.items())
    result = {'status':'accepted' if process.returncode == 0 and stable else 'failed',
        'exit_code':process.returncode, 'sources_unchanged':stable,'sources':manifest,
        'effective_source_hashes':effective, 'root_sha256':root_digest,
        'project_session_declaration':project_declaration, 'original_root_sha256':original_root_digest,
        'checked_theories':len(rebuilt),
        'parent_theories_reused':len(reused), 'roots':args.roots, 'command':command,
        'started_utc':started, 'finished_utc':build.utc_now(), 'log':str(output/'build.log')}
    (output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['sources','effective_source_hashes']},indent=2))
    if result['status'] != 'accepted':
        print((output/'build.log').read_text()[-16000:])
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
