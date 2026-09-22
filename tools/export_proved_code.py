#!/usr/bin/env python3
"""Export selected code modules from one unchanged accepted proof snapshot."""
from __future__ import annotations

import argparse
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import uuid

import execution_support as investigate
import isabelle_places
import proved_code
import prove_context


def export_context(directory, project, output, modules, module_roots=None):
    """Export from the actual immutable provider session of each current theory."""
    import proof_contexts
    context = proof_contexts.load_parent(directory)
    assert proof_contexts.session_declaration(project) == context['project_declaration'], \
        'Project session configuration changed.'
    requested = {t for t, _ in modules}
    module_roots = {} if module_roots is None else module_roots
    assert isinstance(module_roots, dict), 'Module proof roots must be a mapping.'
    assert set(module_roots) <= requested, 'Proof roots name an unrequested export.'
    assert all(isinstance(roots, list) and all(isinstance(n, str) and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n) for n in roots) for roots in module_roots.values())
    requirements = {t: {t, *module_roots.get(t, [])} for t in requested}
    required = set().union(*requirements.values())
    declared = set(re.findall(r'^    ([A-Za-z_][A-Za-z_0-9]*)\s*$', (project / 'ROOT').read_text(), re.M))
    assert required <= declared, 'Requested export is not declared in the project.'
    source_rows, graph = investigate.source_graph(project, [], sorted(required))
    reused, _ = proved_code.proved_context_partition(source_rows, graph, context['sources'])
    assert required <= reused, 'Requested export does not have a current complete proof context.'
    sources = {n: source_rows[n]['sha256'] for n in reused}
    tracked = context['inputs'] | {source_rows[n]['path']: sources[n] for n in reused}
    tracked[str(project / 'ROOT')] = investigate.file_hash(project / 'ROOT')
    tracked |= {str(Path(m.__file__).resolve()): investigate.file_hash(Path(m.__file__))
                for m in (investigate, proved_code, proof_contexts)}
    tracked[str(Path(__file__).resolve())] = investigate.file_hash(Path(__file__))
    assert not output.exists()
    output.mkdir(parents=True)
    report = {'status': 'failed', 'source_project': str(project), 'proof_context': str(directory),
              'execution_inputs': tracked, 'exports': []}
    groups = {}
    for theory, filename in modules:
        provider = context['providers'][theory]
        groups.setdefault(provider['session'], []).append((theory, filename, provider))
    try:
        for session, members in groups.items():
            command = ['isabelle', 'export', '-n']
            for parent in context['directories']:
                command += ['-d', parent]
            destination = output / 'code' / session
            command += ['-O', str(destination)]
            for theory, filename, provider in members:
                command += ['-x', provider['theory'] + ':code/' + filename,
                            '-x', provider['theory'] + ':subjects/*.yxml']
            command += [session]
            log = output / (session + '-export.log')
            with log.open('w') as stream:
                done = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                                      env=proof_contexts.ENV, timeout=60)
            assert done.returncode == 0, 'Export failed: ' + str(log)
            for theory, filename, provider in members:
                paths = [p for p in destination.rglob(filename)
                         if p.parent.name == 'code' and p.parent.parent.name == provider['theory']]
                assert len(paths) == 1, (theory, filename, paths)
                path = paths[0]
                contracts = [{'path': str(p), 'sha256': investigate.file_hash(p)}
                             for p in sorted((path.parent.parent / 'subjects').glob('*.yxml'))]
                text = (project / 'theories' / (theory + '.thy')).read_text()
                targets = re.findall(r'\bin\s+(Eval|SML)\s+module_name\s+\S+\s+file_prefix\s+"?'
                                     + re.escape(path.stem) + r'"?(?=\s|$)', text)
                assert len(targets) == 1
                entry = {'path': str(path), 'sha256': investigate.file_hash(path)}
                module_closure = investigate.import_contexts(graph, requirements[theory])
                module_sources = {n: sources[n] for n in module_closure}
                derived = {'status': 'accepted', 'exit_code': 0, 'sources_unchanged': True,
                           'sources': module_sources, 'effective_source_hashes': {},
                           'roots': sorted(requirements[theory]), 'checked_theories': len(module_sources),
                           'parent_theories_reused': len(module_sources), 'exports': [entry],
                           'subject_contracts': contracts, 'code_target': targets[0],
                           'complete_artifact_transport': 'complete_artifact_reference' in path.read_text(),
                           'complete_term_transport': 'complete_term_reference' in path.read_text(),
                           'export_theory': theory, 'export_command': command, 'export_exit_code': 0,
                           'export_log': str(log), 'export_log_sha256': investigate.file_hash(log),
                           'proof_context': {'path': context['receipt'],
                               'sha256': investigate.file_hash(Path(context['receipt'])),
                               'provider': provider},
                           'proof_boundary': 'Every supplied source has its unchanged entire import context '
                               'in the accepted provider graph; code was exported from its actual provider session.'}
                receipt = output / (path.stem + '.proof.json')
                receipt.write_text(json.dumps(derived, indent=2) + '\n')
                report['exports'].append({'theory': theory, **entry, 'proof': str(receipt),
                                          'proof_sha256': investigate.file_hash(receipt)})
        assert all(investigate.file_hash(Path(p)) == h for p, h in tracked.items()), 'Export inputs changed.'
        report.update(status='accepted', sources_and_tools_unchanged=True)
    except Exception as error:
        report['error'] = repr(error)
    (output / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'execution_inputs'}))
    return int(report['status'] != 'accepted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--proof", type=Path)
    source.add_argument("--context", type=Path, help="Export from an accepted graph of immutable proof providers.")
    source.add_argument("--main-project", type=Path,
                        help="Export directly from a fully checked unchanged main session.")
    parser.add_argument("--project", type=Path, default=proved_code.ROOT)
    parser.add_argument("--module-roots", type=json.loads, default={}, help="Additional client proof roots for each context-export theory.")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--module", action="append", required=True, metavar="THEORY:FILENAME")
    args = parser.parse_args()
    output = args.output.resolve()
    modules = [value.split(":") for value in args.module]
    assert all(len(row) == 2 and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", row[0])
               and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*\.ML", row[1]) for row in modules)
    assert len({name for _, name in modules}) == len(modules)
    if args.context:
        return export_context(args.context.resolve(), args.project.resolve(), output, modules, args.module_roots)
    assert not args.module_roots, "Additional proof roots require --context."
    if args.main_project:
        project = args.main_project.resolve()
        session, accepted_sources, parent_inputs = prove_context.accepted_parent(project)
        proof_path = project / 'validation/build.json'
        main = json.loads(proof_path.read_text())
        assert all(t in accepted_sources for t, _ in modules)
        proof = {'status': 'accepted', 'exit_code': 0, 'sources_unchanged': True,
                 'sources': accepted_sources, 'effective_source_hashes': accepted_sources,
                 'checked_theories': len(accepted_sources), 'parent_theories_reused': 0,
                 'roots': [t for t, _ in modules], 'command': main['command'],
                 'main_proof_inputs': parent_inputs,
                 'proof_boundary': 'The unchanged complete main build and source checks were verified by accepted_parent.'}
        sources = {str(project / 'theories' / (n + '.thy')): sha for n, sha in accepted_sources.items()}
        snapshot = project
    else:
        project = args.project.resolve()
        proof_path = args.proof.resolve()
        proof, sources = proved_code.accepted_proof(proof_path, project=project,
                                                   required_theories=[t for t, _ in modules])
        snapshot = proof_path.parent
    effective = {str(snapshot / "theories" / (name + ".thy")): sha
                 for name, sha in proof["effective_source_hashes"].items()}
    assert all(investigate.file_hash(Path(p)) == sha for p, sha in effective.items())
    original = proof_path.read_bytes()
    root_file = snapshot / "ROOT"
    session = re.search(r"^session (\S+) =", root_file.read_text()).group(1)
    tracked = {str(p.resolve()): investigate.file_hash(p) for p in
               [proof_path, root_file, Path(__file__), Path(proved_code.__file__),
                Path(investigate.__file__)]} | sources | effective
    tracked.update(proof.get('main_proof_inputs', {}))
    assert not output.exists(), "Retain preceding exports and use a new directory."
    output.mkdir(parents=True)
    report = {"status": "failed", "invocation": str(uuid.uuid4()),
              "source_project": str(project),
              "proof": str(proof_path), "proof_sha256": investigate.digest(original),
              "session": session, "execution_inputs": tracked}
    command = ["isabelle", "export", "-n"]
    build_command = proof.get('command', [])
    for i, item in enumerate(build_command[:-1]):
        if item == '-d' and Path(build_command[i + 1]).resolve() != snapshot:
            parent_directory = Path(build_command[i + 1]).resolve()
            command += ['-d', str(parent_directory)]
            tracked[str(parent_directory / 'ROOT')] = investigate.file_hash(parent_directory / 'ROOT')
    command += ["-d", str(snapshot), "-O", str(output / "code")]
    for theory, filename in modules:
        command += ["-x", f"*.{theory}:code/{filename}"]
        command += ["-x", f"*.{theory}:subjects/*.yxml"]
    command.append(session)
    report["command"] = command
    log_path = output / "export.log"
    try:
        with log_path.open("w") as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                                    env={**os.environ, "USER_HOME": str(isabelle_places.USER_HOME)}, timeout=60)
        report["exit_code"] = result.returncode
        assert result.returncode == 0, "See the retained export.log."
        assert proof_path.read_bytes() == original
        assert all(investigate.file_hash(Path(p)) == sha for p, sha in tracked.items())
        exports = []
        for theory, filename in modules:
            paths = [p for p in (output / "code").rglob(filename)
                     if p.parent.name == 'code' and p.parent.parent.name.endswith('.' + theory)]
            assert len(paths) == 1, (theory, filename, paths)
            path = paths[0]
            entry = {"path": str(path), "sha256": investigate.file_hash(path)}
            contracts = [{"path": str(p), "sha256": investigate.file_hash(p)}
                         for p in sorted((path.parent.parent / "subjects").glob("*.yxml"))]
            derived = copy.deepcopy(proof)
            original_theory = (project / 'theories' / (theory + '.thy')).read_text()
            targets = re.findall(r'\bin\s+(Eval|SML)\s+module_name\s+\S+\s+file_prefix\s+"?'
                                 + re.escape(path.stem) + r'"?(?=\s|$)', original_theory)
            assert len(targets) == 1, 'Expected one declared target for the exported module.'
            derived.update(exports=[entry], subject_contracts=contracts,
                           code_target=targets[0],
                           complete_artifact_transport='complete_artifact_reference' in path.read_text(),
                           complete_term_transport='complete_term_reference' in path.read_text(),
                           export_theory=theory, export_command=command,
                           pre_export_receipt_sha256=investigate.digest(original),
                           export_exit_code=0, export_log=str(log_path),
                           export_log_sha256=investigate.file_hash(log_path))
            receipt = output / (path.stem + ".proof.json")
            receipt.write_text(json.dumps(derived, indent=2) + "\n")
            exports.append({"theory": theory, **entry, "proof": str(receipt),
                            "proof_sha256": investigate.file_hash(receipt)})
        report.update(status="accepted", sources_and_tools_unchanged=True, exports=exports,
                      log_sha256=investigate.file_hash(log_path))
    except Exception as error:
        report["error"] = str(error)
    (output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "execution_inputs"}, indent=2))
    return int(report["status"] != "accepted")


if __name__ == "__main__":
    raise SystemExit(main())
