"""Execute an existing investigation from its accepted export and exact subject contract."""
from pathlib import Path
import sys

import investigate
import proved_code
import observation_contracts


def prepare(args, receipt, output, log, kind):
    if not __debug__:
        raise ValueError('Proved investigation checks require Python assertions.')
    theory = investigate.BUILTIN_CASES[kind]['theory'] if kind in investigate.BUILTIN_CASES else investigate.ENGINE_THEORY
    supplied = args.proof.resolve()
    proof, engine, source_paths = proved_code.proved_export(supplied,
        project=investigate.ROOT, required_theories=[theory])
    assert proof['code_target'] in ('Eval', 'SML'), 'Unknown accepted export target.'
    tracked = {str(supplied): investigate.file_hash(supplied),
               str(engine): investigate.file_hash(engine)}
    tools = {str(Path(module.__file__).resolve()): investigate.file_hash(Path(module.__file__))
             for module in tuple(sys.modules.values())
             if getattr(module, '__file__', None)
             and Path(module.__file__).resolve().is_relative_to(Path(__file__).parent)
             and Path(module.__file__).is_file()}
    for path, sha in (source_paths | tools | tracked).items():
        investigate.archive_evidence(output, receipt, 'accepted investigation input', Path(path), sha)
    if kind in investigate.BUILTIN_CASES:
        function = investigate.BUILTIN_CASES[kind]['function']
        contracts = [item for item in proof['subject_contracts']
                     if Path(item['path']).name == function + '.yxml']
        assert len(contracts) == 1, 'Missing or ambiguous original-subject contract.'
        path = Path(contracts[0]['path'])
        assert investigate.file_hash(path) == contracts[0]['sha256']
        contract = observation_contracts.read_contract(path, theory, function)
        receipt['formal_subject_contract'] = {**contract, 'path': str(path), 'sha256': contracts[0]['sha256']}
        tracked[str(path)] = contracts[0]['sha256']
        investigate.archive_evidence(output, receipt, 'checked observation subject contract', path, contracts[0]['sha256'])
    (output / 'proof.json').write_bytes(supplied.read_bytes())
    sources = {Path(path).stem: {'path': path, 'sha256': sha} for path, sha in source_paths.items()}
    receipt.update(engine_theory=theory, code_target=proof['code_target'], engine_sources=sources,
        tools=tools, generated_engine=str(engine), generated_engine_sha256=tracked[str(engine)],
        reused_export_inputs=tracked, accepted_export=str(supplied),
        proof_receipt_sha256=investigate.file_hash(output / 'proof.json'), engine_snapshot=str(output),
        proof_snapshot_hashes={'proof.json': investigate.file_hash(output / 'proof.json')},
        proof_reuse_boundary='The existing accepted export supplies the exact source closure, generated module and '
            'checked original-subject contract. This invocation does not rebuild a proof or infer subject meaning '
            'from a description, operation name or supplied observation table.')
    return engine, investigate.select_poly(args, receipt, log), sources
