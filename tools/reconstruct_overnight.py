"""Rebuild the consolidated partial theory scope from HOL, then replay its requests.

No overnight temporary provider, active-context pointer, or old heap is consulted.
The known Development_Seed failure is outside this explicitly partial scope.
"""
from __future__ import annotations

import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import uuid

import check_presented_report
import execution_support
import export_proved_code
import investigation_json
import isabelle_native_execution
import native_stage_timing
import proof_contexts

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'validation/overnight-20260918'


def build(output, threads, timeout):
    integration = json.loads((EVIDENCE / 'integration.json').read_text())
    roots = [r['theory'] for r in integration['theories']]
    session = 'Native_Control_Rebuilt_' + uuid.uuid4().hex
    command = [sys.executable, '-B', str(ROOT / 'tools/prove_context.py'),
               '--project', str(ROOT), '--output', str(output), '--session', session,
               '--threads', str(threads), '--timeout', str(timeout), *roots]
    return subprocess.run(command, cwd=ROOT).returncode


def export(context, output):
    if not (context / 'accepted-context.json').exists():
        proof_contexts.adopt_proof_context(context, ROOT)
    return export_proved_code.export_context(context, ROOT, output, [
        ('Native_Control_Child_Review', 'native_control_child_review.ML'),
        ('Native_Control_Source_Execution', 'native_control_source_execution.ML')])


def assignment(tree, name):
    return next(n.value for n in tree.body if isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == name for t in n.targets))


def assessment_boundary(assessment):
    """Identify the complete stable report without retaining its generated bulk.

    These are reconstruction identities, not native satisfaction observations.
    Only the same physical/presentation fields excluded by the original replay
    comparison are omitted. Every result, control and native word remains bound.
    """
    stable = {k: v for k, v in assessment.items()
              if k not in ('timings', 'scope', 'physical_completion')}
    raw = json.dumps(stable, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
            'words': stable['words']}


def request_functions(name, output):
    """Load only the original request/assessment functions, with new file locators.

    The historical driver main (including all /tmp paths) is never executed.
    Keeping its function AST unchanged preserves the exact native expressions.
    """
    driver = EVIDENCE / 'requests' / (name + '.py')
    presenter = EVIDENCE / 'requests/presenter.py'
    metadata = json.loads((EVIDENCE / 'requests.json').read_text())[name]
    assert hashlib.sha256(driver.read_bytes()).hexdigest() == metadata['driver_sha256']
    tree = ast.parse(driver.read_text())
    view = eval(compile(ast.Expression(assignment(ast.parse(presenter.read_text()), 'view')),
                        str(presenter), 'eval'), {'investigation_json': investigation_json})
    words_name = 'words' if name == 'sources' else 'word_values'
    words = ast.literal_eval(assignment(tree, words_name))
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                 and n.name in ('program', 'assess')]
    assert len(functions) == 2
    namespace = dict(gzip=gzip, json=json, re=re, output=output, view=view,
                     check_presented_report=check_presented_report,
                     execution_support=execution_support, native_stage_timing=native_stage_timing)
    namespace[words_name] = words
    native_stage_timing.PRELUDE = native_stage_timing.PRELUDE.replace(
        'in result end;', 'in TextIO.flushOut TextIO.stdOut; result end;')
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(driver), 'exec'), namespace)
    return namespace, metadata, [driver, presenter]


def replay(name, exports, output):
    functions, meta, paths = request_functions(name, output)
    module = 'native_control_source_execution' if name == 'sources' else 'native_control_child_review'
    result = isabelle_native_execution.checked_execution(exports / (module + '.proof.json'),
        Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly'), output,
        workers=meta['workers'], program=functions['program'], assess=functions['assess'],
        input_paths=[Path(__file__), EVIDENCE / 'requests.json', *paths,
                     Path(check_presented_report.__file__), Path(native_stage_timing.__file__)],
        required_theories=meta['required_theories'], inputs=meta['inputs'], question=meta['question'],
        boundary=meta['boundary'], timeout=meta['timeout'], project=ROOT)
    comparison = {'request': name, 'status': result['status'],
                  'boundary': 'Historical result equality is a reproducibility check, not a new admission rule.'}
    if result['status'] == 'accepted' and 'expected_boundary' in meta:
        actual = assessment_boundary(result['assessment'])
        comparison['report_boundaries_equal'] = actual == meta['expected_boundary']
        comparison['report_boundary'] = actual
    (output / 'reconstruction.json').write_text(json.dumps(comparison, indent=2) + '\n')
    print(json.dumps(comparison))
    return int(result['status'] != 'accepted' or comparison.get('report_boundaries_equal') is False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    proof = sub.add_parser('prove')
    proof.add_argument('--output', required=True, type=Path)
    proof.add_argument('--threads', default=16, type=int)
    proof.add_argument('--timeout', default=1200, type=int)
    code = sub.add_parser('export')
    code.add_argument('--context', required=True, type=Path)
    code.add_argument('--output', required=True, type=Path)
    run = sub.add_parser('replay')
    run.add_argument('request', choices=['certificates', 'materials', 'sources'])
    run.add_argument('--exports', required=True, type=Path)
    run.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Reconstruction requires assertions.')
    if args.action == 'prove':
        return build(args.output.resolve(), args.threads, args.timeout)
    if args.action == 'export':
        return export(args.context.resolve(), args.output.resolve())
    return replay(args.request, args.exports.resolve(), args.output.resolve())


if __name__ == '__main__':
    raise SystemExit(main())
