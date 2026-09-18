#!/usr/bin/env python3
"""Adopt an accepted answer to a request of the refinement layer into the published repository state.

Adoption is a generation over the repository: the theory Isabelle accepted when the answer was
judged, framed where it is adopted, becomes a theory of the repository that the layer's import
boundary imports. The tool moves bytes and invokes the checked tools; it decides nothing. Each step
is judged by the existing machinery:

1. The retained answer is judged again against the present workspace, and its verdict word must be
   the retained one: nothing the answer was accepted against has moved. A differing word makes the
   answer a re-evaluation for the process, and nothing is installed. An answer is adoptable when its
   verdict accepts it, or when the verdict refuses it only for constants it introduces and the
   repair derived from that refusal accepts it: the extension defining those constants is
   conservative and the answer is accepted against the request issued again over the extension.
   The derived definition problems are answered by the answer's own definitions.
2. The judged theory is installed byte for byte and the boundary imports it.
3. The ordinary incremental check proves the changed theories and executes every recipe whose
   execution boundary the change reaches; every report word must equal its retained word.
4. The answer is judged again in the adopted workspace, where its theory is part of the published
   state; it must be accepted as an unchanged answer, with nothing removed or added.

Any refused step withdraws the installation. The receipt retains every step and, for every executed
recipe, its measured seconds beside its retained seconds. Measured cost is an observation; nothing
is ranked or selected by it. Which recipes a change reaches is computed by the host from manifests.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time

import development_answer
from evidence_io import write_json
import execution_support as investigate

ROOT = development_answer.ROOT
TOOLS = ROOT / 'tools'
LAYER = development_answer.STATES['refinement_layer']['layer']


def judge(answer_file, output, timeout):
    started = time.monotonic()
    completed = subprocess.run([sys.executable, '-B', str(TOOLS / 'development_answer.py'), 'answer', '--answer',
                                str(answer_file), '--output', str(output), '--timeout', str(timeout)],
                               cwd=ROOT, capture_output=True, text=True, timeout=timeout + 600)
    record = json.loads((output / 'answer.json').read_text()) if (output / 'answer.json').is_file() else \
        {'status': 'failed', 'error': completed.stdout[-2000:] + completed.stderr[-2000:]}
    record['seconds'] = round(time.monotonic() - started, 2)
    return record


def install(answer, judged):
    """Install the theory exactly as it was judged and import it at the layer's boundary."""
    name = development_answer.answer_name(answer)
    text = (judged / 'project' / 'theories' / (name + '.thy')).read_text()
    assert text == development_answer.answer_theory(development_answer.STATES['refinement_layer'], answer), \
        'The judged frame differs from the present one.'
    theory = ROOT / 'theories' / (name + '.thy')
    assert not theory.exists()
    layer = ROOT / 'theories' / (LAYER + '.thy')
    root = ROOT / 'ROOT'
    original = {'layer': layer.read_text(), 'root': root.read_text()}
    header = re.match(r'(\s*theory\s+\S+\s+imports\s+)([\s\S]*?)(\s+begin\b)', original['layer'])
    assert header and name not in investigate.theory_imports(original['layer'], LAYER)
    entry = '    ' + LAYER + '\n'
    assert original['root'].count(entry) == 1
    theory.write_text(text)
    layer.write_text(header[1] + header[2] + ' ' + name + header[3] + original['layer'][header.end():])
    root.write_text(original['root'].replace(entry, '    ' + name + '\n' + entry))
    assert name in investigate.theory_imports(layer.read_text(), LAYER)
    return {'theory': str(theory.relative_to(ROOT)), 'theory_sha256': investigate.file_hash(theory),
            'layer_sha256': investigate.file_hash(layer), 'root_sha256': investigate.file_hash(root)}, original


def withdraw(answer, original):
    name = development_answer.answer_name(answer)
    (ROOT / 'theories' / (name + '.thy')).unlink(missing_ok=True)
    (ROOT / 'theories' / (LAYER + '.thy')).write_text(original['layer'])
    (ROOT / 'ROOT').write_text(original['root'])


def recipe_costs(summary):
    """Measured seconds of every executed recipe beside the seconds of its retained execution."""
    rows = {}
    for recipe, result in summary.get('recipes', {}).items():
        if result.get('status') != 'accepted':
            continue
        verified = ROOT / 'validation/reconstruction' / (recipe + '-verified.json')
        retained = json.loads(verified.read_text()) if verified.is_file() else {}
        rows[recipe] = {'seconds': result['seconds'],
                        'retained_seconds': round(sum(s.get('seconds', 0) for s in retained.get('steps', [])), 2)}
    return rows


def adoptable(summary):
    """The route through which a judged answer is adoptable, if any."""
    summary = summary or {}
    if summary.get('accepted'):
        return 'request'
    if summary.get('repaired') and summary.get('extension'):
        return 'repaired request'
    return None


def adopt(args):
    record_path = args.record.resolve()
    record = json.loads(record_path.read_text())
    answer = record['answer']
    route = adoptable(record['summary']) if record['status'] == 'judged' else None
    assert route is not None, 'Only an accepted or a repaired and accepted answer is adopted.'
    assert answer['request']['state'] == 'refinement_layer', 'Only answers of the refinement layer are adoptable.'
    assert not development_answer.adopted(answer), 'The answer is already adopted.'
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh adoption directory.'
    output.mkdir(parents=True)
    answer_file = output / 'answer.json'
    answer_file.write_text(json.dumps(answer, indent=1) + '\n')
    name = development_answer.answer_name(answer)
    receipt = {'status': 'refused', 'record': str(record_path), 'record_sha256': investigate.file_hash(record_path),
               'theory': name, 'route': route, 'control': args.control, 'steps': {}}
    original = None
    try:
        before = judge(answer_file, output / 'before', args.timeout)
        receipt['steps']['precondition'] = {k: before.get(k) for k in ('status', 'accepted', 'verdict_word', 'summary',
                                                                       'adopted', 'seconds', 'error')}
        assert before['status'] == 'judged' and adoptable(before.get('summary')) == route, \
            'The answer is no longer accepted through the retained route.'
        assert before['verdict_word'] == record['verdict_word'], \
            'The verdict changed since the answer was retained: it is a re-evaluation, not an adoption.'
        installed, original = install(answer, output / 'before')
        receipt['steps']['installation'] = installed
        started = time.monotonic()
        code = subprocess.run([sys.executable, '-B', str(TOOLS / 'incremental_check.py'), 'check', '--output',
                               str(output / 'check'), '--jobs', '8', '--threads', '16'],
                              cwd=ROOT, capture_output=True, text=True).returncode
        summary = json.loads((output / 'check' / 'incremental.json').read_text())
        receipt['steps']['check'] = {'exit_code': code, 'status': summary['status'], 'error': summary.get('error'),
                                     'seconds': round(time.monotonic() - started, 2), 'phases': summary.get('phases'),
                                     'rebuilt_theories': len(summary.get('rebuilt_theories', [])),
                                     'recipes': {status: sorted(n for n, r in summary.get('recipes', {}).items()
                                                                if r['status'] == status)
                                                 for status in ('accepted', 'reused', 'unchanged', 'failed')},
                                     'costs': recipe_costs(summary)}
        assert code == 0 and summary['status'] == 'accepted', 'A report word changed or the check failed.'
        after = judge(answer_file, output / 'after', args.timeout)
        receipt['steps']['published'] = {k: after.get(k) for k in ('status', 'accepted', 'verdict_word', 'summary',
                                                                   'adopted', 'seconds', 'error')}
        counts = (after.get('summary') or {}).get('counts', [])
        assert after['status'] == 'judged' and after.get('accepted') and after.get('adopted'), \
            'The published state does not accept the adopted answer.'
        assert counts[:4] == [0, 0, 0, 0], 'The published state differs from the adopted answer.'
        receipt['status'] = 'adopted'
    except (AssertionError, OSError, ValueError, KeyError) as error:
        receipt['error'] = str(error)
        if original is not None:
            withdraw(answer, original)
            receipt['withdrawn'] = True
    if receipt['status'] == 'adopted' and args.control:
        withdraw(answer, original)
        receipt['withdrawn'] = True
    write_json(output / 'receipt.json', receipt)
    print(json.dumps({k: receipt[k] for k in ('status', 'theory', 'error', 'withdrawn') if k in receipt}))
    return 0 if receipt['status'] == 'adopted' else 1


def main():
    if not __debug__:
        raise ValueError('Adoption requires Python assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True, help='A retained judged answer record.')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--control', action='store_true',
                        help='Withdraw the adoption after it is established: the answer is a control of the process.')
    return adopt(parser.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
