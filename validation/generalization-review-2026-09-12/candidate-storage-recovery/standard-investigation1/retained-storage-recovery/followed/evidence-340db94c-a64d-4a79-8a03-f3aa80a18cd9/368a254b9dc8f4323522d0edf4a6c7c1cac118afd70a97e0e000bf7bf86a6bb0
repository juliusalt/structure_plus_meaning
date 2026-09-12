#!/usr/bin/env python3
"""Independently reconstruct saved finite investigations for content-quality review.

This checks finite computations and recorded bytes. The supplied observation
meanings, independent comparison, and coverage still require subject review.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relation(rows):
    return {tuple(row) for row in rows}


def functional(rows):
    values = {}
    for occurrence, condition in rows:
        if occurrence in values and values[occurrence] != condition:
            return False
        values[occurrence] = condition
    return True


def basis_analysis(case, result, scope):
    candidates = case.get('candidates', [p['candidate'] for p in result['profiles']])
    C = set(candidates)
    if 'facets' in case:
        U = set(case['facets'])
    elif isinstance(scope, dict) and isinstance(scope.get('facets'), dict):
        U = {int(f) for f in scope['facets']}
    else:
        raise ValueError('No independent available-facet domain was retained.')
    F = set(case['selected'])
    T = relation(case.get('observations', result.get('observations', [])))
    R = relation(case.get('relation', result.get('relation', [])))
    pairs = set(itertools.product(C, C))
    formed = F <= U and all(f in U and c in C for f, c, w in T)
    observe = lambda f, c: {w for g, d, w in T if (f, c) == (g, d)}
    profile = lambda G, c: {(f, w) for f in G for w in observe(f, c)}
    loss = lambda G, c, d: profile(G, c) - profile(G, d)
    residual = lambda G: {(c, d) for c, d in pairs if ((c, d) in R) != (profile(G, c) <= profile(G, d))}
    missing = lambda G: {(c, d) for c, d in pairs - R if profile(G, c) <= profile(G, d)}
    safe = {f for f in U if all(observe(f, c) <= observe(f, d) for c, d in pairs & R)}
    conflicts = lambda G: {(c, d, f, w) for c, d in pairs & R for f, w in loss(G, c, d)}
    repairs = lambda G: {(c, d, f, w) for c, d in missing(G) for f, w in loss(safe - G, c, d)}
    extend = lambda G, witnesses: G | {f for c, d, f, w in witnesses}
    retained = F & safe
    withdrawn = F - safe
    original_repairs = repairs(F)
    revised_repairs = repairs(retained)
    extension = extend(F, original_repairs)
    revised = extend(retained, revised_repairs)
    expected = {'input_formed': formed, 'residual': residual(F), 'safe_facets': safe,
                'conflicts': conflicts(F), 'repairs': original_repairs,
                'unrepairable': residual(safe), 'extension': extension}
    checked, mismatches = [], []
    for key, value in expected.items():
        if key not in result:
            continue
        actual = result[key] if isinstance(value, bool) else set(result[key]) if key in {'safe_facets', 'extension'} else relation(result[key])
        checked.append(key)
        if actual != value:
            mismatches.append(key)
    if [p['candidate'] for p in result['profiles']] != candidates:
        mismatches.append('profile occurrence domain')
    if any(relation(p['profile']) != profile(F, p['candidate']) for p in result['profiles']):
        mismatches.append('profile values')
    if [(p['from'], p['to']) for p in result['losses']] != list(itertools.product(candidates, candidates)):
        mismatches.append('loss occurrence domain')
    if any(relation(p['losses']) != loss(F, p['from'], p['to']) for p in result['losses']):
        mismatches.append('loss values')
    checked.extend(['complete profiles', 'complete ordered losses'])
    if isinstance(scope, dict) and isinstance(scope.get('candidates'), dict):
        if {int(c) for c in scope['candidates']} != C:
            mismatches.append('declared actual candidate scope')
    if 'revision' in result:
        report = result['revision']
        if not formed:
            if report is not None:
                mismatches.append('revision proposed for rejected input')
        elif not isinstance(report, dict):
            mismatches.append('missing formed revision')
        else:
            for key, value in {'retained': retained, 'withdrawn': withdrawn, 'repairs': revised_repairs,
                               'selection': revised, 'residual': residual(revised)}.items():
                actual = set(report[key]) if key in {'retained', 'withdrawn', 'selection'} else relation(report[key])
                if actual != value:
                    mismatches.append('revision.' + key)
        checked.append('complete revision and admission gate')
    adequate = None
    if len(U) <= 12:
        adequate = [sorted(G) for n in range(len(U) + 1) for xs in itertools.combinations(sorted(U), n)
                    if not residual(G := set(xs))]
    facts = {'input_formed': formed, 'candidate_count': len(C), 'available_facets': sorted(U),
             'selected': sorted(F), 'safe': sorted(safe), 'invalid_selected': sorted(F - U),
             'residual_count': len(residual(F)), 'conflict_count': len(conflicts(F)),
             'missing_count': len(missing(F)), 'repair_count': len(original_repairs),
             'unrepairable_count': len(residual(safe)),
             'positive_comparisons': len(pairs & R), 'negative_comparisons': len(pairs - R),
             'relation_reflexive': all((c, c) in R for c in C),
             'relation_transitive': all((c, e) in R for c in C for d in C for e in C if (c, d) in R and (d, e) in R),
             'empty_selection_adequate': not residual(set()),
             'adequate_selections': adequate,
             'adequate_selection_enumeration': 'complete' if adequate is not None else 'omitted: more than twelve facets',
             'extension_adequate': not residual(extension),
             'sound_language_adequate': not residual(safe)}
    if formed:
        facts['revision'] = {'retained': sorted(retained), 'required_withdrawals': sorted(withdrawn),
                             'new_missing_after_withdrawal': sorted(missing(retained) - missing(F)),
                             'reuse_original_repairs_adequate': not residual(extend(retained, original_repairs)),
                             'recomputed_selection': sorted(revised), 'residual': sorted(residual(revised))}
    signature = [sorted(C), sorted(U), sorted(F), sorted(T), sorted(R), formed]
    facts['evaluation_signature'] = digest(json.dumps(signature, separators=(',', ':')).encode())
    return mismatches, checked, facts


def inference_analysis(case, result):
    rules, known, goals = case['rules'], set(case['known']), case['goals']
    valid = [rule for rule in rules if functional(rule['premises'])]
    reached = set(known)
    while True:
        more = {rule['conclusion'] for rule in valid if {b for i, b in rule['premises']} <= reached}
        if more <= reached:
            break
        reached |= more
    demanded = {b for i, b in goals}
    while True:
        more = {b for rule in valid if rule['conclusion'] in demanded - known for i, b in rule['premises']}
        if more <= demanded:
            break
        demanded |= more
    reasons = {(rule['conclusion'], frozenset(tuple(row) for row in rule['premises']), i, b)
               for rule in valid if rule['conclusion'] in demanded - known for i, b in rule['premises']}
    formed = len(valid) == len(rules) and functional(goals)
    residual = {(i, b) for i, b in goals if b not in reached}
    expected = {'input_formed': formed, 'residual': residual, 'demand': demanded, 'reasons': reasons}
    actual = {'input_formed': result['input_formed'], 'residual': relation(result['residual']),
              'demand': set(result['demand']),
              'reasons': {(r['conclusion'], frozenset(tuple(row) for row in r['premises']), r['premise'], r['condition']) for r in result['reasons']}}
    facts = {'input_formed': formed, 'rule_count': len(rules), 'invalid_rule_count': len(rules) - len(valid),
             'known_count': len(known), 'goal_count': len(goals), 'closure_count': len(reached),
             'residual_count': len(residual), 'demand_count': len(demanded), 'reason_count': len(reasons),
             'evaluation_signature': digest(json.dumps([rules, sorted(known), goals], sort_keys=True).encode())}
    return [key for key in expected if expected[key] != actual[key]], list(expected), facts


def artifact_analysis(path, receipt, case):
    records = []
    archives = {item['sha256']: item['archive'] for item in receipt.get('evidence_archive', [])}
    def check(role, source, expected):
        if not source or not expected:
            return
        p = Path(source)
        state = 'matches' if p.is_file() and digest(p.read_bytes()) == expected else 'changed' if p.is_file() else 'missing'
        item = {'role': role, 'path': str(p), 'sha256': expected, 'state': state}
        if state != 'matches' and expected in archives:
            archive = Path(archives[expected])
            item['archive'] = str(archive)
            item['archive_matches'] = archive.is_file() and digest(archive.read_bytes()) == expected
        records.append(item)
    for role, source, expected in [
        ('saved case', path.parent / 'case.json', receipt.get('case_sha256')),
        ('generated engine', receipt.get('generated_engine'), receipt.get('generated_engine_sha256')),
        ('runtime', receipt.get('poly'), receipt.get('poly_sha256')),
        ('runtime program', path.parent / 'execute.ML', receipt.get('runtime_program_sha256')),
        ('proof receipt', path.parent / 'proof.json', receipt.get('proof_receipt_sha256')),
        ('run log', path.parent / 'run.log', receipt.get('log_sha256'))]:
        check(role, source, expected)
    for source, expected in receipt.get('tools', {}).items():
        check('original execution tool', source, expected)
    for source, expected in receipt.get('proof_snapshot_hashes', {}).items():
        check('engine snapshot', Path(receipt['engine_snapshot']) / source, expected)
    for item in case.get('evidence', []):
        check('external case evidence', item['path'], item['sha256'])
    for item in receipt.get('evidence_archive', []):
        check('archived ' + item['role'], item['archive'], item['sha256'])
    if 'input' in receipt:
        check('original case', receipt['input']['path'], receipt['input']['sha256'])
    return {'counts': dict(Counter(item['state'] for item in records)),
            'issues': [item for item in records if item['state'] != 'matches'],
            'checked_roles': dict(Counter(item['role'] for item in records))}


def review(path):
    raw = path.read_bytes()
    receipt = json.loads(raw)
    record = {'path': str(path.resolve()), 'receipt_sha256': digest(raw), 'status': receipt.get('status')}
    if 'result' not in receipt:
        return {**record, 'computation': 'no evaluator result; no semantic success inferred'}
    case_path = path.parent / 'case.json'
    case = json.loads(case_path.read_text())
    kind = case.get('kind', 'inference')
    scope = receipt.get('scope', case.get('scope'))
    try:
        mismatches, checked, facts = (inference_analysis(case, receipt['result']) if kind == 'inference'
                                      else basis_analysis(case, receipt['result'], scope))
        record.update(kind=kind, question=receipt.get('question', case.get('question')), scope=scope,
                      semantic_boundary=receipt.get('semantic_boundary', case.get('semantic_boundary')),
                      computation='matches independent reconstruction' if not mismatches else 'mismatch',
                      mismatches=mismatches, checked_fields=checked, facts=facts,
                      artifacts=artifact_analysis(path, receipt, case))
    except (ValueError, KeyError, TypeError) as error:
        record.update(computation='not fully reconstructed', error=str(error))
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', type=Path, nargs='+', help='Receipt files or run directories; directories are searched recursively')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    paths = sorted({p.resolve() for item in args.paths for p in ([item] if item.is_file() else item.rglob('receipt.json'))})
    records = [review(path) for path in paths]
    summary = {'receipts': len(records), 'computations': dict(Counter(r['computation'] for r in records)),
               'statuses': dict(Counter(r['status'] for r in records)),
               'distinct_evaluation_states': len({r['facts']['evaluation_signature'] for r in records if 'facts' in r}),
               'formed_runs_with_required_withdrawals': sum(bool(r.get('facts', {}).get('revision', {}).get('required_withdrawals')) for r in records),
               'formed_runs_with_new_missing_after_withdrawal': sum(bool(r.get('facts', {}).get('revision', {}).get('new_missing_after_withdrawal')) for r in records)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'scope': 'Supplied saved finite computations and recorded artifacts; independent subject meanings and coverage require review',
                                     'summary': summary, 'runs': records}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    return int(any(r['computation'] in {'mismatch', 'not fully reconstructed'} for r in records))


if __name__ == '__main__':
    raise SystemExit(main())
