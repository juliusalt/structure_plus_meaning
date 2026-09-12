"""Construct the nonempty reader from exact source leaves and complete native data calls."""
from pathlib import Path
import argparse, json
import nonempty_source_case as family
from proved_code import accepted_execution as accepted
from evidence_io import write_json

WORKTREE, review = family.ROOT, family.review


def cases_for(catalog, result):
    assessment = result['assessment']
    source = assessment['checked_source']
    old_known = catalog['assessment']['source_example']['known']
    library = catalog['assessment']['compiled_library']
    cases = []
    def add(name, work, depth, known=None, omitted=(), residual=None):
        positives = [call for call, truth in zip(work['condition_calls'], work['condition_values']) if truth]
        supplied = source['known'] + positives if known is None else known
        frontier = source['known'] + [[350, source['source']], work['join_call']] + work['condition_calls']
        selected = [row for row in library if row['entry'] not in omitted]
        goals = [[0, 350, source['source']], [1, 359, review.pair(source['source'], work['table'])]]
        item = review.case(name, selected, frontier, supplied, goals, ['guided', depth])
        native = {'name': 'inference_claim_construction_library'}
        if omitted: native['entries'] = sorted({row['entry'] for row in selected})
        formed = all(review.formed(term) for _, term in frontier + supplied) and all(review.formed(t) for _, _, t in goals)
        expectation = {'input_formed': formed}
        if formed and residual is not None:
            expectation['residual_goals'] = residual
            expectation['settled_goals'] = [i for i in [0, 1] if i not in residual]
        item.update(guided_rounds=depth, native_libraries=[native], native_goal_truth=[True, work['local_truth']],
            expected_report=expectation, source_operand=source['source'],
            semantic_boundary='The actual source and local base reader are kernel-proved. Complete table-control truth uses the exact native reader contract. Initial evidence contains only the exported source leaves and positively checked data calls; 100, 350 and 359 are never known.')
        cases.append(item)
    for work in assessment['controls']:
        add(work['name'] + '-depth-3', work, 3, residual=[] if work['local_truth'] else [1])
    base = assessment['controls'][0]
    for depth in [0, 2]: add('complete-depth-' + str(depth), base, depth)
    positives = [call for call, truth in zip(base['condition_calls'], base['condition_values']) if truth]
    known = source['known'] + positives
    add('withheld-node-source', base, 3, known=[q for q in known if q[0] != 94], residual=[0, 1])
    child_fibre = review.freeze(base['condition_calls'][2])
    add('withheld-child-fibre', base, 3, known=[q for q in known if review.freeze(q) != child_fibre], residual=[1])
    add('wrong-source-leaves', base, 3, known=old_known + positives, residual=[0, 1])
    add('no-known-calls', base, 3, known=[], residual=[0, 1])
    for entry in [350, 100, 359]:
        add('omitted-constructor-' + str(entry), base, 3, omitted=[entry], residual=[0, 1] if entry == 350 else [1])
    return cases


def main():
    parser = argparse.ArgumentParser()
    for name in ['proof', 'poly', 'catalog', 'inputs', 'output']: parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    catalog = accepted(args.catalog, args.poly, args.proof)
    result = accepted(args.inputs, args.poly, args.proof)
    facts = result['assessment']['checked_source']['known'] + catalog['assessment']['source_example']['known']
    for work in result['assessment']['controls']:
        facts += [q for q, truth in zip(work['condition_calls'], work['condition_values']) if truth]
    established = frozenset(map(review.freeze, facts))
    def known_call(entry, term): return review.freeze([entry, term]) in established
    paths = [Path(__file__), Path(family.__file__), Path(accepted.__code__.co_filename),
             args.catalog / 'receipt.json', args.catalog / 'results.log', args.inputs / 'receipt.json', args.inputs / 'results.log']
    contract = review.KnownCallContract(known_call,
        'Exact emitted finite_child_inference_known [] and finite_literal_inference_known [] satisfy their proved whole-program inclusion theorems. Positive native table, complete-fibre, projection and comparison calls satisfy their complete-input equations and whole-program agreements. Neither the join nor either reader is initially known.', tuple(paths))
    cases = cases_for(catalog, result)
    for case in cases:
        contract.validate(case['known'])
        assert all(d not in {100, 350, 359} for d, _ in case['known'])
    review.ROOT = WORKTREE
    args.engine = None
    status = review.run(args, cases_factory=lambda: cases, cases_source=Path(__file__),
                        cases_dependencies=paths, known_call_contract=contract)
    if status: return status
    reports = {}
    for line in (args.output / 'results.log').read_text().splitlines():
        if line.startswith('REASONING_RESULT '):
            _, i, value = line.split(' ', 2)
            assert int(i) not in reports
            reports[int(i)] = json.loads(value)
    assert set(reports) == set(range(len(cases)))
    write_json(args.output / 'adequacy.json', {'cases': [
        {'name': c['name'], 'native_goal_truth': c['native_goal_truth'], 'expected': c['expected_report'],
         'input_formed': reports[i]['input_formed'], 'residual': reports[i]['residual'],
         'applications': len(reports[i]['applications'])} for i, c in enumerate(cases)],
         'boundary': 'Bounded native construction from exact proved sources. The separate assertion, whole-graph and mathematical-proof boundaries remain explicit.'})
    print(json.dumps({'cases': len(cases), 'complete_results_checked': True}))
    return 0


if __name__ == '__main__': raise SystemExit(main())
