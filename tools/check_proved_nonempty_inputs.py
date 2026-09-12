"""Check actual exported child sources, their initial calls and complete local table controls."""
from pathlib import Path
import argparse, json
import check_nonempty_construction_inputs as original
import check_child_primitives as primitives

family = original.family
WORKTREE, review = family.ROOT, family.review
tables, investigate, proved_code = original.tables, original.investigate, original.proved_code

NAMES = ['complete', 'missing-child', 'wrong-child-pattern', 'wrong-child-callee',
         'duplicate-child', 'malformed-unused', 'wrong-parent', 'reordered', 'extra-formed']


def program(engine, inputs):
    code = original.program(engine, inputs['source_specification'])
    code += r'''
val () = print ("CHECKED_CHILD {\"source\":" ^ jterm (N.finite_child_inference_value []) ^
 ",\"goal\":" ^ jterm (N.finite_child_claim_value []) ^
 ",\"known\":" ^ jlist jcall (N.finite_child_inference_known []) ^ "}\n");
val wrongPattern = pair callee (pair (pl [9]) (pl [9]));
val wrongCallee = pair (site (SOME [n 2]) [n 9]) (pair (pl []) (pl []));
val controls = [claimRows,[(parentKey,claimValue)],
 [(parentKey,claimValue),(childKey,wrongPattern)],
 [(parentKey,claimValue),(childKey,wrongCallee)],
 claimRows @ [(childKey,claimValue)],claimRows @ [(pl [200],pl [256])],
 [(parentKey,wrongPattern),(childKey,claimValue)],rev claimRows,claimRows @ [(pl [200],pl [])]];
fun emitControl (i,rows) = let
 val values = N.finite_key_fibre_values childKey rows
 val joined = case values of [v] => [pair premiseKey v] | _ => []
 val projected = N.finite_prefixed_observation_outputs owner joined
 val (l,r) = case projected of SOME p => p | NONE => ([],[])
 val projectionOK = case projected of SOME _ => true | NONE => false
 val facts = [(n 21,table rows),
  (n 28,pair parentKey (pair (table rows) (seq [claimValue]))),
  (n 28,pair childKey (pair (table rows) (seq values))),
  (n 358,pair owner (pair (seq joined) (pair (seq l) (seq r)))),
  (n 353,pair (seq l) ordinary),(n 353,pair (seq r) ordinary)]
 val truth = [N.finite_keyed_table_comparison rows rows,
  N.finite_key_fibre_holds parentKey rows [claimValue],
  N.finite_key_fibre_holds childKey rows values,projectionOK,
  N.finite_keyed_table_comparison (map rowFields l) [(pl [24],pair callee (pl []))],
  N.finite_keyed_table_comparison (map rowFields r) [(pl [24],pair callee (pl []))]]
 val localTruth = List.all (fn x => x) truth andalso List.length values = 1
 val joinCall = (n 100,pair (table rows) (pair (table dischargeRows) (seq joined)))
 in print ("CHECKED_CONTROL " ^ Int.toString i ^ " {\"rows\":" ^ jlist jrow rows ^
  ",\"table\":" ^ jterm (table rows) ^ ",\"child_values\":" ^ jlist jterm values ^
  ",\"joined_rows\":" ^ jlist jterm joined ^ ",\"projection\":[" ^ jlist jterm l ^ "," ^ jlist jterm r ^
  "],\"condition_calls\":" ^ jlist jcall facts ^ ",\"condition_values\":" ^ jlist Bool.toString truth ^
  ",\"join_call\":" ^ jcall joinCall ^ ",\"local_truth\":" ^ Bool.toString localTruth ^ "}\n") end;
val () = List.app emitControl (ListPair.zip (List.tabulate (List.length controls, fn i => i),controls));
'''
    return code


def assess(inputs, raw):
    result = original.assess(inputs['source_specification'], raw)
    checked, controls = [], {}
    for line in raw.splitlines():
        if line.startswith('CHECKED_CHILD '): checked.append(json.loads(line.split(' ', 1)[1]))
        elif line.startswith('CHECKED_CONTROL '):
            _, number, value = line.split(' ', 2)
            assert int(number) not in controls
            controls[int(number)] = json.loads(value)
    assert len(checked) == 1 and set(controls) == set(range(len(NAMES)))
    source = result['source']
    actual = checked[0]
    assert actual['source'] == source['source'] == inputs['previous']['source']['source']
    assert actual['goal'] == review.pair(source['source'], source['table'])
    assert result['application_problem'] == inputs['previous']['application_problem']
    assert result['native_application_targets'] == inputs['previous']['native_application_targets']
    assert [entry for entry, _ in actual['known']] == [94, 294, 126, 125, 61, 61, 345, 346]
    assert actual['known'][4] == actual['known'][5]
    assert all(review.formed(term) for _, term in actual['known'])
    parent_key, parent_value = source['rows'][0]
    child_key, _ = source['rows'][1]
    premise_key, target = source['discharge_rows'][0]
    assert target == child_key
    ordinary = source['projection'][0]
    rows_of = lambda terms: [list(term['pair']) for term in terms]
    def comparison(left, right):
        l, r = tables.relation(left), tables.relation(right)
        return l is not None and r is not None and l == r
    verified = []
    for number, name in enumerate(NAMES):
        work = controls[number]
        rows = work['rows']
        values = [v for k, v in rows if k == child_key]
        joined = [review.pair(premise_key, values[0])] if len(values) == 1 else []
        projection = primitives.project(source['owner'], joined)
        assert work['child_values'] == values and work['joined_rows'] == joined
        assert work['table'] == tables.table_value(rows)
        assert work['projection'] == (projection if projection is not None else [[], []])
        left, right = work['projection']
        expected = [comparison(rows, rows),
                    review.formed(parent_key) and tables.data(parent_key) and tables.rows_formed(rows)
                    and [v for k, v in rows if k == parent_key] == [parent_value],
                    review.formed(child_key) and tables.data(child_key) and tables.rows_formed(rows),
                    projection is not None, comparison(rows_of(left), rows_of(ordinary)),
                    comparison(rows_of(right), rows_of(ordinary))]
        assert work['condition_values'] == expected, name
        assert work['local_truth'] == (all(expected) and len(values) == 1), name
        assert [d for d, _ in work['condition_calls']] == [21, 28, 28, 358, 353, 353]
        expected_calls = [[21, work['table']],
            [28, review.pair(parent_key, review.pair(work['table'], review.sequence([parent_value])))],
            [28, review.pair(child_key, review.pair(work['table'], review.sequence(values)))],
            [358, review.pair(source['owner'], review.pair(review.sequence(joined),
                  review.pair(review.sequence(left), review.sequence(right))))],
            [353, review.pair(review.sequence(left), review.sequence(ordinary))],
            [353, review.pair(review.sequence(right), review.sequence(ordinary))]]
        assert work['condition_calls'] == expected_calls
        assert work['join_call'] == [100, review.pair(work['table'], review.pair(
            tables.table_value(source['discharge_rows']), review.sequence(joined)))]
        verified.append({'name': name, **work})
    assert [row['local_truth'] for row in verified] == [True, False, False, False, False, False, False, True, True]
    result.update(checked_source=actual, controls=verified,
        contracts=['finite_child_inference_admitted', 'finite_child_claim_admitted',
                   'inference_claim_child_known_sound', 'inference_claim_at_arguments',
                   'keyed_row_join_output_unique', 'finite_key_fibre_values_native',
                   'finite_prefixed_observation_outputs_native'],
        boundary='The complete source and base child operand equal the checked exported constants. '
        'The eight exported source leaves and every positive native complete-input data call are justified '
        'in the compiled reader program. Local control truth follows the existing complete reader contract. '
        'The assertion child remains an assumption; this is not whole-graph or mathematical-proof admission.')
    return result


def main():
    parser = argparse.ArgumentParser()
    for name in ['proof', 'poly', 'baseline', 'output']: parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    baseline = proved_code.accepted_execution(args.baseline, args.poly, args.proof)
    inputs = {'source_specification': family.source_specification(), 'previous': baseline['assessment']}
    receipt = proved_code.checked_execution(args.proof, args.poly, args.output, project=WORKTREE,
        required_theories=['Factor_Finite_Child_Premises', 'Factor_Inference_Claim_Correspondence',
                           'Finite_Keyed_Fibre_Values', 'Inference_Claim_Input_Execution'],
        inputs=inputs, input_paths=[Path(__file__), Path(original.__file__), Path(family.__file__),
          Path(primitives.__file__), Path(tables.__file__), Path(tables.table_cases.__file__),
          original.RECOVERY, family.ORIGINAL, args.baseline / 'receipt.json', args.baseline / 'results.log'],
        program=program, assess=assess, timeout=180,
        question='Check the actual nonempty child source, its exported initial evidence and all complete claim-table controls.',
        boundary='Source and local-reader proofs are required in the checked export; all complete operands and operation subjects are retained.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__': raise SystemExit(main())
