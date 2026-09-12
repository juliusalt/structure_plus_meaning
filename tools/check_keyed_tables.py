"""Execute complete table subjects and independently assess both native operations."""
from pathlib import Path
import argparse, json
import investigate, proved_code, check_reasoning as review
import table_cases


def table_value(rows):
    return review.sequence([review.pair(k, v) for k, v in rows])


def program(engine, inputs):
    tables, indices = [], {}
    def index(rows):
        key = review.freeze(rows)
        if key not in indices:
            indices[key] = len(tables)
            tables.append(rows)
        return indices[key]
    calls = [(i, index(c['left']), index(c['right'])) for i, c in enumerate(inputs['cases'])]
    ml_row = lambda row: '(' + review.ml_term(row[0]) + ',' + review.ml_term(row[1]) + ')'
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n' + review.PRELUDE
    code += 'val tables = Vector.fromList ' + investigate.ml_list(tables, lambda xs: investigate.ml_list(xs, ml_row)) + ';\n'
    code += r'''
fun jrow (k,v) = "[" ^ jterm k ^ "," ^ jterm v ^ "]";
fun emitTable (i,a,b) = let
 val xs = Vector.sub (tables,a); val ys = Vector.sub (tables,b)
 val result = N.finite_keyed_table_comparison xs ys
 val old = N.finite_keyed_data_comparison xs ys
 in print ("TABLE_RESULT " ^ Int.toString i ^ " {\"left\":" ^ jlist jrow xs ^
  ",\"right\":" ^ jlist jrow ys ^ ",\"left_formed\":" ^ Bool.toString (N.finite_keyed_rows_formed xs) ^
  ",\"right_formed\":" ^ Bool.toString (N.finite_keyed_rows_formed ys) ^
  ",\"keyed\":" ^ Bool.toString result ^ ",\"data\":" ^ Bool.toString old ^ "}\n") end;
val () = emitCompiledLibrary 0 N.keyed_table_construction_library;
'''
    code += 'val () = List.app emitTable ' + investigate.ml_list(calls, lambda row: '(' + ','.join(map(str, row)) + ')') + ';\n'
    return code


def data(term):
    if 'payload' in term:
        return True
    return 'pair' in term and all(data(t) for t in term['pair'])


def rows_formed(rows):
    return all(review.formed(k) and data(k) and review.formed(v) for k, v in rows)


def relation(rows):
    keys = [review.freeze(k) for k, _ in rows]
    if not rows_formed(rows) or len(set(keys)) != len(keys):
        return None
    return {review.freeze(k): review.freeze(v) for k, v in rows}


def expected_library():
    v = lambda n: {'var': n}
    p = review.pair
    def entry(d, head, premises):
        return {'entry': d, 'schema': {'head': head, 'premises': premises, 'materials': []},
                'enumeration': premises}
    return [
        entry(351, p(v(0), p(v(1), v(2))), [[0, 28, p(v(1), p(v(0), review.sequence([v(2)])))]]),
        entry(352, p(v(0), review.payload()), []),
        entry(352, p(v(0), p(v(1), v(2))), [[0, 351, p(v(0), v(1))], [1, 352, p(v(0), v(2))]]),
        entry(353, p(v(0), v(1)), [[0, 352, p(v(1), v(0))], [1, 352, p(v(0), v(1))]]),
    ]


def assess(inputs, raw):
    reports, libraries = {}, []
    for line in raw.splitlines():
        if line.startswith('TABLE_RESULT '):
            _, identifier, value = line.split(' ', 2)
            identifier = int(identifier)
            assert identifier not in reports
            reports[identifier] = json.loads(value)
        elif line.startswith('COMPILED_LIBRARY '):
            _, identifier, value = line.split(' ', 2)
            assert identifier == '0'
            libraries.append(json.loads(value))
    assert len(libraries) == 1
    actual_library = libraries[0]
    assert len(actual_library) == len(expected_library())
    assert [review.schema_key(e['schema']) for e in actual_library] == [review.schema_key(e['schema']) for e in expected_library()]
    assert [e['entry'] for e in actual_library] == [e['entry'] for e in expected_library()]
    for e in actual_library:
        assert {review.freeze(x) for x in e['enumeration']} == {review.freeze(x) for x in e['schema']['premises']}
        assert len(e['enumeration']) == len(e['schema']['premises'])
    assert set(reports) == set(range(len(inputs['cases'])))
    mismatches, scope, failures = [], [], []
    for i, case in enumerate(inputs['cases']):
        xs, ys = case['left'], case['right']
        a, b = relation(xs), relation(ys)
        keyed = a is not None and b is not None and a == b
        old = (rows_formed(xs) and rows_formed(ys) and all(data(v) for _, v in xs + ys)
               and set(map(review.freeze, xs)) == set(map(review.freeze, ys)))
        expected = {'left': xs, 'right': ys, 'left_formed': rows_formed(xs),
                    'right_formed': rows_formed(ys), 'keyed': keyed, 'data': old}
        expected = json.loads(json.dumps(expected))
        if reports[i] != expected:
            mismatches.append({'case': i, 'name': case['name'], 'actual': reports[i], 'expected': expected})
        if old != keyed:
            scope.append({'case': i, 'name': case['name'], 'data': old, 'keyed': keyed,
                          'literal_value_present': any(not data(v) for _, v in xs + ys),
                          'duplicate_key_present': a is None or b is None})
        if not keyed:
            failures.append({'case': i, 'name': case['name'], 'left_functional_formed': a is not None,
                             'right_functional_formed': b is not None,
                             'complete_relations_equal': a is not None and b is not None and a == b})
    assert not mismatches, mismatches[:3]
    return {'cases': len(reports), 'small_tables': inputs['small_tables'], 'small_pairs': inputs['small_pairs'],
            'complete_inputs_and_native_results_equal': True, 'compiled_library': actual_library,
            'scope_differences': scope, 'independent_rejection_analysis': failures,
            'boundary': 'Both whole native operations and every full returned input are checked. The rejection analysis is independently reconstructed by the host. Native rule construction and semantic admission of its premises are separate subsequent checks.'}


def main():
    p = argparse.ArgumentParser()
    for name in ['proof', 'poly', 'project', 'output']:
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    receipt = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Finite_Keyed_Table_Comparison'], inputs=table_cases.cases(),
        input_paths=[Path(__file__), Path(table_cases.__file__)], program=program, assess=assess,
        question='Do both native table operations retain the exact complete functional-table and data-set domains on the supplied complete subjects?',
        boundary='Actual native-call equations govern the complete finite operands. A finite test family supplements their universal Isabelle contracts and does not replace whole symbolic proof admission.',
        timeout=180, project=args.project.resolve())
    print(json.dumps({"status": receipt["status"], "error": receipt.get("error"),
                      "cases": receipt.get("assessment", {}).get("cases")}))
    return int(receipt["status"] != "accepted")


if __name__ == '__main__':
    raise SystemExit(main())
