"""Compare complete native artifact lookup and retain local update observations."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code
import reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Artifact_Lookup_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.artifact_lookup_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jvalue c = jartifact (N.finite_artifact_rows c);
fun jentry (u,c) = "[" ^ juse u ^ "," ^ jvalue c ^ "]";
fun jsubject (rows,u) = "{\"artifact_rows\":" ^ jlist jentry rows ^ ",\"query_use\":" ^ juse u ^ "}";
'''
    code += reader_comparison_json.prelude('jvalue', 'artifact_lookup_inspect')
    code += r'''
fun jafter (u,(previous,following)) = "{\"use\":" ^ juse u ^ ",\"before\":" ^ jf jvalue previous ^
  ",\"after\":" ^ jf jvalue following ^ "}";
fun jpath (path,((values,reads),(updates,(result,rows)))) =
  "{\"path\":" ^ jlist Bool.toString path ^ ",\"optional_bucket\":" ^ jo (jf jvalue) values ^
  ",\"read_steps\":" ^ jnat reads ^ ",\"update_steps\":" ^ jnat updates ^
  ",\"updated_value\":" ^ jf jvalue result ^ ",\"all_before_and_after\":" ^ jlist jafter rows ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "ARTIFACT_LOOKUP_SCOPE" (jlist jnat N.artifact_lookup_indices);
val (table,(comparison,cycles)) = N.artifact_lookup_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("ARTIFACT_LOOKUP_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("ARTIFACT_LOOKUP_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = List.app (fn (w,(context,cells)) => emit ("ARTIFACT_LOOKUP_PATH " ^ jnat w)
  (jpath (N.artifact_lookup_path_report (#1 context)))) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "ARTIFACT_LOOKUP_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "ARTIFACT_LOOKUP_INVESTIGATION" (jcycle c)) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'RRA_Artifact_Lookup_Investigation', 'artifact_lookup_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'ARTIFACT_LOOKUP_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 3 * size + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT', 'PATH']):
            assert all(r['tag'] == 'ARTIFACT_LOOKUP_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 3 * size]
        assert compared['tag'] == 'ARTIFACT_LOOKUP_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'ARTIFACT_LOOKUP_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[2 + 3 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'All source rows, native reference and candidate values, original-condition '
                            'assessments, comparison and revision reasons, actual encoded paths, instrumented '
                            'step counts and complete before/after lookups are retained. The host checks only '
                            'complete report reproduction.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Artifact_Lookup_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which lookup methods recover exactly the original complete artifact relation, preserving '
                 'conflicting values, distinct optional uses and every natural use word?',
        boundary='Registered all-input equations connect actual sources to original artifact membership. '
                 'The persistent store equations preserve off-path lookups and count actual path positions. '
                 'Preparation, whole-artifact comparison, global formation and the full physical decision '
                 'cost remain separate requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
