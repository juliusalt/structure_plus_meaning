"""Compare complete actual digit-store generation readings with original operations."""
from pathlib import Path
import argparse
import json

import check_reasoning
import generation_program_json
import investigate
import investigation_json
import machine_reports
import native_program_json
import native_stream_json
import observation_contracts
import proved_code
import stream_reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Indexed_Generation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += native_stream_json.PRELUDE + generation_program_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.indexed_generation_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun wstate (n,e) = wobject [
  ("\"next_head\"",fn () => print (jnat n)),
  ("\"environment\"",fn () => wenvironment e)];
fun wsubject (input,(l,(p,(c,(rows,queries))))) = wobject [
  ("\"state\"",fn () => woption (wstate o N.digit_allocated_view) input),
  ("\"locus\"",fn () => wtarget l),
  ("\"payload\"",fn () => wtarget p),
  ("\"cause\"",fn () => wtarget c),
  ("\"predecessors\"",fn () => wlist wpredecessor rows),
  ("\"queries\"",fn () => wlist wpredecessor queries)];
fun wreading (query,(fields,(checked,anchor))) = wobject [
  ("\"query\"",fn () => wpredecessor query),
  ("\"field_readings\"",fn () => wf wgenerationFields fields),
  ("\"checked\"",fn () => print (Bool.toString checked)),
  ("\"anchor\"",fn () => woption (wartifact o N.finite_artifact_rows) anchor)];
fun wvalue (ready,(anchors,readings)) = wobject [
  ("\"ready\"",fn () => print (Bool.toString ready)),
  ("\"selected_anchors\"",fn () => woption (wlist wanchor) anchors),
  ("\"query_results\"",fn () => wlist wreading readings)];
'''
    code += stream_reader_comparison_json.prelude('wvalue', 'wsubject', 'indexed_generation_inspect')
    code += r'''
fun wvariant (k,result) = wobject [
  ("\"variant\"",fn () => print (jnat k)),
  ("\"readings\"",fn () => wf wvalue result)];
fun wcontext (subject,(reference,variants)) = wobject [
  ("\"subject\"",fn () => wsubject subject),
  ("\"reference_readings\"",fn () => wf wvalue reference),
  ("\"prepared_operations\"",fn () => wlist wvariant variants)];
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun lookup label key rows = case List.find (fn (k,_) => k=key) rows of
  NONE => raise Fail ("Missing complete " ^ label ^ " row") | SOME (_,value) => value;
val () = emit "INDEXED_GENERATION_SCOPE" (jlist jnat N.indexed_generation_indices);
val () = let
val (table,(comparison,cycles)) = N.indexed_generation_packet scope selections;
val () = List.app (fn (w,(context,cells)) => wemit ("INDEXED_GENERATION_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("INDEXED_GENERATION_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "INDEXED_GENERATION_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "INDEXED_GENERATION_INVESTIGATION" (jcycle c)) cycles;
val () = emit "INDEXED_GENERATION_SOURCE_SCOPE" (jlist jnat (N.indexed_generation_source_scope scope));
val previous = N.indexed_generation_previous_cases scope;
val () = List.app (fn (w,old) => let
  val ((subject,(reference,variants)),cells) = lookup "subject" w table
  in wemit ("INDEXED_GENERATION_SOURCE " ^ jnat w) (fn () => wobject [
    ("\"previous\"",fn () => wgenerationProblem old),
    ("\"projected\"",fn () => woption wgenerationProblem (N.indexed_generation_original_subject subject)),
    ("\"native_equal\"",fn () => print (Bool.toString (N.indexed_generation_source_equal subject old)))]) end) previous;
in () end;
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
        'RRA_Indexed_Generation_Investigation', 'indexed_generation_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports[0]['tag'] == 'INDEXED_GENERATION_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'INDEXED_GENERATION_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, reports[1 + i * size:1 + (i + 1) * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'INDEXED_GENERATION_COMPARISON' and compared['value']['scope'] == requested
        start = 2 + 2 * size
        assert all(r['tag'] == 'INDEXED_GENERATION_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[start:start + len(inputs['selections'])]))
        start += len(inputs['selections'])
        assert reports[start]['tag'] == 'INDEXED_GENERATION_SOURCE_SCOPE' and reports[start]['indices'] == []
        source_scope = reports[start]['value']
        assert set(source_scope) <= set(requested)
        source_rows = reports[start + 1:]
        assert len(source_rows) == len(source_scope)
        assert all(r['tag'] == 'INDEXED_GENERATION_SOURCE' and r['indices'] == [w]
                   for w, r in zip(source_scope, source_rows))
        assert len(reports) == 2 * size + 3 + len(inputs['selections']) + len(source_scope)
        return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': source_scope,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete actual inputs, every original field, anchor, recursive check and readiness '
                            'result, ordered queries and outputs, native observations, comparison reasons, '
                            'revisions and unchanged original source cases are retained.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Indexed_Generation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual indexed generation readers preserve every original field, recursive '
                 'predecessor check, readiness and anchor result for the complete requested inputs?',
        boundary='The closed store supplies formation and complete original lookups. Actual native '
                 'operations have all-input original-operation equations and registered subject observations. '
                 'Generation installation, complete physical cost, all six development conditions, native '
                 'mathematical-proof admission, historical permission and reachability, and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
