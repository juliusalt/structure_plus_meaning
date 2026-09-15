"""Compare whole digit generation construction and complete original generation assessments."""
from pathlib import Path
import argparse
import json

import check_reasoning
import generation_assessment_json
import generation_program_json
import investigate
import investigation_json
import machine_reports
import native_program_json
import native_stream_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Digit_Generation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += native_stream_json.PRELUDE + generation_program_json.PRELUDE + generation_assessment_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    code += 'val originalFacets = N.generation_record_condition_scope;\n'
    scope = ('N.digit_generation_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun wstate (n,e) = wobject [
  ("\"next_head\"",fn () => print (jnat n)),
  ("\"environment\"",fn () => wenvironment e)];
fun wsubjectView (input,(l,(p,(c,rows)))) = wobject [
  ("\"state\"",fn () => woption wstate input),
  ("\"locus\"",fn () => wtarget l),
  ("\"payload\"",fn () => wtarget p),
  ("\"cause\"",fn () => wtarget c),
  ("\"predecessors\"",fn () => wlist wpredecessor rows)];
fun wsubject x = wsubjectView (N.digit_generation_subject_view x);
fun wvalue result = woption (fn (state,(u,g)) => wobject [
  ("\"state\"",fn () => wstate state),
  ("\"use\"",fn () => print (juse u)),
  ("\"generation\"",fn () => wgeneration g)]) result;
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun woriginal (value,assessment) = wobject [
  ("\"value\"",fn () => wvalue value),
  ("\"assessment\"",fn () => woption wgenerationAssessment assessment),
  ("\"original_qualities\"",fn () => print (jlist jquality
    (map (fn f => (f,N.digit_generation_original_inspect assessment f)) originalFacets)))];
fun wresult (result,(reference,original)) = wobject [
  ("\"readings\"",fn () => wf wvalue result),
  ("\"reference_readings\"",fn () => wf wvalue reference),
  ("\"original_assessments\"",fn () => wf woriginal original)];
fun wcandidate (m,result) = wobject [
  ("\"method\"",fn () => print (jnat m)),
  ("\"result\"",fn () => wresult result)];
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.digit_generation_inspect result f)) facets) ^ "}";
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
val () = emit "DIGIT_GENERATION_SCOPE" (jlist jnat N.digit_generation_indices);
val () = let
val (table,(comparison,cycles)) = N.digit_generation_packet scope selections;
val () = List.app (fn (w,(context,cells)) => wemit ("DIGIT_GENERATION_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("DIGIT_GENERATION_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "DIGIT_GENERATION_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "DIGIT_GENERATION_INVESTIGATION" (jcycle c)) cycles;
val () = emit "DIGIT_GENERATION_SOURCE_SCOPE" (jlist jnat (N.digit_generation_source_scope scope));
val originals = N.digit_generation_source_cases scope;
val () = List.app (fn (w,(source,original)) => let
  val ((subject,(reference,variants)),cells) = lookup "subject" w table
  in wemit ("DIGIT_GENERATION_SOURCE " ^ jnat w) (fn () => wobject [
    ("\"initial_original_source\"",fn () => wgenerationProblem source),
    ("\"reference_input\"",fn () => wsubjectView original),
    ("\"projected_input\"",fn () => wsubject subject),
    ("\"construction_steps\"",fn () => print (jnat (N.digit_generation_chain_length w))),
    ("\"native_equal\"",fn () => print (Bool.toString (N.digit_generation_source_equal subject original)))]) end) originals;
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
        'RRA_Digit_Generation_Investigation', 'digit_generation_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports[0]['tag'] == 'DIGIT_GENERATION_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'DIGIT_GENERATION_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, reports[1 + i * size:1 + (i + 1) * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'DIGIT_GENERATION_COMPARISON' and compared['value']['scope'] == requested
        start = 2 + 2 * size
        assert all(r['tag'] == 'DIGIT_GENERATION_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[start:start + len(inputs['selections'])]))
        start += len(inputs['selections'])
        assert reports[start]['tag'] == 'DIGIT_GENERATION_SOURCE_SCOPE' and reports[start]['indices'] == []
        source_scope = reports[start]['value']
        assert source_scope == requested
        source_rows = reports[start + 1:]
        assert len(source_rows) == len(source_scope)
        assert all(r['tag'] == 'DIGIT_GENERATION_SOURCE' and r['indices'] == [w]
                   for w, r in zip(source_scope, source_rows))
        assert len(reports) == 2 * size + 3 + len(inputs['selections']) + len(source_scope)
        return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': source_scope,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every complete source, counter and environment, generation value, optional result, '
                            'original field reading and predecessor reference, independent original assessment, '
                            'actual observation, comparison and revision reason is retained.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Digit_Generation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=2400,
        question='Which actual persistent digit generation constructions preserve the whole original bounded '
                 'operation and every original generation condition through subsequent requests and reservations?',
        boundary='Whole optional operation equality retains an explicit allocation and reservation policy. '
                 'Original generation meaning is independently assessed; another fresh embedding can preserve '
                 'that meaning while differing from this operation. Full physical cost, complete development '
                 'adoption, all six workflow conditions, native mathematical-proof admission, historical '
                 'permission and reachability, and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
