"""Compare full native history transitions under the retained original policy."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_certificate_json
import native_program_json
import native_stream_json
import observation_contracts
import program_evaluation_json
import proved_code
import stream_reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Required_History_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += program_evaluation_json.PRELUDE + '\nfun jcall q = jcallWith jsite q;\n'
    code += native_certificate_json.PROOFS + admission_goal_json.PRELUDE
    code += investigation_json.PRELUDE + investigation_json.CYCLE + native_stream_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.required_history_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun wmember (site,g) = (print "["; print (jsite site); print ","; wgeneration g; print "]");
fun wstate q = wobject [
  ("\"source_environment\"",fn () => wenvironment (N.required_history_source q)),
  ("\"source_use\"",fn () => print (juse (N.required_history_source_use q))),
  ("\"source_address\"",fn () => waddress (N.required_history_source_root q)),
  ("\"requirements\"",fn () => wlist (wencoded (jgoalWith jsite)) (N.required_history_goals q)),
  ("\"entry\"",fn () => print (jsite (N.required_history_entry q))),
  ("\"policy_environment\"",fn () => wenvironment (N.required_history_policy q)),
  ("\"policy_use\"",fn () => print (juse (N.required_history_policy_use q))),
  ("\"generation_material\"",fn () => wenvironment (N.required_history_material q)),
  ("\"admitted_members\"",fn () => wlist wmember (N.required_history_members q))];
fun winput (N.History_Step (l,rows,e,pu,pr,au,ar,root,r)) = wobject [
  ("\"locus\"",fn () => wtarget l),
  ("\"predecessor_rows\"",fn () => wlist wmember rows),
  ("\"replay_environment\"",fn () => wenvironment e),
  ("\"program_use\"",fn () => print (juse pu)),
  ("\"program_address\"",fn () => waddress pr),
  ("\"application_use\"",fn () => print (juse au)),
  ("\"application_address\"",fn () => waddress ar),
  ("\"proof_root\"",fn () => print (jsite root)),
  ("\"payload\"",fn () => wartifact (N.finite_artifact_rows r))];
fun wsubject (q,input) = wobject [
  ("\"previous_state\"",fn () => wstate (N.raw_required_history q)),
  ("\"requested_step\"",fn () => winput input)];
fun wsourceRow (key,input) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input\"",fn () => woption wsubject input)];
fun wsubjects subjects = wf wsourceRow subjects;
fun woutputRow (key,result) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input_result\"",fn () => woption (fn following => wobject [
    ("\"next_state\"",fn () => woption wstate following)]) result)];
'''
    code += stream_reader_comparison_json.prelude('woutputRow', 'wsubjects', 'required_history_inspect')
    code += r'''
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun jcoverage (total,available) = "{\"certificate_positions\":" ^ jnat total ^
  ",\"available_positions\":" ^ jnat available ^ "}";
val () = emit "REQUIRED_HISTORY_SCOPE" (jlist jnat N.required_history_indices);
val timer = Timer.startRealTimer ();
val (table,(comparison,cycles)) = N.required_history_packet scope selections;
val () = print ("Physicaltime required-history-packet " ^
  LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => wemit ("REQUIRED_HISTORY_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("REQUIRED_HISTORY_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "REQUIRED_HISTORY_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "REQUIRED_HISTORY_INVESTIGATION" (jcycle c)) cycles;
val () = List.app (fn (w,((subjects,reference),cells)) => emit ("REQUIRED_HISTORY_COVERAGE " ^ jnat w)
  (jcoverage (N.required_history_subject_coverage subjects))) table;
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
        'Factor_Required_History_Investigation', 'required_history_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path, deferred=True))
        assert rows[0]['tag'] == 'REQUIRED_HISTORY_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 3 * size + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'REQUIRED_HISTORY_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 2 * size]
        assert compared['tag'] == 'REQUIRED_HISTORY_COMPARISON' and compared['value']['scope'] == requested
        start = 2 + 2 * size
        assert all(r['tag'] == 'REQUIRED_HISTORY_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[start:start + len(inputs['selections'])]))
        assert all(r['tag'] == 'REQUIRED_HISTORY_COVERAGE' and r['indices'] == [w]
                   for w, r in zip(requested, rows[start + len(inputs['selections']):]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every certificate and unavailable position, original state field, '
                            'requested predecessor row and replay field, complete candidate state, '
                            'native condition, comparison, revision and position count is retained.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Required_History_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=2400,
        question='Which operations preserve the whole original request and state while admitting '
                 'only actual replayed causes whose exact predecessors occur in the retained admission ledger?',
        boundary='The abstract state type carries original payload requirement truth. The exact '
                 'transition contract checks actual predecessor membership, joined replay, original '
                 'policy cause and every output field. Adequate workflow requirements, complete '
                 'historical permission, reachability, full physical cost and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
