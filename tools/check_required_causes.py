"""Compare actual cause admission under the complete original requirement policy."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_native_certificates as shared
import investigate
import machine_reports
import native_cause_json
import native_stream_json
import observation_contracts
import proved_code
import requirement_decision_json


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Required_Cause_Execution', 'required_cause_indices')
    code += admission_goal_json.PRELUDE + shared.investigation_json.CYCLE
    code += native_stream_json.PRELUDE + native_cause_json.SUBJECT
    code += 'structure Decision_JSON = struct\n' + requirement_decision_json.PRELUDE + '\nend;\n'
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jjudgment (e,(pu,(pr,(au,ar)))) = "{\"environment\":" ^ jenv e ^
  ",\"program_use\":" ^ juse pu ^ ",\"program_address\":" ^ jaddress pr ^
  ",\"application_use\":" ^ juse au ^ ",\"application_address\":" ^ jaddress ar ^ "}";
fun japplication ((d,t),(inside,slots)) = "{\"call\":" ^ jcall (d,t) ^
  ",\"interior\":" ^ jf jaddress inside ^ ",\"slots\":" ^ jf jaddress slots ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,assessment) = "{\"method\":" ^ jnat m ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.decision_family_inspect assessment f)) facets) ^ "}";
fun wrequest (s,(u,(r,goals))) = wobject [
  ("\"source_environment\"",fn () => wenvironment s),
  ("\"source_use\"",fn () => print (juse u)),
  ("\"source_address\"",fn () => waddress r),
  ("\"requirements\"",fn () => wlist (wencoded (jgoalWith jsite)) goals)];
fun wsubject (request,cause) = wobject [
  ("\"original_request\"",fn () => wrequest request),
  ("\"cause_subject\"",fn () => wcause cause)];
fun wsource (d,(k,pu)) = wobject [
  ("\"entry\"",fn () => print (jsite d)),
  ("\"environment\"",fn () => wenvironment k),
  ("\"program_use\"",fn () => print (juse pu))];
fun walignment (q,(site,(scope,(apps,entry)))) = wobject [
  ("\"judgment\"",fn () => print (jjudgment q)),
  ("\"site_matches\"",fn () => print (Bool.toString site)),
  ("\"scope_matches\"",fn () => print (Bool.toString scope)),
  ("\"application_readings\"",fn () => wf (wencoded japplication) apps),
  ("\"entry_and_literal_match\"",fn () => print (Bool.toString entry))];
fun wpolicy (source,(programs,rows)) = wobject [
  ("\"constructed_policy\"",fn () => wsource source),
  ("\"package_readings\"",fn () => wf (wencoded jprogram) programs),
  ("\"alignments\"",fn () => wf walignment rows)];
fun wreport (certified,(scopes,(policy,decision))) = wobject [
  ("\"original_cause_certified\"",fn () => print (Bool.toString certified)),
  ("\"generation_judgments\"",fn () => wf (wencoded jjudgment) scopes),
  ("\"original_policy\"",fn () => woption wpolicy policy),
  ("\"original_requirement_decision\"",fn () => print (jo Decision_JSON.jresult decision))];
fun wprepared (key,result) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"result\"",fn () => woption (fn (x,report) => wobject [
    ("\"subject\"",fn () => wsubject x),
    ("\"readings\"",fn () => wreport report)]) result)];
fun wcontext (w,(covered,rows)) = wobject [
  ("\"case\"",fn () => print (jnat w)),
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"rows\"",fn () => wf wprepared rows)];
fun wrow row = let val (key,result) = row in wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"result\"",fn () => woption (fn (x,(report,(original,chosen))) => wobject [
    ("\"subject\"",fn () => wsubject x),
    ("\"readings\"",fn () => wreport report),
    ("\"original\"",fn () => print (Bool.toString original)),
    ("\"chosen\"",fn () => print (Bool.toString chosen))]) result),
  ("\"qualities\"",fn () => wlist (wencoded jquality)
    (map (fn f => (f,N.decision_row_inspect row f)) facets))] end;
fun wfamily (covered,rows) = wobject [
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"rows\"",fn () => wf wrow rows)];
fun wcandidate (m,assessment) = wobject [
  ("\"method\"",fn () => print (jnat m)),
  ("\"assessment\"",fn () => wfamily assessment)];
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "REQUIRED_CAUSE_SCOPE" (jlist jnat N.required_cause_indices);
val timer = Timer.startRealTimer ();
val (table,(comparison,cycles)) = N.required_cause_packet scope selections;
val () = print ("Physicaltime required-cause-comparison " ^
  LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => wemit ("REQUIRED_CAUSE_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("REQUIRED_CAUSE_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "REQUIRED_CAUSE_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "REQUIRED_CAUSE_INVESTIGATION" (jcycle c)) cycles;
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
        'Factor_Required_Cause_Investigation', 'required_cause_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'REQUIRED_CAUSE_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'REQUIRED_CAUSE_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 2 * size]
        assert compared['tag'] == 'REQUIRED_CAUSE_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'REQUIRED_CAUSE_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original requests, constructed policies, actual generations, native '
                            'judgments, application readings, entry and scope comparisons, original conditions '
                            'and every native revision reason are retained. The host checks report reproduction.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Required_Cause_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=3600,
        question='Which methods bind a complete certified cause to the policy constructed from the original '
                 'requirement request, preserving its actual source, scope and called entry?',
        boundary='The exact policy gate entails every original goal under its original source meaning. '
                 'Its policy identity condition is separate from admitting alternative proved policy '
                 'realizations. Full workflow-policy adequacy, enforced transitions, historical permission, '
                 'complete criticism coverage and physical cost remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
