"""Compare actual generation cause admission, retaining every source and native reading."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_native_certificates as shared
import investigate
import machine_reports
import native_replay_json
import native_stream_json
import observation_contracts
import proved_code
import requirement_decision_json


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Certified_Cause_Execution', 'certified_cause_indices')
    code += shared.native_graph_json.prelude('jsite') + admission_goal_json.PRELUDE
    code += shared.investigation_json.CYCLE
    code += 'structure Decision_JSON = struct\n' + requirement_decision_json.PRELUDE + '\nend;\n'
    code += 'structure Replay_JSON = struct\n' + native_replay_json.PRELUDE + '\nend;\n'
    code += native_stream_json.PRELUDE
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jreplayRow (certificate,result) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"result\":" ^ Replay_JSON.jresult result ^ "}";
fun jdecision (decision,replays) = "{\"decision\":" ^ Decision_JSON.jresult decision ^
  ",\"replays\":" ^ jf jreplayRow replays ^ "}";
fun jseed seed = jo (fn (e,(u,(r,(a,decision)))) => "{\"environment\":" ^ jenv e ^
  ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^
  ",\"payload\":" ^ jartifact (N.finite_artifact_rows a) ^
  ",\"decision_replay\":" ^ jo jdecision decision ^ "}") seed;
fun jjudgment (e,(pu,(pr,(au,ar)))) = "{\"environment\":" ^ jenv e ^
  ",\"program_use\":" ^ juse pu ^ ",\"program_address\":" ^ jaddress pr ^
  ",\"application_use\":" ^ juse au ^ ",\"application_address\":" ^ jaddress ar ^ "}";
fun jreading (q,(least,(programs,(apps,(replays,(literal,(included,(canonical,words)))))))) =
  "{\"judgment\":" ^ jjudgment q ^ ",\"least_judgment_environment\":" ^ jenv least ^
  ",\"package_readings\":" ^ jf jprogram programs ^
  ",\"application_readings\":" ^ jf Replay_JSON.japplicationReading apps ^
  ",\"replay_readings\":" ^ jf Replay_JSON.jassertions replays ^
  ",\"literal_application_matches\":" ^ Bool.toString literal ^
  ",\"scope_included\":" ^ Bool.toString included ^
  ",\"canonical_quotation\":" ^ Bool.toString canonical ^
  ",\"byte_valued_use_words\":" ^ Bool.toString words ^ "}";
fun jreport (present,(payload,rows)) = "{\"actual_generation\":" ^ Bool.toString present ^
  ",\"payload_matches\":" ^ Bool.toString payload ^ ",\"scope_readings\":" ^ jf jreading rows ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,assessment) = "{\"method\":" ^ jnat m ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.decision_family_inspect assessment f)) facets) ^ "}";
fun emit tag data = (print (tag ^ " " ^ data ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun wsubject (e,(u,(r,(g,(h,(root,a)))))) = wobject [
  ("\"generation_environment\"",fn () => wenvironment e),
  ("\"generation_use\"",fn () => print (juse u)),
  ("\"generation_address\"",fn () => waddress r),
  ("\"generation\"",fn () => wgeneration g),
  ("\"replay_environment\"",fn () => wenvironment h),
  ("\"proof_root\"",fn () => print (jsite root)),
  ("\"payload\"",fn () => wartifact (N.finite_artifact_rows a))];
fun wprepared (certificate,result) = wobject [
  ("\"certificate\"",fn () => print (jcertificate certificate)),
  ("\"result\"",fn () => woption (fn (x,report) => wobject [
    ("\"subject\"",fn () => wsubject x),
    ("\"readings\"",fn () => print (jreport report))]) result)];
fun wcontext (seed,(w,(covered,rows))) = wobject [
  ("\"seed\"",fn () => print (jseed seed)),
  ("\"case\"",fn () => print (jnat w)),
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"rows\"",fn () => wf wprepared rows)];
fun wrow row = let val (certificate,result) = row in wobject [
  ("\"certificate\"",fn () => print (jcertificate certificate)),
  ("\"result\"",fn () => woption (fn (x,(report,(original,chosen))) => wobject [
    ("\"subject\"",fn () => wsubject x),
    ("\"readings\"",fn () => print (jreport report)),
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
val () = emit "CERTIFIED_CAUSE_SCOPE" (jlist jnat N.certified_cause_indices);
val timer = Timer.startRealTimer ();
val (seed,(table,(comparison,cycles))) = N.certified_cause_packet scope selections;
val () = print ("Physicaltime native-cause-comparison " ^
  LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = emit "CERTIFIED_CAUSE_SEED" (jseed seed);
val () = List.app (fn (w,(context,cells)) => wemit ("CERTIFIED_CAUSE_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("CERTIFIED_CAUSE_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "CERTIFIED_CAUSE_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "CERTIFIED_CAUSE_INVESTIGATION" (jcycle c)) cycles;
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
        'Factor_Certified_Cause_Investigation', 'certified_cause_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'CERTIFIED_CAUSE_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 3 + len(inputs['selections'])
        assert reports[1]['tag'] == 'CERTIFIED_CAUSE_SEED' and reports[1]['indices'] == []
        assert all(r['tag'] == 'CERTIFIED_CAUSE_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[2:2 + size]))
        assert all(r['tag'] == 'CERTIFIED_CAUSE_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[2 + size:2 + 2 * size]))
        compared = reports[2 + 2 * size]
        assert compared['tag'] == 'CERTIFIED_CAUSE_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'CERTIFIED_CAUSE_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[3 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every original seed, generation source and core, retained proof source, recovered '
                            'judgment and least environment, package, application and replay reading, method '
                            'decision, derived condition, comparison and revision is a native result. The '
                            'host checks complete report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Certified_Cause_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=3600,
        question='Which methods accept exactly the original certified generation causes while preserving '
                 'all allowed quotation layouts, whole scopes, payload identities and actual retained replays?',
        boundary='Registered all-input observation equations connect actual complete subjects and native '
                 'readings to the original certified-base-cause relation. An actually valid seed is required '
                 'for coverage. The empty test history and requirement policy do not establish full workflow '
                 'policy, historical permission, candidate and criticism coverage, the full cost account or genesis.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
