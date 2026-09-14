"""Execute original literal-replay admission comparisons with complete native readings."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_native_certificates as shared
import investigate
import machine_reports
import native_replay_json
import observation_contracts
import proved_code
import requirement_decision_json


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Literal_Replay_Execution', 'literal_replay_indices')
    code += shared.native_graph_json.prelude('jsite') + admission_goal_json.PRELUDE
    code += shared.investigation_json.CYCLE
    code += 'structure Decision_JSON = struct\n' + requirement_decision_json.PRELUDE + '\nend;\n'
    code += 'structure Replay_JSON = struct\n' + native_replay_json.PRELUDE + '\nend;\n'
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
fun jsubject (e,(pu,(pr,(au,(ar,(root,a)))))) = "{\"environment\":" ^ jenv e ^
  ",\"program_use\":" ^ juse pu ^ ",\"program_address\":" ^ jaddress pr ^
  ",\"application_use\":" ^ juse au ^ ",\"application_address\":" ^ jaddress ar ^
  ",\"proof_root\":" ^ jsite root ^ ",\"payload\":" ^ jartifact (N.finite_artifact_rows a) ^ "}";
fun jreport (programs,(apps,(replays,a))) = "{\"package_readings\":" ^ jf jprogram programs ^
  ",\"application_readings\":" ^ jf Replay_JSON.japplicationReading apps ^
  ",\"replay_readings\":" ^ jf Replay_JSON.jassertions replays ^
  ",\"payload\":" ^ jartifact (N.finite_artifact_rows a) ^ "}";
fun jprepared (certificate,result) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"result\":" ^ jo (fn (x,report) => "{\"subject\":" ^ jsubject x ^
    ",\"readings\":" ^ jreport report ^ "}") result ^ "}";
fun jcontext (seed,(w,(covered,rows))) = "{\"seed\":" ^ jseed seed ^
  ",\"case\":" ^ jnat w ^ ",\"covered\":" ^ Bool.toString covered ^
  ",\"rows\":" ^ jf jprepared rows ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jrow row = let val (certificate,result) = row in
  "{\"certificate\":" ^ jcertificate certificate ^ ",\"result\":" ^ jo
    (fn (x,(report,(original,chosen))) => "{\"subject\":" ^ jsubject x ^
      ",\"readings\":" ^ jreport report ^ ",\"original\":" ^ Bool.toString original ^
      ",\"chosen\":" ^ Bool.toString chosen ^ "}") result ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.literal_replay_row_inspect row f)) facets) ^ "}" end;
fun jfamily (covered,rows) = "{\"covered\":" ^ Bool.toString covered ^
  ",\"rows\":" ^ jf jrow rows ^ "}";
fun jcandidate (m,assessment) = "{\"method\":" ^ jnat m ^
  ",\"assessment\":" ^ jfamily assessment ^ "}";
fun jassessed (m,assessment) = "{\"method\":" ^ jnat m ^
  ",\"qualities\":" ^ jlist jquality
    (map (fn f => (f,N.literal_replay_family_inspect assessment f)) facets) ^ "}";
val () = print ("LITERAL_REPLAY_SCOPE " ^ jlist jnat N.literal_replay_indices ^ "\n");
val (seed,(table,(comparison,cycles))) = N.literal_replay_packet scope selections;
val () = print ("LITERAL_REPLAY_SEED " ^ jseed seed ^ "\n");
val () = List.app (fn (w,(context,cells)) => print ("LITERAL_REPLAY_SUBJECT " ^ jnat w ^
  " {\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n")) table;
val () = List.app (fn (w,(context,cells)) => print ("LITERAL_REPLAY_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jassessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("LITERAL_REPLAY_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("LITERAL_REPLAY_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Literal_Replay_Investigation', 'literal_replay_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'LITERAL_REPLAY_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 3 + len(inputs['selections'])
        assert reports[1]['tag'] == 'LITERAL_REPLAY_SEED' and reports[1]['indices'] == []
        assert all(r['tag'] == 'LITERAL_REPLAY_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[2:2 + size]))
        assert all(r['tag'] == 'LITERAL_REPLAY_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[2 + size:2 + 2 * size]))
        compared = reports[2 + 2 * size]
        assert compared['tag'] == 'LITERAL_REPLAY_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'LITERAL_REPLAY_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[3 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The complete original seed, decision, keyed certificate and replay family, '
                            'every actual subject, all package, application and replay readings, '
                            'coverage, every method decision, soundness and completeness conditions, '
                            'comparisons and revisions are native results. The host checks reproduction only.'}

    modules = [shared, requirement_decision_json, native_replay_json, admission_goal_json,
               shared.check_reasoning, shared.investigation_json, shared.native_program_json,
               shared.native_history_json, shared.native_graph_json, shared.native_certificate_json,
               shared.program_evaluation_json]
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Literal_Replay_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(m.__file__) for m in modules), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which decisions accept exactly the actual closed native replays whose application '
                 'cites the whole requested payload, while rejecting malformed, missing or mismatched evidence?',
        boundary='Soundness and completeness use the independent original native replay and application '
                 'relations under registered observation equations. Nonempty valid coverage is computed '
                 'from the actual replay family. The explicitly empty test requirement family does not '
                 'establish whole-workflow policy adequacy. Arbitrary cause-value reading, workflow '
                 'transitions and subject coverage, historical permission, physical cost and genesis remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
