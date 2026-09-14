"""Execute complete native generation-record comparisons and their subject contracts."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Generation_Record_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.generation_record_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jgeneration (N.Generation (l,ps,p,c)) = "{\"locus\":" ^ jtarget l ^
  ",\"predecessors\":" ^ jf jgeneration ps ^ ",\"payload\":" ^ jtarget p ^ ",\"cause\":" ^ jtarget c ^ "}";
fun jpredecessor (d,g) = "{\"site\":" ^ jsite d ^ ",\"generation\":" ^ jgeneration g ^ "}";
fun jsubject (e,(l,(p,(c,rows)))) = "{\"environment\":" ^ jenv e ^ ",\"locus\":" ^ jtarget l ^
  ",\"payload\":" ^ jtarget p ^ ",\"cause\":" ^ jtarget c ^ ",\"predecessors\":" ^ jlist jpredecessor rows ^ "}";
fun jresult result = jo (fn (e,(u,g)) => "{\"environment\":" ^ jenv e ^ ",\"use\":" ^ juse u ^
  ",\"generation\":" ^ jgeneration g ^ "}") result;
fun jchecked (row,b) = "{\"predecessor\":" ^ jpredecessor row ^ ",\"checked\":" ^ Bool.toString b ^ "}";
fun joriginal (formed,(l,(p,(c,(distinct,checks))))) = "{\"environment_formed\":" ^ Bool.toString formed ^
  ",\"locus_formed\":" ^ Bool.toString l ^ ",\"payload_formed\":" ^ Bool.toString p ^
  ",\"cause_formed\":" ^ Bool.toString c ^ ",\"predecessor_values_distinct\":" ^ Bool.toString distinct ^
  ",\"predecessor_checks\":" ^ jlist jchecked checks ^ "}";
fun jsocket (s,d) = "[" ^ jaddress s ^ "," ^ jaddress d ^ "]";
fun jfields (l,(ms,(p,c))) = "{\"locus\":" ^ jtarget l ^ ",\"sockets\":" ^ jf jsocket ms ^
  ",\"payload\":" ^ jtarget p ^ ",\"cause\":" ^ jtarget c ^ "}";
fun jbody (fields,(refs,(l,(p,(c,(preds,(formed,(native,(preserved,original))))))))) =
  "{\"field_readings\":" ^ jf jfields fields ^ ",\"actual_predecessor_sites\":" ^ jf jsite refs ^
  ",\"locus_exact\":" ^ Bool.toString l ^ ",\"payload_exact\":" ^ Bool.toString p ^
  ",\"cause_exact\":" ^ Bool.toString c ^ ",\"predecessor_values_exact\":" ^ Bool.toString preds ^
  ",\"environment_formed\":" ^ Bool.toString formed ^ ",\"native_generation\":" ^ Bool.toString native ^
  ",\"old_environment_preserved\":" ^ Bool.toString preserved ^ ",\"original_references\":" ^ Bool.toString original ^ "}";
fun jassessment (ready,(available,body)) = "{\"ready\":" ^ Bool.toString ready ^
  ",\"available\":" ^ Bool.toString available ^ ",\"result\":" ^ jo jbody body ^ "}";
fun jbase (m,r) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult r ^ "}";
fun jcontext (x,(ready,(original,bases))) = "{\"subject\":" ^ jsubject x ^
  ",\"ready\":" ^ Bool.toString ready ^ ",\"original\":" ^ joriginal original ^
  ",\"bases\":" ^ jlist jbase bases ^ "}";
fun jcandidate (m,(x,(result,a))) = "{\"method\":" ^ jnat m ^ ",\"subject\":" ^ jsubject x ^
  ",\"result\":" ^ jresult result ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,(x,(result,a))) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.generation_record_inspect a f)) facets) ^ "}";
val () = print ("GENERATION_RECORD_SCOPE " ^ jlist jnat N.generation_record_indices ^ "\n");
val (table,(comparison,cycles)) = N.generation_record_packet scope selections;
val () = List.app (fn (w,(context,cells)) => print ("GENERATION_RECORD_SUBJECT " ^ jnat w ^
  " {\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n")) table;
val () = List.app (fn (w,(context,cells)) => print ("GENERATION_RECORD_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jassessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("GENERATION_RECORD_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("GENERATION_RECORD_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'RRA_Generation_Record_Investigation', 'generation_record_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'GENERATION_RECORD_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'GENERATION_RECORD_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'GENERATION_RECORD_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'GENERATION_RECORD_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'GENERATION_RECORD_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original generation-record inputs, every candidate environment and core, '
                            'original premise checks, actual field readings and predecessor references, '
                            'all derived conditions, comparisons and revisions are native results. '
                            'The host checks reproduction only.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Generation_Record_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], list(range(7)), list(range(9))]},
        input_paths=[Path(__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual native generation-record constructions recover the requested targets and '
                 'predecessor values, preserve every old artifact and binding, retain every original '
                 'predecessor use and address, and refuse every unready input?',
        boundary='Complete actual generation subjects and original RRA conditions have registered '
                 'observation equations. Native cause truth, whole-workflow transitions and subject '
                 'coverage, historical permission, physical cost and genesis remain separate requirements.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
