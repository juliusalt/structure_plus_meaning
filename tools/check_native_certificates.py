"""Execute complete certificate path, coordinate and graph comparisons."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import investigation_json
import machine_reports
import native_certificate_json
import native_graph_json
import native_history_json
import native_program_json
import observation_contracts
import program_evaluation_json
import proved_code


def source_preamble(engine, inputs, module="Native_Certificate_Investigation_Execution", scope_name="native_certificate_indices"):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = ' + module + ';\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE + investigation_json.PRELUDE
    code += native_history_json.SOURCE + native_certificate_json.PRELUDE
    code += native_graph_json.prelude('jaddress')
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.' + scope_name if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jproblemOption NONE = "null" | jproblemOption (SOME x) = jproblem x;
'''
    code += native_certificate_json.INSTANCES
    return code


def preamble(engine, inputs, module="Native_Certificate_Investigation_Execution", scope_name="native_certificate_indices"):
    code = source_preamble(engine, inputs, module, scope_name)
    code += r'''fun jmapping r = jf (fn (n,ss) => "[" ^ jinstantiated n ^ "," ^ jpath ss ^ "]") r;
fun jrow (n,(paths,(mapping,graph))) = "{\"root\":" ^ jinstantiated n ^
  ",\"paths\":" ^ jpaths paths ^ ",\"mapping\":" ^ jmapping mapping ^
  ",\"graph\":" ^ jgraphWith jpath graph ^ "}";
fun jresult NONE = "null"
  | jresult (SOME (p,(a,r))) = "{\"program\":" ^ jprogram p ^
      ",\"answer\":" ^ jf jcall a ^ ",\"rows\":" ^ jf jrow r ^ "}";
fun jrowInspection (paths,(graph,(exact,(mapping,coordinates)))) =
  "{\"original_paths\":" ^ jpaths paths ^ ",\"original_graph\":" ^ jgraphWith jinstantiated graph ^
  ",\"paths_exact\":" ^ Bool.toString exact ^ ",\"mapping_exact\":" ^ Bool.toString mapping ^
  ",\"actual_coordinates\":" ^ Bool.toString coordinates ^ "}";
fun jinspection (row,a) = "{\"row\":" ^ jrow row ^ ",\"inspection\":" ^ jrowInspection a ^ "}";
fun jbody NONE = "null"
  | jbody (SOME (answers,(source,(family,rows)))) =
      "{\"answers_exact\":" ^ Bool.toString answers ^ ",\"source_exact\":" ^ Bool.toString source ^
      ",\"family_exact\":" ^ Bool.toString family ^ ",\"rows\":" ^ jf jinspection rows ^ "}";
fun jassessment (ready,(body,rejected)) = "{\"ready\":" ^ Bool.toString ready ^
  ",\"result\":" ^ jbody body ^ ",\"rejected\":" ^ Bool.toString rejected ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jcandidate (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jassessed (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_certificate_inspect a f)) facets) ^ "}";
fun emitSubject (w,(x,(original,cells))) = print ("CERTIFICATE_SUBJECT " ^ jnat w ^
  " {\"problem\":" ^ jproblemOption x ^ ",\"original\":" ^ jderivation original ^
  ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n");
fun emitAssessment (w,(x,(original,cells))) = print ("CERTIFICATE_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jassessed cells ^ "\n");
'''
    code += investigation_json.CYCLE
    return code


def program(engine, inputs):
    code = preamble(engine, inputs)
    code += r'''val () = print ("CERTIFICATE_SCOPE " ^ jlist jnat N.native_certificate_indices ^ "\n");
val (table,(comparison,cycles)) = N.native_certificate_report_packet scope selections;
val () = List.app emitSubject table;
val () = List.app emitAssessment table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("CERTIFICATE_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("CERTIFICATE_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'Factor_Native_Certificate_Investigation', 'native_certificate_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path, deferred=True))
        assert reports and reports[0]['tag'] == 'CERTIFICATE_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'CERTIFICATE_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'CERTIFICATE_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'CERTIFICATE_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'CERTIFICATE_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original native inputs, source-derived programs, answers and certificates, '
                            'all actual candidate paths, coordinate maps and graphs, original reference paths '
                            'and graphs, every row inspection, comparisons and revisions are retained. '
                            'The proved packet supplies every observation; the launcher checks reproduction.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Certificate_Investigation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1, 2, 6], [0, 1, 2, 3, 4, 5, 6]]},
        input_paths=[Path(__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), Path(native_history_json.__file__),
                     Path(native_graph_json.__file__), Path(native_certificate_json.__file__),
                     Path(program_evaluation_json.__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual constructors preserve the complete original answer and certificate family, '
                 'retain every path and graph through actual source-path coordinates, and refuse unavailable inputs?',
        boundary='The exact observation equation retains the complete original native source and requested '
                 'calls, the source-derived certificate family, every actual candidate value and all seven '
                 'conditions. Full certificate-and-call nodes, complete independent path relations and '
                 'arbitrary graph correspondences remain explicit. This path-coordinate comparison does '
                 'not establish arbitrary-method or arbitrary-certificate coverage, native source positioning, '
                 'artifact placement, mathematical-proof checking, full development admission, physical cost or genesis.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
