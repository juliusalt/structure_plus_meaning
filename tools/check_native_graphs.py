"""Execute actual native graph constructors and their complete condition investigation."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_Graph_Investigation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.TARGETS + program_evaluation_json.PRELUDE
    code += investigation_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.native_graph_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jenv e = jenvironment
  (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jnode N.Finite_Assertion = "{\"kind\":\"assertion\"}"
  | jnode (N.Finite_Inference (c,v)) = "{\"kind\":\"inference\",\"clause\":" ^ jsite c ^
      ",\"bindings\":" ^ jf (jbindingWith jsite) v ^ "}";
fun jgraphWith key g = "{\"inferences\":" ^
  jf (fn (n,v) => "[" ^ key n ^ "," ^ jnode v ^ "]") (N.finite_graph_inferences g) ^
  ",\"discharges\":" ^ jf (fn ((n,s),q) => "[[" ^ key n ^ "," ^ jsite s ^ "]," ^ key q ^ "]")
    (N.finite_graph_discharges g) ^ "}";
fun jproblem (x as (e,(g,root))) = let
  val (formed,(graph,metadata)) = N.native_graph_input_inspection x
in "{\"environment\":" ^ jenv e ^ ",\"graph\":" ^ jgraphWith jaddress g ^
  ",\"root\":" ^ jaddress root ^ ",\"prerequisites\":{\"environment\":" ^ Bool.toString formed ^
  ",\"graph\":" ^ Bool.toString graph ^ ",\"metadata\":" ^ Bool.toString metadata ^ "}}" end;
fun jresult NONE = "null"
  | jresult (SOME (f,(mapping,(r,g)))) = "{\"environment\":" ^ jenv f ^
      ",\"mapping\":" ^ jf (fn (n,s) => "[" ^ jaddress n ^ "," ^ jsite s ^ "]") mapping ^
      ",\"root\":" ^ jsite r ^ ",\"graph\":" ^ jgraphWith jsite g ^ "}";
fun jbody NONE = "null"
  | jbody (SOME (readings,(recovery,(mapping,(source,(fresh,injective)))))) =
      "{\"readings\":" ^ jf (jgraphWith jsite) readings ^ ",\"recovered\":" ^ Bool.toString recovery ^
      ",\"mapping\":" ^ Bool.toString mapping ^ ",\"source_retained\":" ^ Bool.toString source ^
      ",\"fresh\":" ^ Bool.toString fresh ^ ",\"injective\":" ^ Bool.toString injective ^ "}";
fun jassessment (ready,(body,rejected)) = "{\"ready\":" ^ Bool.toString ready ^
  ",\"result\":" ^ jbody body ^ ",\"rejected\":" ^ Bool.toString rejected ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jcandidate (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jassessed (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_graph_inspect a f)) facets) ^ "}";
fun emitSubject (w,(x,cells)) = print ("GRAPH_SUBJECT " ^ jnat w ^ " {\"problem\":" ^ jproblem x ^
  ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n");
fun emitAssessment (w,(x,cells)) = print ("GRAPH_ASSESSMENT " ^ jnat w ^ " " ^ jlist jassessed cells ^ "\n");
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";
val () = print ("GRAPH_SCOPE " ^ jlist jnat N.native_graph_indices ^ "\n");
val (table,(comparison,cycles)) = N.native_graph_report_packet scope selections;
val () = List.app emitSubject table;
val () = List.app emitAssessment table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("GRAPH_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("GRAPH_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'Factor_Native_Graph_Investigation', 'native_graph_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'GRAPH_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'GRAPH_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'GRAPH_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        assert reports[1 + 2 * size]['tag'] == 'GRAPH_COMPARISON'
        assert reports[1 + 2 * size]['value']['scope'] == requested
        assert all(r['tag'] == 'GRAPH_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The complete original source, graph, root, actual prerequisite inspections, returned environments, '
                            'complete mappings and graphs, native readings, assessments, comparisons and revisions are retained. '
                            'The proved native packet constructs all semantic observations and decisions.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Graph_Investigation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases,
                'selections': [[], [0, 2, 3, 5], [0, 1, 2, 3, 4, 5],
                               [0, 2, 3, 5, 1], [0, 1, 2, 4, 5]]},
        input_paths=[Path(__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), Path(program_evaluation_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual whole-graph constructors recover every original node and indexed edge through '
                 'a fresh injective correspondence, preserve the complete source and refuse unavailable inputs?',
        boundary='The observation equation connects actual methods and complete original source and graph '
                 'inputs to six independent construction conditions. Every actual returned graph is checked '
                 'through the native reader. Complete relation images retain metadata and indexed edges '
                 'without restricting candidates to a canonical placement. The original universal constructor '
                 'contract remains required. This finite comparison does not validate inference claims, '
                 'position or flatten certificates, check native mathematical proofs, enforce the complete '
                 'development cycle, establish the whole cost account or authorize genesis.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
