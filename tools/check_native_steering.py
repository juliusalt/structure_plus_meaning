"""Run the closed native development cycle on its actual producer comparison."""
from pathlib import Path
from contextlib import closing
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import investigate
import observation_contracts
import native_development_input
import native_development_json
import workflow_input
import workflow_json
import native_stage_timing


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Steering', 'native_development_indices')
    code += shared.investigation_json.CYCLE + native_development_json.PRELUDE
    questions = inputs['questions']
    default_questions = 'List.take (N.development_case_inputs, 1)' if inputs['first'] else 'N.development_case_inputs'
    code += ('val questions = ' + default_questions + ';\n' if questions is None else
             'val questions = [' + ','.join(native_development_input.question(q) for q in questions) + '];\n')
    requests = inputs['requests']
    code += ('val requests = N.development_case_inputs;\n' if requests is None else
             'val requests = [' + ','.join(native_development_input.question(q) for q in requests) + '];\n')
    code += native_stage_timing.PRELUDE + r"""
val (originalRequests,(steering,(chosen,results))) = native_stage_timed "steering"
  (fn () => N.native_steered_development questions requests);
val physical_report_clock = Timer.startRealTimer ();
val (originals,(table,execution)) = steering;
val () = print ("STEERING_SCOPE {\"question_count\":" ^ Int.toString (length originals) ^ ",\"request_count\":" ^ Int.toString (length originalRequests) ^
  ",\"methods\":" ^ jlist jnat N.development_methods ^ ",\"facets\":" ^ jlist jnat N.development_facets ^ "}\n");
val () = List.app (fn (w,((question,(original,reference)),cells)) =>
  (print ("STEERING_CONTEXT " ^ jnat w ^ " {\"question\":" ^ jdevelopmentQuestion question ^
    ",\"original\":" ^ jdevelopmentReport original ^ ",\"reference\":" ^ jdevelopmentDecision reference ^ "}\n");
   List.app (fn (m,(actual,assessment)) => print ("STEERING_CANDIDATE " ^ jnat w ^ " " ^ jnat m ^
    " " ^ jdevelopmentResult actual ^ "\n")) cells)) table;
val () = List.app (fn (w,(context,cells)) => print ("STEERING_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jdevelopmentAssessed cells ^ "\n")) table;
val () = (case execution of NONE =>
    print "STEERING_QUESTION null\nSTEERING_REPORT null\nSTEERING_ADMISSION null\nSTEERING_METHODS null\n"
  | SOME (question,(report,(admission,methods))) =>
    (print ("STEERING_QUESTION " ^ jdevelopmentQuestion question ^ "\n");
     print ("STEERING_REPORT " ^ jdevelopmentReport report ^ "\n");
     print ("STEERING_ADMISSION " ^ jdevelopmentDecision admission ^ "\n");
     print ("STEERING_METHODS " ^ joption (jlist jnat) methods ^ "\n")));
fun eachIndexed f xs = let
  fun walk i [] = () | walk i (x::rest) = (f (i,x); walk (i+1) rest)
  in walk 0 xs end;
val () = eachIndexed (fn (i,Q) => print ("STEERED_REQUEST " ^ Int.toString i ^ " " ^ jdevelopmentQuestion Q ^ "\n")) originalRequests;
val () = print ("STEERED_CHOICE " ^ joption jnat chosen ^ "\n");
val () = print ("STEERED_AVAILABLE " ^ Bool.toString (Option.isSome results) ^ "\n");
fun jsteeredResult (m,(Q,(report,(claim,admission)))) = "{\"method\":" ^ jnat m ^
  ",\"question\":" ^ jdevelopmentQuestion Q ^ ",\"report\":" ^ jdevelopmentReport report ^
  ",\"claim\":" ^ jdevelopmentDecision claim ^ ",\"admission\":" ^ jdevelopmentDecision admission ^ "}";
val () = (case results of NONE => () | SOME rows => eachIndexed
  (fn (i,result) => print ("STEERED_RESULT " ^ Int.toString i ^ " " ^ jsteeredResult result ^ "\n")) rows);
"""
    return code + native_stage_timing.REPORT_END


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--questions', type=Path, help='Complete original question list; defaults to native cases.')
    group.add_argument('--empty', action='store_true', help='Submit the empty original question scope.')
    group.add_argument('--first', action='store_true', help='Submit only the first complete native question.')
    parser.add_argument('--requests', type=Path, help='New complete requests; defaults to native cases.')
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    questions = [] if args.empty else None
    if args.questions:
        questions = json.loads(args.questions.read_text(), object_pairs_hook=workflow_input.unique_object)
        assert isinstance(questions, list)
        for q in questions:
            native_development_input.question(q)
    requests = None
    if args.requests:
        requests = json.loads(args.requests.read_text(), object_pairs_hook=workflow_input.unique_object)
        assert isinstance(requests, list)
        for q in requests:
            native_development_input.question(q)
    proof = json.loads(args.proof.read_text())
    contracts = [c for c in proof['subject_contracts'] if Path(c['path']).stem == 'development_subject_investigation']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Development_Subjects', 'development_subject_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, log):
        with closing(machine_reports.reports(log, deferred=True)) as records:
            first = next(records)
            assert first['tag'] == 'STEERING_SCOPE' and first['indices'] == []
            scope = first['value']
            assert scope['methods'] == inputs['candidates'] and scope['facets'] == inputs['facets']
            size = scope['question_count']
            if inputs['questions'] is not None:
                assert size == len(inputs['questions'])
            for w in range(size):
                r = next(records)
                assert r['tag'] == 'STEERING_CONTEXT' and r['indices'] == [w]
                if inputs['questions'] is not None:
                    assert machine_reports.field(r, 'question') == inputs['questions'][w]
                for m in inputs['candidates']:
                    r = next(records)
                    assert r['tag'] == 'STEERING_CANDIDATE' and r['indices'] == [w, m]
            for w in range(size):
                r = next(records)
                assert r['tag'] == 'STEERING_ASSESSMENT' and r['indices'] == [w]
                assert [row['method'] for row in r['value']] == inputs['candidates']
                assert all([f for f, _ in row['qualities']] == inputs['facets'] for row in r['value'])
            for tag in ['STEERING_QUESTION', 'STEERING_REPORT', 'STEERING_ADMISSION', 'STEERING_METHODS']:
                r = next(records)
                assert r['tag'] == tag and r['indices'] == []
            request_count = scope['request_count']
            if inputs['requests'] is not None:
                assert request_count == len(inputs['requests'])
            for i in range(request_count):
                r = next(records)
                assert r['tag'] == 'STEERED_REQUEST' and r['indices'] == [i]
                if inputs['requests'] is not None:
                    assert r['value'] == inputs['requests'][i]
            r = next(records)
            assert r['tag'] == 'STEERED_CHOICE' and r['indices'] == []
            r = next(records)
            assert r['tag'] == 'STEERED_AVAILABLE' and r['indices'] == [] and type(r['value']) is bool
            if r['value']:
                for i in range(request_count):
                    r = next(records)
                    assert r['tag'] == 'STEERED_RESULT' and r['indices'] == [i]
                    assert machine_reports.value_keys(r) == {'method', 'question', 'report', 'claim', 'admission'}
                    if inputs['requests'] is not None:
                        assert machine_reports.field(r, 'question') == inputs['requests'][i]
            assert next(records, None) is None
            return {'scope': scope, 'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                    'boundary': 'Complete original subjects, computed producer results and observations, derived '
                        'native sources and every closed-cycle operation and result are transported unchanged. '
                        'The host supplies no satisfaction or selection flags.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Development_Steering'],
        inputs={'questions': questions, 'requests': requests, 'first': args.first, 'cases': [], 'candidates': contract['candidate_indices'],
                'facets': contract['facet_indices'], 'selections': []},
        input_paths=[Path(__file__), Path(native_development_input.__file__), Path(native_development_json.__file__),
                     Path(workflow_input.__file__), Path(workflow_json.__file__),
                     *(Path(c['path']) for c in contracts), *([args.questions.resolve()] if args.questions else []),
                     *([args.requests.resolve()] if args.requests else [])],
        workers=args.workers, program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual development producers satisfy every original condition on every complete original question, '
                 'when generation, native observations, criticism, comparison, revision and admission run as one closed cycle?',
        boundary='Original questions produce the complete computed subject table. The proved source constructor derives '
                 'native criteria from those actual observations. Every selected method is tied to all original subjects '
                 'by development_steering_original_conditions. This finite scope does not authorize the genesis handoff.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
