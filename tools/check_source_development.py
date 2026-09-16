"""Use the computed native workflow to install an admitted source and query it."""
from pathlib import Path
from contextlib import closing
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import investigate
import native_development_input
import observation_contracts
import source_development_input
import source_development_json
import workflow_input


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Source_Development', 'native_development_indices')
    code += shared.investigation_json.CYCLE + source_development_json.PRELUDE
    default = 'List.take (N.development_case_inputs, 1)' if inputs['first'] else 'N.development_case_inputs'
    code += 'val questions = ' + (default if inputs['questions'] is None else
        '[' + ','.join(native_development_input.question(q) for q in inputs['questions']) + ']') + ';\n'
    code += 'val requests = ' + ('N.source_development_cases' if inputs['requests'] is None else
        '[' + ','.join(source_development_input.request(r) for r in inputs['requests']) + ']') + ';\n'
    code += r'''
val (originalRequests,(policy,results)) = N.native_source_development questions requests;
val (policyRequests,(steering,(chosen,policyResults))) = policy;
val (originals,(table,execution)) = steering;
val () = print ("SOURCE_SCOPE {\"question_count\":" ^ Int.toString (length originals) ^
  ",\"request_count\":" ^ Int.toString (length originalRequests) ^ ",\"methods\":" ^ jlist jnat N.development_methods ^
  ",\"facets\":" ^ jlist jnat N.development_facets ^ "}\n");
val () = List.app (fn (w,((question,(original,reference)),cells)) =>
  (print ("SOURCE_POLICY_CONTEXT " ^ jnat w ^ " {\"question\":" ^ jdevelopmentQuestion question ^
    ",\"original\":" ^ jdevelopmentReport original ^ ",\"reference\":" ^ jdevelopmentDecision reference ^ "}\n");
   List.app (fn (m,(actual,assessment)) => print ("SOURCE_POLICY_CANDIDATE " ^ jnat w ^ " " ^ jnat m ^
    " " ^ jdevelopmentResult actual ^ "\n")) cells)) table;
val () = List.app (fn (w,(context,cells)) => print ("SOURCE_POLICY_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jdevelopmentAssessed cells ^ "\n")) table;
val () = (case execution of NONE =>
    print "SOURCE_POLICY_QUESTION null\nSOURCE_POLICY_REPORT null\nSOURCE_POLICY_ADMISSION null\nSOURCE_POLICY_METHODS null\n"
  | SOME (question,(report,(admission,methods))) =>
    (print ("SOURCE_POLICY_QUESTION " ^ jdevelopmentQuestion question ^ "\n");
     print ("SOURCE_POLICY_REPORT " ^ jdevelopmentReport report ^ "\n");
     print ("SOURCE_POLICY_ADMISSION " ^ jdevelopmentDecision admission ^ "\n");
     print ("SOURCE_POLICY_METHODS " ^ joption (jlist jnat) methods ^ "\n")));
val () = print ("SOURCE_POLICY_DISPATCH {\"requests\":" ^ jlist jdevelopmentQuestion policyRequests ^
  ",\"results\":" ^ joption (jlist jsteeredSourceResult) policyResults ^ "}\n");
fun eachIndexed f xs = let
  fun walk i [] = () | walk i (x::rest) = (f (i,x); walk (i+1) rest)
  in walk 0 xs end;
val () = eachIndexed (fn (i,R) => print ("SOURCE_REQUEST " ^ Int.toString i ^ " " ^ jsourceRequest R ^ "\n")) originalRequests;
val () = print ("SOURCE_CHOICE " ^ joption jnat chosen ^ "\n");
val () = print ("SOURCE_AVAILABLE " ^ Bool.toString (Option.isSome results) ^ "\n");
val () = (case results of NONE => () | SOME rows => eachIndexed
  (fn (i,result) => print ("SOURCE_RESULT " ^ Int.toString i ^ " " ^ jsourcePacket result ^ "\n")) rows);
val () = (case results of SOME ((R,(report,admission))::_) =>
    eachIndexed (fn (i,result) => print ("SOURCE_CONTROL " ^ Int.toString i ^ " " ^ jsourceControl result ^ "\n"))
      (N.source_development_report_controls R report)
  | _ => ());
'''
    return code


def read_inputs(path, encode):
    value = json.loads(path.read_text(), object_pairs_hook=workflow_input.unique_object)
    if not isinstance(value, list):
        raise ValueError('Expected a complete input list.')
    for item in value:
        encode(item)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--questions', type=Path)
    group.add_argument('--empty', action='store_true')
    group.add_argument('--first', action='store_true')
    parser.add_argument('--requests', type=Path)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    questions = [] if args.empty else None
    if args.questions:
        questions = read_inputs(args.questions, native_development_input.question)
    requests = read_inputs(args.requests, source_development_input.request) if args.requests else None
    proof = json.loads(args.proof.read_text())
    contracts = [c for c in proof['subject_contracts'] if Path(c['path']).stem == 'development_subject_investigation']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Development_Subjects', 'development_subject_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, log):
        with closing(machine_reports.reports(log)) as records:
            r = next(records)
            assert r['tag'] == 'SOURCE_SCOPE' and r['indices'] == []
            scope = r['value']
            assert scope['methods'] == inputs['candidates'] and scope['facets'] == inputs['facets']
            if inputs['questions'] is not None:
                assert scope['question_count'] == len(inputs['questions'])
            for w in range(scope['question_count']):
                r = next(records)
                assert r['tag'] == 'SOURCE_POLICY_CONTEXT' and r['indices'] == [w]
                if inputs['questions'] is not None:
                    assert r['value']['question'] == inputs['questions'][w]
                for m in inputs['candidates']:
                    r = next(records)
                    assert r['tag'] == 'SOURCE_POLICY_CANDIDATE' and r['indices'] == [w, m]
            for w in range(scope['question_count']):
                r = next(records)
                assert r['tag'] == 'SOURCE_POLICY_ASSESSMENT' and r['indices'] == [w]
                assert [row['method'] for row in r['value']] == inputs['candidates']
            for tag in ['SOURCE_POLICY_QUESTION', 'SOURCE_POLICY_REPORT', 'SOURCE_POLICY_ADMISSION',
                        'SOURCE_POLICY_METHODS', 'SOURCE_POLICY_DISPATCH']:
                r = next(records)
                assert r['tag'] == tag and r['indices'] == []
            count = scope['request_count']
            if inputs['requests'] is not None:
                assert count == len(inputs['requests'])
            originals = []
            for i in range(count):
                r = next(records)
                assert r['tag'] == 'SOURCE_REQUEST' and r['indices'] == [i]
                source_development_input.request(r['value'])
                originals.append(r['value'])
                if inputs['requests'] is not None:
                    assert r['value'] == inputs['requests'][i]
            r = next(records)
            assert r['tag'] == 'SOURCE_CHOICE' and r['indices'] == []
            r = next(records)
            assert r['tag'] == 'SOURCE_AVAILABLE' and r['indices'] == [] and type(r['value']) is bool
            if r['value']:
                for i in range(count):
                    r = next(records)
                    assert r['tag'] == 'SOURCE_RESULT' and r['indices'] == [i]
                    assert set(r['value']) == {'request', 'report', 'admission'}
                    assert r['value']['request'] == originals[i]
                    assert set(r['value']['report']) == {'proposals', 'observations', 'question', 'execution',
                        'selected', 'installed', 'stage', 'query'}
                if count:
                    for i in range(4):
                        r = next(records)
                        assert r['tag'] == 'SOURCE_CONTROL' and r['indices'] == [i]
                        assert set(r['value']) == {'control', 'report', 'admission'}
                        assert r['value']['control'] == i
            assert next(records, None) is None
        return {'scope': scope, 'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'Every complete input, computed native policy, proposal, observation, report, '
                    'installation, query and admission is transported unchanged. The host supplies no truth, '
                    'selection or installation flags.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Source_Development'],
        inputs={'questions': questions, 'requests': requests, 'first': args.first, 'cases': [],
                'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'], 'selections': []},
        input_paths=[Path(__file__), Path(source_development_input.__file__), Path(source_development_json.__file__),
                     Path(native_development_input.__file__), Path(workflow_input.__file__),
                     *(Path(c['path']) for c in contracts), *([args.questions.resolve()] if args.questions else []),
                     *([args.requests.resolve()] if args.requests else [])],
        workers=args.workers, program=program, assess=assess, project=args.project.resolve(), timeout=1200,
        question='Does the computed native development choice select and install a permitted actual source '
            'extension, preserve the complete old source and use the installed entry for the original next query?',
        boundary='The complete original source and target family determine every native criterion. '
            'The closed cycle performs the selection and the original source-change admission gates '
            'installation and complete query evidence. Universal target meaning and old-source preservation '
            'remain distinct from the declared finite target family and historical continuation authority.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
