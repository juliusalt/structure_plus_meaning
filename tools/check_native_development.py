"""Execute a complete native development cycle and its actual producer comparison."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import execution_support as investigate
import observation_contracts
import native_development_json
import workflow_json


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Development', 'native_development_indices')
    code += shared.investigation_json.CYCLE + native_development_json.PRELUDE
    code += r'''
val () = print ("DEVELOPMENT_SCOPE " ^ jlist jnat N.native_development_indices ^ "\n");
val (table,(comparison,cycles)) = N.development_producer_packet scope selections;
val () = List.app (fn (w,((question,(original,reference)),cells)) =>
  (print ("DEVELOPMENT_CONTEXT " ^ jnat w ^ " {\"question\":" ^ jdevelopmentQuestion question ^
    ",\"original\":" ^ jdevelopmentReport original ^ ",\"reference\":" ^ jdevelopmentDecision reference ^ "}\n");
   List.app (fn (m,(actual,assessment)) => print ("DEVELOPMENT_CANDIDATE " ^ jnat w ^ " " ^ jnat m ^
    " " ^ jdevelopmentResult actual ^ "\n")) cells)) table;
val () = List.app (fn (w,(context,cells)) => print ("DEVELOPMENT_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jdevelopmentAssessed cells ^ "\n")) table;
val () = print ("DEVELOPMENT_COMPARISON " ^ jdevelopmentComparison comparison ^ "\n");
val () = List.app (fn c => print ("DEVELOPMENT_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = [c for c in proof['subject_contracts'] if Path(c['path']).stem == 'development_producer_investigation']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Development_Comparison', 'development_producer_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, log):
        records = list(machine_reports.reports(log, deferred=True))
        assert records[0]['tag'] == 'DEVELOPMENT_SCOPE' and records[0]['indices'] == []
        scope = records[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        position = 1
        for w in requested:
            assert records[position]['tag'] == 'DEVELOPMENT_CONTEXT' and records[position]['indices'] == [w]
            position += 1
            for m in inputs['candidates']:
                assert records[position]['tag'] == 'DEVELOPMENT_CANDIDATE' and records[position]['indices'] == [w, m]
                position += 1
        for w in requested:
            assert records[position]['tag'] == 'DEVELOPMENT_ASSESSMENT' and records[position]['indices'] == [w]
            assert [r['method'] for r in records[position]['value']] == inputs['candidates']
            assert all([f for f, _ in r['qualities']] == inputs['facets'] for r in records[position]['value'])
            position += 1
        assert records[position]['tag'] == 'DEVELOPMENT_COMPARISON' and records[position]['indices'] == []
        position += 1
        for selected in inputs['selections']:
            assert records[position]['tag'] == 'DEVELOPMENT_INVESTIGATION' and records[position]['indices'] == []
            assert records[position]['value']['selected'] == selected
            position += 1
        assert position == len(records)
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'Complete native questions, source applications, all constructed guards, '
                    'observations and certificates, native criticism, comparisons, revisions and '
                    'admissions are retained. The host checks transport and supplies no semantic flags.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Development_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1], contract['facet_indices']]},
        input_paths=[Path(__file__), Path(native_development_json.__file__), Path(workflow_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        workers=args.workers, program=program, assess=assess, project=args.project.resolve(), timeout=600,
        question='Which complete native development producers preserve generation, original criteria, '
                 'all evidence, independent native criticism, comparison, revision and complete admission?',
        boundary='Actual producers operate on complete finite native questions. The registered observer '
                 'compares their results with original uncompiled native goal observations and inspects '
                 'every required operation. The finite generation boundary and coverage of wider '
                 'development questions remain explicit.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
