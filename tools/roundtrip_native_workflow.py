"""Re-encode complete native request reports and compare their complete executions."""
from pathlib import Path
import argparse
import json

import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import run_native_workflow
import workflow_input
import workflow_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'comparison']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    source_records = list(machine_reports.reports(args.comparison))
    contexts = [r for r in source_records if r['tag'] == 'WORKFLOW_CONTEXT']
    assessments = {tuple(r['indices']): r['value'] for r in source_records if r['tag'] == 'WORKFLOW_ASSESSMENT'}
    assert contexts and all(len(r['indices']) == 1 for r in contexts)
    requests = [r['value']['subject'] for r in contexts]
    for request in requests:
        workflow_input.request(request)
    expected = []
    for context in contexts:
        rows = assessments[tuple(context['indices'])]
        originals = [r['assessment'] for r in rows if r['method'] == 0]
        assert len(originals) == 1
        execution = context['value']['original']
        expected.append({'execution': execution,
                         'admission': None if execution is None else originals[0]['paths']})

    def assess(inputs, log):
        records = list(machine_reports.reports(log))
        tags = ['WORKFLOW_REQUEST', 'WORKFLOW_COMPILED', 'WORKFLOW_EXECUTION', 'WORKFLOW_ADMISSION']
        assert len(records) == len(requests) * len(tags)
        for i, (request, original) in enumerate(zip(requests, expected)):
            group = records[4*i:4*i+4]
            assert [r['tag'] for r in group] == tags
            assert all(r['indices'] == [i] for r in group)
            assert group[0]['value'] == request, ('request fields', i)
            assert group[2]['value'] == original['execution'], ('complete execution', i)
            assert group[3]['value'] == original['admission'], ('native admission', i)
        return {'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'complete_request_and_execution_roundtrip': True,
                'boundary': 'All request fields and entire native executions and admissions are compared '
                            'with the original native comparison outputs. The host supplies no satisfaction values.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Workflow_Execution'],
        inputs={'requests': requests, 'cases': [], 'facets': [], 'selections': []},
        input_paths=[Path(__file__), Path(run_native_workflow.__file__), Path(workflow_input.__file__),
                     Path(workflow_json.__file__), args.comparison.resolve()],
        workers=args.workers, program=run_native_workflow.batch_program, assess=assess,
        project=args.project.resolve(), timeout=300,
        question='Does encoding each complete native requirement request preserve its entire native workflow execution?',
        boundary='The original comparison supplies complete structural requests and reference outputs. '
                 'The codec invokes proved native constructors, and the native batch executes and admits '
                 'each reconstructed request. Full report comparison checks transport identity and does '
                 'not assign any development meaning or satisfaction flag.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
