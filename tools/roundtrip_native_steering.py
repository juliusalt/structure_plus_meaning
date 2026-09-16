"""Reconstruct every original steering subject and compare the complete native cycle."""
from pathlib import Path
from contextlib import closing
import argparse
import json

import check_native_steering
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import native_development_input
import native_development_json
import workflow_input
import workflow_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'comparison']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    questions, requests, scope = [], [], None
    with closing(machine_reports.reports(args.comparison)) as original:
        for r in original:
            if r['tag'] == 'STEERING_SCOPE':
                assert scope is None
                scope = r['value']
            elif r['tag'] == 'STEERING_CONTEXT':
                assert r['indices'] == [len(questions)]
                questions.append(r['value']['question'])
            elif r['tag'] == 'STEERED_REQUEST':
                assert r['indices'] == [len(requests)]
                requests.append(r['value'])
    assert scope is not None and len(questions) == scope['question_count'] and len(requests) == scope['request_count']
    for question in questions + requests:
        native_development_input.question(question)

    def assess(inputs, log):
        count = 0
        with closing(machine_reports.reports(log)) as actual, closing(machine_reports.reports(args.comparison)) as original:
            for old in original:
                assert next(actual, None) == old
                count += 1
            assert next(actual, None) is None
        return {'reports_directly_equal': count, 'complete_original_question_roundtrip': True,
                'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'Every original subject, actual producer result, derived native source, '
                    'criterion certificate, criticism, comparison, revision and admission agrees directly.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Development_Steering'],
        inputs={'questions': questions, 'requests': requests, 'first': False, 'cases': [], 'candidates': scope['methods'],
                'facets': scope['facets'], 'selections': []},
        input_paths=[Path(__file__), args.comparison.resolve(), Path(check_native_steering.__file__),
                     Path(native_development_input.__file__), Path(native_development_json.__file__),
                     Path(workflow_input.__file__), Path(workflow_json.__file__)],
        workers=args.workers, program=check_native_steering.program, assess=assess,
        project=args.project.resolve(), timeout=900,
        question='Do the complete original subjects reconstruct every operation and result of the native self-development decision?',
        boundary='Complete record identity checks transport and reproducibility. Semantic authority remains '
                 'with the native operations and their proved actual-subject contracts.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
