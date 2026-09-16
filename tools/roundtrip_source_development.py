"""Reencode the entire original policy and source requests and compare every record."""
from pathlib import Path
from contextlib import closing
import argparse
import json

import check_source_development
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import native_development_input
import source_development_input
import source_development_json
import workflow_input


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'comparison']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    questions, requests, scope = [], [], None
    with closing(machine_reports.reports(args.comparison, deferred=True)) as records:
        for row in records:
            if row['tag'] == 'SOURCE_SCOPE':
                assert scope is None
                scope = row['value']
            elif row['tag'] == 'SOURCE_POLICY_CONTEXT':
                assert row['indices'] == [len(questions)]
                questions.append(machine_reports.field(row, 'question'))
            elif row['tag'] == 'SOURCE_REQUEST':
                assert row['indices'] == [len(requests)]
                requests.append(row['value'])
    assert scope is not None and len(questions) == scope['question_count'] and len(requests) == scope['request_count']
    for q in questions:
        native_development_input.question(q)
    for r in requests:
        source_development_input.request(r)

    def assess(inputs, log):
        count = 0
        with closing(machine_reports.reports(log, deferred=True)) as actual, closing(machine_reports.reports(args.comparison, deferred=True)) as reference:
            for old in reference:
                assert machine_reports.record_equal(next(actual, None), old)
                count += 1
            assert next(actual, None) is None
        return {'reports_directly_equal': count, 'complete_original_input_roundtrip': True,
                'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'Both complete original input lists reconstruct every policy result, candidate, '
                    'native question, source-change report, installation, query, admission and control directly.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Source_Development'],
        inputs={'questions': questions, 'requests': requests, 'first': False, 'cases': [],
                'candidates': scope['methods'], 'facets': scope['facets'], 'selections': []},
        input_paths=[Path(__file__), args.comparison.resolve(), Path(check_source_development.__file__),
                     Path(native_development_input.__file__), Path(source_development_input.__file__),
                     Path(source_development_json.__file__), Path(workflow_input.__file__)],
        workers=args.workers, program=check_source_development.program, assess=assess,
        project=args.project.resolve(), timeout=1200,
        question='Do the complete original inputs reconstruct the selected native source change and every following query?',
        boundary='This compares complete transport and reconstructed execution. Semantic authority remains '
            'with the proved original-subject equations and source-change admission contract.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
