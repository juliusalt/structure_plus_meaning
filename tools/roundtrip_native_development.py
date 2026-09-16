"""Reconstruct native development questions and compare every returned field."""
from pathlib import Path
import argparse
import json

import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import native_development_input
import native_development_json
import run_native_development
import workflow_input
import workflow_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'comparison']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    original = list(machine_reports.reports(args.comparison, deferred=True))
    contexts = [r for r in original if r['tag'] == 'DEVELOPMENT_CONTEXT']
    questions = [machine_reports.field(r, 'question') for r in contexts]
    controls = {r['indices'][0]: r for r in original if r['tag'] == 'DEVELOPMENT_CANDIDATE' and r['indices'][1] == 0}
    assert contexts and len(controls) == len(contexts)
    for question in questions:
        native_development_input.question(question)

    def assess(inputs, log):
        records = list(machine_reports.reports(log, deferred=True))
        assert len(records) == 3 * len(questions)
        for i, context in enumerate(contexts):
            group = records[3*i:3*i+3]
            assert [r['tag'] for r in group] == ['DEVELOPMENT_QUESTION', 'DEVELOPMENT_REPORT', 'DEVELOPMENT_ADMISSION']
            assert all(r['indices'] == [i] for r in group)
            assert machine_reports.field_equal(group[0], (), context, ('question',))
            assert machine_reports.field_equal(group[1], (), context, ('original',))
            assert machine_reports.field_equal(group[2], (), controls[context['indices'][0]], ('decision',))
        return {'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'complete_question_report_admission_roundtrip': True,
                'boundary': 'The full original native question, every operation and certificate, every comparison '
                            'and revision field and the original admission result agree directly after input reconstruction.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Development_Execution'],
        inputs={'questions': questions, 'cases': [], 'facets': [], 'selections': []},
        input_paths=[Path(__file__), args.comparison.resolve(), Path(run_native_development.__file__),
                     Path(native_development_input.__file__), Path(native_development_json.__file__),
                     Path(workflow_input.__file__), Path(workflow_json.__file__)],
        workers=args.workers, program=run_native_development.batch_program, assess=assess,
        project=args.project.resolve(), timeout=600,
        question='Does the complete original native development input reconstruct every native operation and admission?',
        boundary='Complete native results are compared directly through the proved parallel batch. '
                 'This validates the input transport without assigning truth to any original native condition.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
