"""Construct, criticize and admit one complete original native development question."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import native_development_input
import native_development_json
import workflow_input
import workflow_json


def batch_program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Development', 'native_development_indices')
    code += shared.investigation_json.CYCLE + native_development_json.PRELUDE
    code += 'val questions = [' + ','.join(native_development_input.question(q) for q in inputs['questions']) + '];\n'
    code += r'''
val packets = N.native_development_batch questions;
val () = List.app (fn (i,(question,(report,decision))) =>
  (print ("DEVELOPMENT_QUESTION " ^ jnat i ^ " " ^ jdevelopmentQuestion question ^ "\n");
   print ("DEVELOPMENT_REPORT " ^ jnat i ^ " " ^ jdevelopmentReport report ^ "\n");
   print ("DEVELOPMENT_ADMISSION " ^ jnat i ^ " " ^ jdevelopmentDecision decision ^ "\n"))) packets;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'question']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    question = native_development_input.read_question(args.question)

    def assess(inputs, log):
        records = list(machine_reports.reports(log))
        assert [r['tag'] for r in records] == ['DEVELOPMENT_QUESTION', 'DEVELOPMENT_REPORT', 'DEVELOPMENT_ADMISSION']
        assert all(r['indices'] == [0] for r in records)
        assert records[0]['value'] == inputs['questions'][0]
        return {'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'The native packet constructs and admits the complete original question. '
                            'The host preserves and renders its values; it supplies no observations or acceptance flags.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Development_Execution'],
        inputs={'questions': [question], 'cases': [], 'facets': [], 'selections': []},
        input_paths=[Path(__file__), args.question.resolve(), Path(native_development_input.__file__),
                     Path(native_development_json.__file__), Path(workflow_input.__file__), Path(workflow_json.__file__)],
        workers=args.workers, program=batch_program, assess=assess, project=args.project.resolve(), timeout=600,
        question='Construct the complete development cycle for the original native question and admit its original results.',
        boundary='Native source generation, requirement construction, complete observations, independent evidence '
                 'inspection and native scope criticism, comparison and revision precede native admission. '
                 'A refusal is retained with all available operations. The question is the reconstructible local input.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
