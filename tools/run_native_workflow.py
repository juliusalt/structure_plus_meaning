"""Construct and admit a workflow for a complete native request value."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import workflow_input
import workflow_json


EMIT = r'''
fun jrequestOption f NONE = "null" | jrequestOption f (SOME x) = f x;
fun emitRequest prefix (specs,(original,(compiled,(execution,admitted)))) =
  (print ("WORKFLOW_REQUEST " ^ prefix ^ "{\"requirements\":" ^ jlist jrequirement specs ^
     ",\"problem\":" ^ jterm original ^ "}\n");
   print ("WORKFLOW_COMPILED " ^ prefix ^ jrequestOption
     (fn w => jlist jstage (N.development_workflow_stages w)) compiled ^ "\n");
   print ("WORKFLOW_EXECUTION " ^ prefix ^ jrequestOption jexecution execution ^ "\n");
   print ("WORKFLOW_ADMISSION " ^ prefix ^ jrequestOption (jlist (jlist jterm)) admitted ^ "\n"));
'''


def preamble(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Workflow', 'workflow_indices')
    return code + workflow_json.PRELUDE + EMIT


def program(engine, inputs):
    specs, problem = workflow_input.request(inputs['request'])
    return preamble(engine, inputs) + 'val () = emitRequest "" (N.workflow_request_packet ' + specs + ' ' + problem + ');\n'


def batch_program(engine, inputs):
    requests = []
    for value in inputs['requests']:
        specs, problem = workflow_input.request(value)
        requests.append('(' + specs + ',' + problem + ')')
    return preamble(engine, inputs) + 'val requests = [' + ','.join(requests) + r'''];
val packets = N.workflow_request_batch requests;
val () = List.app (fn (i,packet) => emitRequest (jnat i ^ " ") packet) packets;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output', 'request']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    original = workflow_input.read_request(args.request)

    def assess(inputs, log):
        records = list(machine_reports.reports(log))
        assert [record['tag'] for record in records] == [
            'WORKFLOW_REQUEST', 'WORKFLOW_COMPILED', 'WORKFLOW_EXECUTION', 'WORKFLOW_ADMISSION']
        assert all(record['indices'] == [] for record in records)
        return {'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'The complete request, compiled protocol, execution and admission are native '
                            'outputs. This host check verifies their complete transport and ordering.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Workflow_Execution'],
        inputs={'request': original, 'cases': [], 'facets': [], 'selections': []},
        input_paths=[Path(__file__), Path(workflow_input.__file__), Path(workflow_json.__file__), args.request.resolve()],
        workers=args.workers, program=program, assess=assess, project=args.project.resolve(), timeout=300,
        question='Construct and admit a workflow for these complete original native requirements and problem.',
        boundary='The input encodes structural source values, original native goals and candidate scopes. '
                 'The native reader enforces all required positions; compilation and admission use the same '
                 'original values. A failed compilation, unavailable computation, rejected trace or empty '
                 'completion remains distinct in the complete output. Host execution success does not mean '
                 'that the native workflow completed or that the original goal family covers every development role.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
