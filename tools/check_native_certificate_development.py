"""Execute computed certificate criticism and the native cycle admission gate."""
from pathlib import Path
import argparse
import json

import check_native_certificates
import execution_support as investigate
import machine_reports
import native_certificate_coverage_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = check_native_certificates.preamble(engine, inputs, 'Native_Certificate_Development_Execution')
    code += native_certificate_coverage_json.PRELUDE
    code += r'''
val () = print ("CERTIFICATE_SCOPE " ^ jlist jnat N.native_certificate_indices ^ "\n");
val (table,(criticism,(comparison,(cycle,admissions)))) =
  N.native_certificate_development_packet scope (hd selections);
val () = List.app emitSubject table;
val () = List.app emitAssessment table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("CERTIFICATE_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = print ("CERTIFICATE_INVESTIGATION " ^ jcycle cycle ^ "\n");
val () = print ("CERTIFICATE_CRITICISM {\"rows\":" ^ jlist jcriticismRow criticism ^
  ",\"accepted\":" ^ Bool.toString (N.native_certificate_criticism_accept criticism) ^ "}\n");
val () = print ("CERTIFICATE_ADMISSIONS " ^ jlist jnat admissions ^ "\n");
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
        'Factor_Native_Certificate_Investigation', 'native_certificate_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'CERTIFICATE_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 5
        assert all(r['tag'] == 'CERTIFICATE_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'CERTIFICATE_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        rest = reports[1 + 2 * size:]
        assert [(r['tag'], r['indices']) for r in rest] == [
            ('CERTIFICATE_COMPARISON', []), ('CERTIFICATE_INVESTIGATION', []),
            ('CERTIFICATE_CRITICISM', []), ('CERTIFICATE_ADMISSIONS', [])]
        assert rest[0]['value']['scope'] == requested
        assert rest[1]['value']['selected'] == inputs['selections'][0]
        assert [w for w, _ in rest[2]['value']['rows']] == requested
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original subjects, actual candidate outputs and assessments, comparison '
                            'and revision, full original-subject criticism witnesses and computed admission '
                            'results are retained. Host checks establish reproduction, not permission.'}

    shared = check_native_certificates
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Certificate_Development_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [list(range(7))]},
        input_paths=[Path(__file__), Path(shared.__file__), Path(native_certificate_coverage_json.__file__),
                     *(Path(module.__file__) for module in [shared.check_reasoning, shared.investigation_json,
                       shared.native_program_json, shared.native_history_json, shared.native_graph_json,
                       shared.native_certificate_json, shared.program_evaluation_json]),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Does the actual certificate development cycle admit any method after its original-subject '
                 'comparison, complete revision and independently computed scope criticism?',
        boundary='The shared cycle constructs every actual context and cell, derives comparisons and revisions, '
                 'and computes criticism from the original source-derived certificate families. Its checked '
                 'admission equation requires all scoped conditions and accepted criticism. The broader '
                 'workflow, historical permission, native mathematical proof admission, cost and genesis remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
