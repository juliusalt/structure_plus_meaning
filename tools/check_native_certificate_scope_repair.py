"""Compare complete native input scopes and retain every correction witness."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import execution_support as investigate
import machine_reports
import native_certificate_coverage_json
import native_certificate_input_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Certificate_Scope_Repair_Execution')
    code += shared.investigation_json.CYCLE + native_certificate_coverage_json.PRELUDE + native_certificate_input_json.PRELUDE
    code += r'''
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jscopeAssessment (retained,(originals,coverage)) = "{\"original_inputs_retained\":" ^ Bool.toString retained ^
  ",\"originals\":" ^ jlist jderivation originals ^ ",\"coverage\":" ^ jlist jfamilyCoverage coverage ^ "}";
fun jscopeCandidate (m,(xs,a)) = "{\"method\":" ^ jnat m ^ ",\"inputs\":" ^ jlist jinputReport xs ^ "}";
fun jscopeAssessed (m,(xs,a)) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jscopeAssessment a ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.certificate_scope_repair_inspect a f)) facets) ^ "}";
val (table,(comparison,cycles)) = N.certificate_scope_repair_packet selections;
val () = print "SCOPE_REPAIR_SCOPE [0]\n";
val () = List.app (fn (w,(xs,cells)) => print ("SCOPE_REPAIR_SUBJECT " ^ jnat w ^
  " {\"original_inputs\":" ^ jlist jinputReport xs ^ ",\"candidates\":" ^ jlist jscopeCandidate cells ^ "}\n")) table;
val () = List.app (fn (w,(xs,cells)) => print ("SCOPE_REPAIR_ASSESSMENT " ^ jnat w ^ " " ^
  jlist jscopeAssessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("SCOPE_REPAIR_COMPARISON {\"scope\":[0],\"observations\":" ^ jlist jtriple rows ^
  ",\"relation\":" ^ jlist jpair relation ^ ",\"selected_methods\":" ^ jlist jnat selected ^
  ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("SCOPE_REPAIR_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Native_Certificate_Scope_Repair', 'certificate_scope_repair_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path, deferred=True))
        assert len(reports) == 4 + len(inputs['selections'])
        assert [(r['tag'], r['indices']) for r in reports[:4]] == [
            ('SCOPE_REPAIR_SCOPE', []), ('SCOPE_REPAIR_SUBJECT', [0]),
            ('SCOPE_REPAIR_ASSESSMENT', [0]), ('SCOPE_REPAIR_COMPARISON', [])]
        assert reports[0]['value'] == [0] and reports[3]['value']['scope'] == [0]
        assert [r['method'] for r in reports[1]['value']['candidates']] == inputs['candidates']
        assert [r['method'] for r in reports[2]['value']] == inputs['candidates']
        assert all(r['tag'] == 'SCOPE_REPAIR_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selected
                   for r, selected in zip(reports[4:], inputs['selections']))
        return {'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original native inputs, actual candidate input scopes, full native '
                            'source and certificate checks, original families and every identity/sharing '
                            'witness, all observations and revision reasons are retained. Verdicts are '
                            'computed by the proved operation; the host checks reproduction only.'}

    modules = [shared.check_reasoning, shared.investigation_json, shared.native_program_json,
               shared.native_history_json, shared.native_graph_json, shared.native_certificate_json,
               shared.program_evaluation_json, shared, native_certificate_coverage_json, native_certificate_input_json]
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Certificate_Scope_Repair_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': [0], 'selections': [[], [0], [0, 1, 2, 3]]},
        input_paths=[Path(__file__), *(Path(m.__file__) for m in modules), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual input-scope correction preserves every full original input and supplies '
                 'independently checked proof identity, call identity and shared-path witnesses?',
        boundary='This executes the proposed correction to the actual failed scope criticism. Complete '
                 'input retention and native source/proof checks remain explicit. Scope selection does '
                 'not establish full workflow admission, candidate-language completeness, cost or genesis.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
