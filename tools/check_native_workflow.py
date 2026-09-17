"""Execute and retain the complete native whole-workflow construction comparison."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import compressed_machine_reports as machine_reports
from compressed_reconstruction import compressed_boundary
import isabelle_native_execution
import execution_support as investigate
import observation_contracts
import workflow_json


def program(engine, inputs):
    family = inputs['family']
    if family == 'input-scope':
        return scope_program(engine, inputs)
    required = family in ['requirements', 'expanded']
    indices = ('expanded_workflow_indices' if family == 'expanded' else
               'required_workflow_indices' if required else 'workflow_indices')
    packet = ('expanded_workflow_packet' if family == 'expanded' else
              'required_workflow_packet' if required else 'workflow_packet')
    subject = 'jrequiredSubject' if required else 'jworkflowSubject'
    code = shared.source_preamble(engine, inputs, 'Native_Workflow', indices)
    if family == 'expanded':
        code = code.replace('N.expanded_workflow_indices',
            '(case N.expanded_workflow_indices of NONE => raise Fail \"No unique adequate input scope\" | SOME xs => xs)')
    code += workflow_json.PRELUDE + shared.investigation_json.CYCLE
    code += ('fun jresult NONE = "null" | jresult (SOME execution) = jexecution execution;\n'
             if required else 'val jresult = jexecution;\n')
    code += r'''
val () = print ("WORKFLOW_SCOPE " ^ jlist jnat N.INDICES ^ "\n");
val (table,(comparison,cycles)) = N.PACKET scope selections;
val () = List.app (fn (w,((subject,original),cells)) =>
  (print ("WORKFLOW_CONTEXT " ^ jnat w ^ " {\"subject\":" ^ SUBJECT subject ^
    ",\"original\":" ^ jresult original ^ "}\n");
   List.app (fn (m,(actual,assessment)) => print ("WORKFLOW_CANDIDATE " ^ jnat w ^ " " ^ jnat m ^
    " " ^ jresult actual ^ "\n")) cells)) table;
val () = List.app (fn (w,(context,cells)) => print ("WORKFLOW_ASSESSMENT " ^ jnat w ^
  " " ^ jlist jworkflowAssessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("WORKFLOW_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("WORKFLOW_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''.replace('INDICES', indices).replace('PACKET', packet).replace('SUBJECT', subject)
    if family == 'expanded':
        code = code.replace('jlist jnat N.expanded_workflow_indices',
            'jlist jnat (case N.expanded_workflow_indices of NONE => raise Fail "No unique adequate input scope" | SOME xs => xs)')
        code = code.replace('N.expanded_workflow_packet scope selections;',
            '(case N.expanded_workflow_packet scope selections of NONE => raise Fail "No unique adequate input scope" | SOME p => p);')
    return code


def scope_program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Workflow', 'workflow_input_scope_indices')
    code += workflow_json.PRELUDE + shared.investigation_json.CYCLE
    code += r'''
val () = print ("WORKFLOW_SCOPE " ^ jlist jnat N.workflow_input_scope_indices ^ "\n");
val (table,(comparison,cycles)) = N.workflow_input_scope_packet selections;
val () = List.app (fn (w,(original,cells)) =>
  (print ("WORKFLOW_CONTEXT " ^ jnat w ^ " {\"subject\":" ^ jlist jrequiredSubject original ^
    ",\"original\":" ^ jlist jrequiredSubject original ^ "}\n");
   List.app (fn (m,(actual,qualities)) => print ("WORKFLOW_CANDIDATE " ^ jnat w ^ " " ^ jnat m ^
    " " ^ jlist jrequiredSubject actual ^ "\n")) cells)) table;
val () = List.app (fn (w,(context,cells)) => print ("WORKFLOW_ASSESSMENT " ^ jnat w ^
  " " ^ jlist (fn (m,(actual,qualities)) => "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^
    jlist jquality qualities ^ "}") cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("WORKFLOW_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("WORKFLOW_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
val () = print ("WORKFLOW_SELECTED_SCOPE " ^ (case N.selected_workflow_input_scope of NONE => "null"
  | SOME xs => jlist jrequiredSubject xs) ^ "\n");
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    parser.add_argument('--workers', type=int, default=16)
    parser.add_argument('--family', choices=['workflow', 'requirements', 'input-scope', 'expanded'], default='workflow')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    identifier, theory = {
        'workflow': ('workflow_investigation', 'Factor_Workflow_Comparison'),
        'requirements': ('required_workflow_investigation', 'Factor_Required_Workflow_Comparison'),
        'input-scope': ('workflow_input_scope_investigation', 'Factor_Workflow_Input_Scope'),
        'expanded': ('required_workflow_scope_investigation', 'Factor_Workflow_Expanded_Comparison'),
    }[args.family]
    if args.family == 'input-scope':
        assert args.cases is None, 'The input scope criticism has one complete original problem.'
    contracts = [c for c in proof['subject_contracts'] if Path(c['path']).stem == identifier]
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        theory, identifier,
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, log):
        records = list(machine_reports.reports(log))
        assert records and records[0]['tag'] == 'WORKFLOW_SCOPE' and records[0]['indices'] == []
        scope = records[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        position = 1
        for w in requested:
            assert records[position]['tag'] == 'WORKFLOW_CONTEXT' and records[position]['indices'] == [w]
            position += 1
            for m in inputs['candidates']:
                assert records[position]['tag'] == 'WORKFLOW_CANDIDATE' and records[position]['indices'] == [w, m]
                position += 1
        for w in requested:
            assert records[position]['tag'] == 'WORKFLOW_ASSESSMENT' and records[position]['indices'] == [w]
            assert [row['method'] for row in records[position]['value']] == inputs['candidates']
            assert all([f for f, _ in row['qualities']] == inputs['facets'] for row in records[position]['value'])
            position += 1
        compared = records[position]
        assert compared['tag'] == 'WORKFLOW_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        position += 1
        for selected in inputs['selections']:
            assert records[position]['tag'] == 'WORKFLOW_INVESTIGATION' and records[position]['indices'] == []
            assert records[position]['value']['selected'] == selected
            position += 1
        if inputs['family'] == 'input-scope':
            assert records[position]['tag'] == 'WORKFLOW_SELECTED_SCOPE' and records[position]['indices'] == []
            position += 1
        assert position == len(records)
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': compressed_boundary(log.with_name('results.log')),
                'boundary': 'Every original source, complete execution tree, candidate, certificate, '
                    'assessment and comparison or revision reason remains in the native output. '
                    'The host checks complete record transport and ordering; it supplies no semantic verdict.'}

    receipt = isabelle_native_execution.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Workflow_Execution'],
        inputs={'family': args.family, 'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1], contract['facet_indices']]},
        input_paths=[Path(__file__), Path(workflow_json.__file__), *(Path(c['path']) for c in contracts)],
        workers=args.workers, program=program, assess=assess, project=args.project.resolve(), timeout=300,
        question=('Which scope construction preserves all original requests and covers every term, '
                  'nested goal and candidate-scope constructor plus malformed targets?'
                  if args.family == 'input-scope' else
                  'Which whole workflow constructors preserve every required stage, original source and '
                  'complete shared input, all ordered branches and every native certificate?'),
        boundary='Actual source experiments evaluate the complete workflow constructor and admission '
                 'mechanism under its registered subject contract. Position names and these transfer '
                 'experiments do not instantiate the missing meanings of the repository development '
                 'stages. Full workflow adequacy and condition-6 use remain explicit obligations.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
