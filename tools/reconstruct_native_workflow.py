"""Reconstruct generated workflows and admission against original native requirements."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-workflow',
    roots=('Native_Workflow_Execution',),
    export='Native_Workflow_Execution:native_workflow.ML',
    session='Reconstruct_Native_Workflow',
    groups=((
        Execution('presentation-workflow', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Workflow_Execution', '--module', 'Native_Workflow', '--report', 'workflow_report_value', '--scope', 'workflow_indices', '--selections', 'workflow_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-requirements', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Workflow_Execution', '--module', 'Native_Workflow', '--report', 'required_workflow_report_value', '--scope', 'required_workflow_indices', '--selections', 'workflow_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-input-scope', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Workflow_Execution', '--module', 'Native_Workflow', '--report', 'workflow_input_scope_report_value', '--scope', 'workflow_input_scope_indices', '--selections', 'workflow_input_scope_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-expanded', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Workflow_Execution', '--module', 'Native_Workflow', '--report', 'expanded_workflow_report_value', '--scope', 'expanded_workflow_report_scope', '--selections', 'workflow_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The source boundary reconstructs all complete native comparisons, including original requirements, generated rule applications, complete executions, all certificates, admission results, comparisons and revisions. Every observation has a proved subject equation. Compilation binds every workflow position to its original native goals. Adequacy of those goals for real development roles, candidate scope, operative integration, condition-6 coverage, the complete cost account and genesis remain separate requirements.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
