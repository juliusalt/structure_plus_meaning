"""Reconstruct generated workflows and admission against original native requirements."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-workflow',
    roots=('Native_Workflow_Execution',),
    export='Native_Workflow_Execution:native_workflow.ML',
    session='Reconstruct_Native_Workflow',
    groups=((
        Execution('workflow', 'check_native_workflow.py',
            ('--project', '{project}', '--family', 'workflow', '--workers', '8'), 300),
        Execution('requirements', 'check_native_workflow.py',
            ('--project', '{project}', '--family', 'requirements', '--workers', '8'), 300),
    ), (
        Execution('input-scope', 'check_native_workflow.py',
            ('--project', '{project}', '--family', 'input-scope', '--workers', '2'), 300),
        Execution('expanded', 'check_native_workflow.py',
            ('--project', '{project}', '--family', 'expanded', '--workers', '8'), 300),
        Execution('requests', 'roundtrip_native_workflow.py',
            ('--project', '{project}', '--comparison', '{output}/requirements/results.log.gz', '--workers', '6'), 300),
    ), (Execution('expanded-requests', 'roundtrip_native_workflow.py',
        ('--project', '{project}', '--comparison', '{output}/expanded/results.log.gz', '--workers', '16'), 300),)),
    fixtures=('tools/isabelle_native_execution.py', 'tools/workflow_json.py',
              'tools/compressed_reconstruction_suite.py'),
    boundary='The source boundary reconstructs all complete native comparisons and both request roundtrips, including original '
             'requirements, generated rule applications, complete executions, all certificates, '
             'admission results, comparisons and revisions. Every observation has a proved subject '
             'equation. Compilation binds every workflow position to its original native goals. '
             'Adequacy of those goals for real development roles, candidate scope, operative integration, '
             'condition-6 coverage, the complete cost account and genesis remain separate requirements.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
