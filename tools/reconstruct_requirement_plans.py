"""Rebuild native requirement planning and complete artifact admission checks."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='requirement-plans',
    roots=('Requirement_Artifact_Execution', 'Factor_Base_Generation_Extensions'),
    export='Requirement_Artifact_Execution:requirement_artifacts.ML',
    session='Requirement_Plan_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Requirement_Artifact_Execution', '--module', 'Requirement_Plans', '--report', 'requirement_plan_report_value', '--scope', 'requirement_plan_counters', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='A run without --proof reconstructs the complete dependency proof, code and all native requirement reports from repository sources. The optional supplied-export mode rechecks execution only. Native plan construction and actual finite artifact admission are executed. Closed generations, preserved cause programs and extension through existing predecessors are proved. Historical permission, a complete development protocol and its overall cost account remain separate.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
