"""Reconstruct the complete requirement decisions execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='requirement-decisions',
    roots=('Requirement_Decision_Execution',),
    export='Requirement_Decision_Execution:requirement_decisions.ML',
    session='Reconstruct_requirement_decisions',
    groups=((Execution("comparison", 'check_requirement_decisions.py', ("--project", "{project}"), 2100),
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Requirement_Decision_Execution', '--module', 'Requirement_Decision_Execution', '--report', 'requirement_decision_report_value', '--scope', 'requirement_decision_indices', '--selections', 'requirement_decision_report_selections', '--workers', '4', '--timeout', '1200'), 1300),),),
    boundary='The complete original native source, every original requirement and term precede actual construction. Every returned environment, source program, term-derived demand, positive answer, certificate, independent proof check and admitted term family is reproduced with full original and candidate evaluations and all comparison and revision reasons. This scoped operation does not establish complete development-workflow enforcement, subject coverage, history permission, full cost or genesis.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
