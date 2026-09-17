"""Reconstruct complete source retention and the native installation observations."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='requirement-sources',
    roots=('Requirement_Source_Execution', 'Retained_Clause_Execution', 'Factor_Requirement_Source_Examples'),
    export='Requirement_Source_Execution:requirement_sources.ML',
    session='Requirement_Source_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Requirement_Source_Execution', '--module', 'Requirement_Source_Execution', '--report', 'requirement_source_report_value', '--scope', 'retained_clause_indices', '--selections', 'source_requirement_variants', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='A run without --proof rebuilds all dependency proofs from HOL, recovers the complete diagnostics, exports the accepted code and executes every source-retention and meaning observation. The inputs name complete internally defined programs and artifact environments. Native package recovery, exact source inclusion, whole-clause admission and all-term meaning contracts establish the observations. The report comparison establishes reproduction only. Checked recursive plans have a proved installation over the actual retained native source. The finite reports do not execute that existential constructor or establish a complete development protocol.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
