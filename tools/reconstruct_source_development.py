"""Reconstruct computed native source selection, installation and subsequent queries."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='source-development',
    roots=('Native_Source_Development',),
    export='Native_Source_Development:native_source_development.ML',
    session='Reconstruct_Source_Development',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Source_Development', '--module', 'Native_Source_Development', '--report', 'source_development_report_value', '--scope', 'development_case_inputs', '--selections', 'source_development_cases', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-empty', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Source_Development', '--module', 'Native_Source_Development', '--report', 'source_development_report_value', '--scope', 'development_empty_questions', '--selections', 'source_development_cases', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-first', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Source_Development', '--module', 'Native_Source_Development', '--report', 'source_development_report_value', '--scope', 'development_first_questions', '--selections', 'source_development_cases', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The original policy questions and complete source-change requests reconstruct all observations, native generation, criticism, comparison, revision, selection, installation and subsequent query evidence. A unique complete target is selected through the existing computed native producer choice. Final admission preserves the original target meaning, old material and ordered query scope. Empty and ambiguous choices, unreadable or incompatible sources, absent entries and missing required query evidence remain explicit. The requested finite target family, wider discovery, global cost, historical authority, native mathematical proof admission and genesis are separate boundaries.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
