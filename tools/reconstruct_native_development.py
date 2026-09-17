"""Reconstruct the complete closed native development cycle and its original inputs."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-development',
    roots=('Native_Development_Execution',),
    export='Native_Development_Execution:native_development.ML',
    session='Reconstruct_Native_Development',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Execution', '--module', 'Native_Development', '--report', 'native_development_report_value', '--scope', 'native_development_indices', '--selections', 'native_development_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The local source and input boundary reconstructs native generation, original condition compilation, all observations and certificates, independent complete evidence inspection and native scope criticism, comparison, revision, admission. The declared finite one-step generation scope remains explicit; adequacy for wider development problems and the eventual genesis handoff are separate conditions.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
