"""Reconstruct the complete closed native development cycle and its original inputs."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-development',
    roots=('Native_Development_Execution',),
    export='Native_Development_Execution:native_development.ML',
    session='Reconstruct_Native_Development',
    groups=((Execution('producers', 'check_native_development.py',
        ('--project', '{project}', '--workers', '16'), 600),),
        (Execution('questions', 'roundtrip_native_development.py',
        ('--project', '{project}', '--comparison', '{output}/producers/results.log.gz', '--workers', '16'), 600),)),
    fixtures=('tools/isabelle_native_execution.py', 'tools/workflow_json.py',
              'tools/compressed_reconstruction_suite.py'),
    boundary='The local source and input boundary reconstructs native generation, original condition '
             'compilation, all observations and certificates, independent complete evidence inspection '
             'and native scope criticism, comparison, revision, admission and whole-question roundtrip. '
             'The declared finite one-step generation scope remains explicit; adequacy for wider '
             'development problems and the eventual genesis handoff are separate conditions.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
