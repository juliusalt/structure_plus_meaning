"""Reconstruct computed native source selection, installation and subsequent queries."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='source-development',
    roots=('Native_Source_Development',),
    export='Native_Source_Development:native_source_development.ML',
    session='Reconstruct_Source_Development',
    groups=((Execution('sources', 'check_source_development.py',
        ('--project', '{project}', '--workers', '16'), 2400),
        Execution('empty', 'check_source_development.py',
        ('--project', '{project}', '--empty', '--workers', '2'), 2400),
        Execution('first', 'check_source_development.py',
        ('--project', '{project}', '--first', '--workers', '4'), 2400)),
        (Execution('requests', 'roundtrip_source_development.py',
        ('--project', '{project}', '--comparison', '{output}/sources/results.log.gz', '--workers', '16'), 2400),)),
    fixtures=('tools/isabelle_native_execution.py', 'tools/source_development_input.py',
              'tools/source_development_json.py', 'tools/compressed_reconstruction_suite.py'),
    boundary='The original policy questions and complete source-change requests reconstruct all observations, '
        'native generation, criticism, comparison, revision, selection, installation and subsequent query evidence. '
        'A unique complete target is selected through the existing computed native producer choice. Final admission '
        'preserves the original target meaning, old material and ordered query scope. Empty and ambiguous choices, '
        'unreadable or incompatible sources, absent entries and missing required query evidence remain explicit. '
        'The requested finite target family, wider discovery, global cost, historical authority, native mathematical '
        'proof admission and genesis are separate boundaries.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
