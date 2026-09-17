"""Reconstruct the seeded native development state read from the checked Isabelle context."""
from reconstruction import Execution, Recipe, main


def presentation(name, scope, report='development_seed_report_value'):
    return Execution(name, 'check_presented_report.py',
                     ('--project', '{project}', '--theory', 'Native_Development_Seed',
                      '--module', 'Native_Development_Seed', '--report', report,
                      '--scope', scope, '--workers', '4', '--timeout', '1200'), 1300)


RECIPE = Recipe(
    name='native-development-seed',
    roots=('Native_Development_Seed',),
    export='Native_Development_Seed:native_development_seed.ML',
    session='Reconstruct_Native_Development_Seed',
    groups=((
        presentation('presentation', 'development_seed_state'),
        presentation('presentation-missing-declaration', 'development_seed_missing_declaration'),
        presentation('presentation-extra-entities', 'development_seed_extra_entities'),
        presentation('presentation-renamed', 'development_seed_renamed'),
        presentation('presentation-moved-equality', 'development_seed_moved_equality'),
        presentation('presentation-problems', 'development_seed_unanswered',
                     report='development_seed_problem_value'),
        presentation('presentation-problems-answered', 'development_seed_replay_answered',
                     report='development_seed_problem_value'),
    ),),
    boundary='The checked context defines the roots of the three paused refinement candidates, the entities '
             'their expansion contributes and the frontier of development constants it does not expand. The '
             'report presents that rooted state with its computed observations: unknown name positions, '
             'undeclared constants, malformed entities, entities unreached from the roots, the frontier, and '
             'the entities accepted by the ground program of the state against a demand, derived from the '
             'state, that includes one constant declared outside the name table. Acceptance is exactly '
             "membership of the supplied entities, proved once for the notion. Removing the first root's "
             'declaration exposes an undeclared constant and refuses it; adding a declaration at a position '
             'outside the name table and an equation without a head exposes unknown positions, unreached and '
             'malformed entities. Reversing the name table moves every position and reports the image of the '
             'original observations under that correspondence; moving the name of HOL equality instead moves '
             'no position and reports the code-equation readings the state loses with it. The exporter\'s '
             'selection inside the checked context, the adequacy of these roots to the candidates and every '
             'extension of the frontier remain open. The problem report presents the three measured refinement '
             'candidates as problems whose subjects are the constants they would change, each decomposed into '
             'one leaf per constant with that constant as its premise slot, and the readiness computed from '
             'those actual dependencies: with nothing answered only the leaves are ready, and answering the '
             "replay candidate's leaves makes exactly that candidate ready. The grouping into candidates, the "
             'decomposition and the leaf contracts are generated choices retained as residuals; no seeded '
             'problem carries owner authority.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
