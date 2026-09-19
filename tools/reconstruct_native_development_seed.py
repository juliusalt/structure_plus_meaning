"""Reconstruct the seeded native development state read from the checked Isabelle context."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-development-seed',
    roots=('Native_Development_Seed',),
    export='Native_Development_Seed:native_development_seed.ML',
    session='Reconstruct_Native_Development_Seed',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_report_value', '--scope', 'development_seed_state', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-missing-declaration', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_report_value', '--scope', 'development_seed_missing_declaration', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-extra-entities', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_report_value', '--scope', 'development_seed_extra_entities', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-renamed', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_report_value', '--scope', 'development_seed_renamed', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-moved-equalities', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_reports_value', '--scope', 'development_seed_moved_equalities', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-problems', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_problem_value', '--scope', 'development_seed_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-problems-answered', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_problem_value', '--scope', 'development_seed_answered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-loop', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_loop_value', '--scope', 'development_seed_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-verification', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_verification_value', '--scope', 'development_seed_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-succession', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_succession_value', '--scope', 'development_seed_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-publication', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Seed', '--module', 'Native_Development_Seed', '--report', 'development_seed_publication_value', '--scope', 'development_seed_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The checked context defines the roots of the three paused refinement candidates, the entities '
             'their expansion contributes and the frontier of development constants it does not expand. The '
             'report presents that rooted state with its computed observations: unknown name positions, '
             'undeclared constants, malformed entities, entities unreached from the roots, the frontier, and '
             'the entities accepted by the ground program of the state against a demand, derived from the '
             'state, that includes one constant declared outside the name table. Acceptance is exactly '
             'membership of the supplied entities, proved once for the notion. Removing the declarations of '
             'every root constant exposes them as undeclared and refuses the state, and the control names no '
             'position of the entity list; adding a declaration at a position outside the name table and an '
             'equation without a head exposes unknown positions, unreached and malformed entities. Reversing '
             'the name table moves every position and reports the image of the original observations under '
             'that correspondence. Moving a name the equation reader recognizes moves no position; these '
             'controls are derived from the reader, one for each equality name it recognizes, and report '
             'what the state reads without that name. Every definition and code equation of this state is a '
             'Pure equality: without Pure.eq those twenty entities lose their subjects and are malformed, and '
             'seventy entities are no longer reached from the roots, while moving HOL.eq changes no '
             'observation. Acceptance is unchanged under both, because it decides membership of the supplied '
             'entities and reads no name. The exporter\'s selection inside the checked '
             'context, the adequacy of these roots to the candidates and every extension of the frontier '
             'remain open. The problem report presents one refinement problem per root constant: its subject '
             'is that constant, its contract is the constant as the state declares it, and its incumbent is the '
             'family of code equations the state states for it, read exactly as declared and selected by the '
             'computed refinement condition on the actual entities rather than supplied. A kernel definition '
             'of the same constant has the same subject reading and is refused, because a refinement does not '
             'replace a definition; a constant the state declares other than exactly once, or states no code '
             'equation for, yields no problem and is retained as unstated. Dependencies are read from those actual statements: a problem depends '
             'on the problems of the other root constants its own statement mentions, with the mentioned '
             'constant as the premise slot, so no grouping and no list position enters. A grouping of more '
             'than one constant is retained as an obstruction, because no entity and no term of the state '
             'states the refinement of several constants at once. On this state that reading finds no '
             'dependency at all: the demanded statements mention no other root, so every premise set is '
             'empty and the ten problems are independent, which the grouping did not report. The remaining '
             'variation is the answered set: with nothing answered every problem is ready, and with every '
             'problem answered none is. Identifying these root constants from the measured candidates '
             'remains a choice generated outside the native process: every seeded problem records that '
             'residual origin and generated authority, and no seeded problem carries owner authority. The '
             'selection is the admitted answer of the reusable filtered native question on the state\'s own '
             'entities; its execution and admission are separate evidence from this presentation. The verification '
             'report judges answer states of every request by the difference they make to the seeded state, read '
             'through the names both tables share: a refinement may replace the code equations of its subject and '
             'nothing else, its equations must stay within the issued support, and the answer state must be closed '
             'and keep the roots. The unchanged state and its reversed table are accepted for every request; an '
             'added axiom, dropped equations, an equation stated through a constant the state does not know, '
             'changed equations of the other subjects and a removed definition are refused with their reasons, '
             'and the unknown constant is named as the one constant outside the support. These answer states are '
             'derived from the request and the state; no actual answer has been verified by this report. The succession '
             'report admits, for every request, the unchanged answer and the answer with the reversed table as '
             'generations of the seeded development: each successor carries the answered problem, its generation '
             'and every other problem moved with the correspondence, and computes the readiness of the successor and '
             'the currency of every request; neither answer changes what a request reads. The publication '
             'report is the published state of the seeded development: one base generation per problem at the '
             'problem\'s locus, which is its contract presented with the names it uses, with the incumbent '
             'equations presented with their names as payload, each recorded in an environment of its own; its '
             'cause is a certified call of the policy that lists that family\'s complete data quotation, which is '
             'constructed only because every entity of the family is an entity of the checked context. For every '
             'issued request the unchanged answer, certified in the same way from the answer state and recorded '
             'beside the incumbent it was judged against, citing it, is published by the transaction that expects '
             'that incumbent and replaces exactly its locus; the answer with the reversed table, certified against '
             'the same incumbent, conflicts with the complete observed comparison, because the locus now holds the '
             'first answer; the two answers present equal payloads; and publishing all unchanged answers in turn '
             'applies every transaction. Transactions are executed on finite generations and are proved to be the '
             'structural transactions on the decoded cores. A recorded cause carries the policy that lists its '
             'family, not the checked context: that the family was accepted is the constructor\'s contract, and '
             'the verdict that admitted an answer stays in the development\'s history.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
