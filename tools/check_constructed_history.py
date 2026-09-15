"""Compare complete history construction using both established local premises."""
import check_quoted_history
import registered_packet_execution


def program(engine, inputs):
    code = check_quoted_history.program(engine, inputs)
    assert code.count('N.quoted_history_packet') == 1
    return code.replace('N.quoted_history_packet', 'N.constructed_history_packet').replace(
        'QUOTED_HISTORY_', 'CONSTRUCTED_HISTORY_')


if __name__ == '__main__':
    raise SystemExit(registered_packet_execution.main(__file__,
        root='Constructed_History_Execution', theory='Factor_Constructed_History_Investigation',
        definition='constructed_history_investigation', prefix='CONSTRUCTED_HISTORY',
        selections=[[], [0], [0, 1]], program=program,
        question='Does composing the established predecessor readings and actual quoted policy scope '
                 'preserve every complete original history result and every original subject condition?',
        boundary='Original closed history validity and actual indexed membership supply the known '
                 'predecessor readings. The actual replay and quotation contracts supply the complete '
                 'policy scope. All remaining checks, full optional results, both preceding refinements '
                 'and all original subjects and methods remain. The omitted-membership control yields '
                 'only raw candidate results. Full physical cost, all six workflow conditions, historical '
                 'permission and reachability, native mathematical-proof admission, genesis and final audit remain open.'))
