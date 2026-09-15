"""Report the native packet's derived observations under its complete cell contract."""


def program(code, *, kind):
    assert kind in ['replay', 'history']
    variable = 'assessment' if kind == 'replay' else 'result'
    inspector = 'digit_replay_family_inspect' if kind == 'replay' else 'digit_history_question_inspect'
    declaration = 'fun jassessed (m,' + variable + ') = '
    start = code.index(declaration)
    end = code.index('\nfun ', start + len(declaration))
    original = code[start:end]
    inspected = 'N.' + inspector + ' ' + variable + ' f'
    assert original.count(inspected) == 1
    replacement = original.replace(declaration, 'fun jassessed rows w (m,' + variable + ') = ', 1)
    replacement = replacement.replace(inspected, 'N.read_assessed_observation rows m w f', 1)
    code = code[:start] + replacement + code[end:]
    call = '(jlist jassessed cells)'
    assert code.count(call) == 1
    return code.replace(call, '(jlist (jassessed (#1 comparison) w) cells)', 1)
