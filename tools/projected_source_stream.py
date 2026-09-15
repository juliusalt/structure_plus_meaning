"""Read complete original sources through the actual packet projection contract."""


def program(code, *, kind):
    assert kind in ['replay', 'history']
    original = 'N.digit_' + kind + '_source_cases scope'
    assert code.count(original) == 1
    return code.replace(original, 'N.' + kind + '_table_sources table', 1)
