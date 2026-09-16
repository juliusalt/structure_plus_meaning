"""Encode every original source-change field through proved native constructors."""
import workflow_input as values


def triple(value, first, second, third):
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError('Expected a triple.')
    return '(' + first(value[0]) + ',(' + second(value[1]) + ',' + third(value[2]) + '))'


def pattern(value):
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError('Expected one pattern constructor.')
    if 'variable' in value:
        return '(N.Finite_Variable ' + values.address(value['variable']) + ')'
    if 'payload' in value:
        return '(N.Finite_Pattern_Payload ' + values.address(value['payload']) + ')'
    if 'pair' in value:
        return '(N.Finite_Pattern_Pair ' + values.pair(value['pair'], pattern, pattern) + ')'
    values.fields(value, ['target'])
    return '(N.Finite_Pattern_Target ' + values.target(value['target']) + ')'


def material(value):
    names = ['source', 'atoms', 'edges', 'counts', 'functions']
    values.fields(value, names)
    return '(N.source_development_material_input ' + ' '.join(pattern(value[k]) for k in names) + ')'


def schema(value):
    values.fields(value, ['conclusion', 'premises', 'materials'])
    return '(N.source_development_schema_input ' + pattern(value['conclusion']) + ' ' + \
        values.sequence(value['premises'], lambda row: triple(row, values.address, values.site, pattern)) + ' ' + \
        values.sequence(value['materials'], lambda row: values.pair(row, values.address, material)) + ')'


def program(value):
    values.fields(value, ['interfaces', 'clauses'])
    return '(N.source_development_program_input ' + \
        values.sequence(value['interfaces'], lambda row: values.pair(row, values.site, pattern)) + ' ' + \
        values.sequence(value['clauses'], lambda row: values.pair(row,
            lambda key: values.pair(key, values.site, values.address), schema)) + ')'


def proposal(value):
    values.fields(value, ['program', 'entry'])
    return '(' + program(value['program']) + ',' + values.site(value['entry']) + ')'


def request(value):
    values.fields(value, ['source', 'source_use', 'source_root', 'targets', 'input', 'outputs'])
    return '(N.source_development_request_input ' + values.environment(value['source']) + ' ' + \
        values.use(value['source_use']) + ' ' + values.address(value['source_root']) + ' ' + \
        values.sequence(value['targets'], proposal) + ' ' + values.term(value['input']) + ' ' + \
        values.sequence(value['outputs'], values.term) + ')'
