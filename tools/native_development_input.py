"""Encode complete native development questions through proved native constructors."""
import json
from pathlib import Path
import workflow_input as values


def condition(value):
    values.fields(value, ['source', 'source_use', 'source_root', 'goals'])
    return '(N.development_condition_input ' + values.environment(value['source']) + ' ' + \
        values.use(value['source_use']) + ' ' + values.address(value['source_root']) + ' ' + \
        values.sequence(value['goals'], values.goal) + ')'


def question(value):
    values.fields(value, ['source', 'source_use', 'source_root', 'generator_entry', 'problem',
                          'conditions', 'scope_criticism', 'selected_facets'])
    return '(N.native_development_question_input ' + values.environment(value['source']) + ' ' + \
        values.use(value['source_use']) + ' ' + values.address(value['source_root']) + ' ' + \
        values.site(value['generator_entry']) + ' ' + values.term(value['problem']) + ' ' + \
        values.sequence(value['conditions'], condition) + ' ' + condition(value['scope_criticism']) + ' ' + \
        values.sequence(value['selected_facets'], values.natural) + ')'


def read_question(path):
    value = json.loads(Path(path).read_text(), object_pairs_hook=values.unique_object)
    question(value)
    return value
