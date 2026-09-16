"""Encode complete JSON request values as applications of proved native constructors."""
from pathlib import Path
import json

from machine_reports import unique_object


def fields(value, names):
    if not isinstance(value, dict) or set(value) != set(names):
        raise ValueError('Expected exactly these fields: ' + ', '.join(names))
    return value


def sequence(value, encode):
    if not isinstance(value, list):
        raise ValueError('Expected a list.')
    return '[' + ','.join(encode(item) for item in value) + ']'


def pair(value, first, second):
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError('Expected a pair.')
    return '(' + first(value[0]) + ',' + second(value[1]) + ')'


def natural(value):
    if type(value) is not int or value < 0:
        raise ValueError('Expected a nonnegative integer.')
    return '(N.nat_of_integer ' + str(value) + ')'


def address(value):
    return sequence(value, natural)


def use(value):
    return 'NONE' if value is None else '(SOME ' + address(value) + ')'


def site(value):
    return pair(value, use, address)


def edge(value):
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError('Expected an incidence triple.')
    return '(' + address(value[0]) + ',(' + address(value[1]) + ',' + address(value[2]) + '))'


def artifact(value):
    fields(value, ['carrier', 'incidence', 'counted_data', 'functional_data'])
    data = lambda row: pair(row, address, address)
    return '(N.finite_enumerated_artifact ' + address_list(value['carrier']) + ' ' + sequence(value['incidence'], edge) + \
        ' ' + sequence(value['counted_data'], data) + ' ' + sequence(value['functional_data'], data) + ')'


def address_list(value):
    return sequence(value, address)


def environment(value):
    fields(value, ['artifacts', 'bindings'])
    return '(N.finite_enumerated_environment ' + sequence(value['artifacts'], lambda row: pair(row, use, artifact)) + \
        ' ' + sequence(value['bindings'], lambda row: pair(row, site, use)) + ')'


def target(value):
    if isinstance(value, dict) and set(value) == {'whole_artifact'}:
        return '(N.Finite_Whole ' + artifact(value['whole_artifact']) + ')'
    fields(value, ['anchored_artifact'])
    return '(N.Finite_Anchor ' + pair(value['anchored_artifact'], artifact, address) + ')'


def term(value):
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError('Expected one term constructor.')
    if 'payload' in value:
        return '(N.Finite_Payload ' + address(value['payload']) + ')'
    if 'pair' in value:
        return '(N.Finite_Pair ' + pair(value['pair'], term, term) + ')'
    fields(value, ['target'])
    return '(N.Finite_Target ' + target(value['target']) + ')'


def goal(value):
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError('Expected one admission-goal constructor.')
    if 'existing' in value:
        return '(N.Existing_Admission ' + site(value['existing']) + ')'
    if 'paired' in value:
        return '(N.Paired_Admission ' + pair(value['paired'], goal, goal) + ')'
    fields(value, ['collected'])
    return '(N.Collected_Admission ' + goal(value['collected']) + ')'


def scope(value):
    if isinstance(value, dict) and set(value) == {'input'} and value['input'] is True:
        return 'N.Workflow_Input'
    if isinstance(value, dict) and set(value) == {'values'}:
        return '(N.Workflow_Values ' + sequence(value['values'], term) + ')'
    fields(value, ['generated_entry'])
    return '(N.Workflow_Generated ' + site(value['generated_entry']) + ')'


def requirement(value):
    fields(value, ['source', 'source_use', 'source_root', 'goals', 'candidates'])
    return '(N.workflow_requirement_input ' + environment(value['source']) + ' ' + use(value['source_use']) + \
        ' ' + address(value['source_root']) + ' ' + sequence(value['goals'], goal) + ' ' + scope(value['candidates']) + ')'


def request(value):
    fields(value, ['requirements', 'problem'])
    return sequence(value['requirements'], requirement), term(value['problem'])


def read_request(path):
    value = json.loads(Path(path).read_text(), object_pairs_hook=unique_object)
    request(value)
    return value
