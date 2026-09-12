"""The complete finite source proposal shared by native exploration and proof checks."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
import check_reasoning as review

ORIGINAL = ROOT / 'validation/fixtures/finite-inference-source.json'

def source_specification():
    old = json.loads(ORIGINAL.read_text())
    proposal = review.clone_json(old)
    source = review.clone_json(old['source'])
    package = review.clone_json(source['artifacts'][0][1])
    package['carrier'] += [[n] for n in range(24, 31)]
    package['incidence'] += [[[r], [s], [t]] for r, s, t in
        [(14, 24, 25), (25, 26, 28), (25, 27, 5), (26, 26, 27), (28, 28, 29), (28, 29, 30)]]
    package['functional'] += [[[30], [1]]]
    source['artifacts'].append([[2], package])
    source['bindings'].append([[2], [29], [2]])
    parent = review.clone_json(old['extended']['artifacts'][2][1])
    parent['carrier'] += [[n] for n in range(8, 18)]
    parent['incidence'] += [[[r], [s], [t]] for r, s, t in
        [(2, 8, 9), (9, 10, 12), (9, 11, 13), (10, 10, 11),
         (12, 12, 14), (12, 14, 15), (13, 13, 16), (13, 16, 17)]]
    parent['functional'] += [[[15], [24]], [[17], []]]
    extended = review.clone_json(source)
    extended['artifacts'] += [[[], parent], [[1], {'carrier': [[]], 'incidence': [], 'bag': [], 'functional': []}]]
    extended['bindings'] += [[[], [6], [2]], [[], [14], [2]], [[], [16], [1]]]
    proposal.update(source=source, extended=extended, package_use=[2], definition=[[2], [1]],
        schema_use=[2], replacement_use=[2],
        node_interior=old['node_interior'] + [[n] for n in [8, 9, 10, 11, 12, 13, 15, 17]],
        node_slots=[[6], [14], [16]], discharges=[[[[2], [24]], [[1], []]]],
        ordinary_premises=[[[24], [[2], [1]], review.payload()]], material_premises=[])
    proposal.pop('formation_precheck', None)
    proposal['boundary'] = ('Complete external finite source specification for native formatting and application construction. '
        'Source admission is established separately by the checked source theories. '
        'The old source artifacts, binding and counted occurrences remain exact. '
        'The separate assertion child carries no conclusion or truth field.')
    return proposal
