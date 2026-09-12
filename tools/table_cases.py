"""Complete small functional-table scope and separate larger structural controls."""
import itertools


def payload(*xs):
    return {'payload': list(xs)}


def pair(x, y):
    return {'pair': [x, y]}


TARGET = {'empty_artifact': True}


def cases():
    keys = [payload(0), payload(1)]
    values = [payload(2), payload(3), TARGET, pair(payload(2), TARGET)]
    rows = [list(row) for row in itertools.product(keys, values)]
    tables = [[]] + [list(xs) for n in [1, 2] for xs in itertools.product(rows, repeat=n)]
    result = [{'name': f'small-{i}-{j}', 'left': xs, 'right': ys}
              for i, xs in enumerate(tables) for j, ys in enumerate(tables)]
    literal = [[payload(0), pair(payload(2), TARGET)]]
    result += [
        {'name': 'literal-target-value', 'left': literal, 'right': literal},
        {'name': 'same-first-observation-different-second', 'left': literal,
         'right': [[payload(0), pair(payload(2), payload(2))]]},
        {'name': 'literal-target-key', 'left': [[TARGET, payload(0)]], 'right': [[TARGET, payload(0)]]},
        {'name': 'malformed-key', 'left': [[payload(256), TARGET]], 'right': [[payload(256), TARGET]]},
        {'name': 'malformed-value', 'left': [[payload(0), payload(256)]], 'right': [[payload(0), payload(256)]]},
        {'name': 'unused-malformed-value', 'left': literal + [[payload(1), payload(256)]], 'right': literal},
    ]
    for n in [16, 128, 512]:
        xs = [[payload(i // 256, i % 256), values[i % len(values)]] for i in range(n)]
        result += [
            {'name': f'large-{n}-reversed', 'left': xs, 'right': xs[::-1]},
            {'name': f'large-{n}-missing', 'left': xs, 'right': xs[:-1]},
            {'name': f'large-{n}-duplicate', 'left': xs, 'right': xs[::-1] + [xs[0]]},
        ]
    return {'small_tables': len(tables), 'small_pairs': len(tables) ** 2,
            'cases': result,
            'boundary': 'Every ordered list of length at most two over two keys and four complete values is compared with every other such list. Separate controls cover malformed fields and larger unique tables. The universal native contract has a wider finite-term domain.'}
