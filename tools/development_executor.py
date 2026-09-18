#!/usr/bin/env python3
"""A deterministic executor: answer a development request from its packet alone.

The executor reads the packet and nothing else: no repository, no tool, no retained state. Its
answer restates the incumbent, the one code equation the packet's context states for the refined
constant, and proves it by the fact the answer frame provides for the subject's code equations in
effect. An answer states one equation, so an incumbent of several equations has no restating
answer here; that is a limit of the answer frame, recorded as such. That answer changes nothing
a request reads, so every admission of it must equal the admission of any other answer stating the
same equation; this is what makes the executor comparable with an agent or a replayed answer.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def restating_answer(packet):
    """The answer that states exactly the incumbent equation of the refined constant."""
    assert set(packet) >= {'request', 'constant', 'context', 'facts', 'answer'}
    assert 'development_demanded_code' in packet['facts']
    assert packet['answer']['fields'] == ['request', 'definitions', 'equation', 'proof']
    (incumbent,) = [item['text'] for item in packet['context'] if item['kind'] == 'code equation']
    return {'request': packet['request'], 'definitions': '', 'equation': incumbent,
            'proof': '  by (rule development_demanded_code)'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Use a fresh answer file.'
    args.output.write_text(json.dumps(restating_answer(json.loads(args.packet.read_text())), indent=1) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
