#!/usr/bin/env python3
"""A deterministic executor: answer a development request from its packet alone.

The executor reads the packet and nothing else: no repository, no tool, no retained state. Its
answer restates the incumbent, the one code equation the packet's context states for the refined
constant, and proves it by the fact the answer frame provides for the subject's code equations in
effect. An answer states one equation, so an incumbent of several equations has no restating
answer here; that is a limit of the answer frame, recorded as such. That answer changes nothing
a request reads, so every admission of it must equal the admission of any other answer stating the
same equation; this is what makes the executor comparable with an agent or a replayed answer.

Given a native packet (`--native`, the packet `native_answers.py packet` read back), the executor answers
natively: its answer is the edit that removes the incumbent statements of the packet and adds them again,
over the packet's names. That edit is the restating answer presented through the packet's names, so its
native judgment equals the native judgment of the restating answer the loop derives itself.
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


def restating_native_answer(record):
    """The native answer that removes the incumbent statements of its packet and adds them again."""
    assert set(record) >= {'request', 'packet'}
    packet = record['packet']
    assert set(packet) == {'names', 'constant', 'support', 'context', 'incumbent'}
    return {'request': record['request'], 'names': packet['names'], 'removed': packet['incumbent'],
            'added': packet['incumbent']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--native', action='store_true', help='Answer a native packet natively.')
    args = parser.parse_args()
    assert not args.output.exists(), 'Use a fresh answer file.'
    packet = json.loads(args.packet.read_text())
    answer = restating_native_answer(packet) if args.native else restating_answer(packet)
    args.output.write_text(json.dumps(answer, indent=1) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
