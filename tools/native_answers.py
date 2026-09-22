"""Transport of native answers: the executor's JSON rendering of an answer to the bits the native reader reads.

An answer to a problem of a constant is a native value (Development_Native_Answers): the names it
uses, the entities it removes and the entities it adds, over positions of those names. Its JSON
rendering mirrors the native datatypes constructor by constructor; this module encodes the rendering
into the native presentation of the answer (payloads and pairs) and that presentation into its
prefix-free digit word, packed into octets with one terminating bit and zero padding, as report
words are packed. The encoding moves bytes and decides nothing: the native reader reads the bits
with an exact contract, so the answer judged is exactly the answer the bits present, and bits that
present no answer are refused there. A mistake in this module can change which answer arrives,
never what is judged of the answer that arrived.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json

import isabelle_places
import re
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

TYPE_TAGS = {'application': 0, 'free': 1, 'variable': 2}
TERM_TAGS = {'constant': 0, 'free': 1, 'variable': 2, 'bound': 3, 'abstraction': 4, 'application': 5}
ENTITY_TAGS = {'base_constant': 0, 'development_constant': 1, 'frontier_constant': 2,
               'definition': 3, 'specification': 4, 'code_equation': 5}
ANSWER_FIELDS = {'request', 'names', 'removed', 'added'}


def payload(octets):
    assert all(isinstance(o, int) and 0 <= o for o in octets)
    return ('payload', tuple(octets))


def pair(left, right):
    return ('pair', left, right)


def data_list(items):
    term = payload([])
    for item in reversed(items):
        term = pair(item, term)
    return term


def binary_digits(n):
    """The binary digits of a natural, least significant first, as Natural_Binary_Digits states them."""
    assert isinstance(n, int) and n >= 0
    digits = []
    while n:
        digits.append(n % 2 == 1)
        n //= 2
    return digits


def position(n):
    return payload([1 if b else 0 for b in binary_digits(n)])


def name(text):
    assert isinstance(text, str) and all(ord(c) < 128 for c in text), 'A name is ASCII.'
    return payload([ord(c) for c in text])


def sort(positions):
    assert isinstance(positions, list)
    return data_list([position(p) for p in positions])


def single(value, tags):
    assert isinstance(value, dict) and len(value) == 1, value
    (key, argument), = value.items()
    assert key in tags, key
    return key, argument


def type_term(value):
    key, argument = single(value, TYPE_TAGS)
    tag = payload([TYPE_TAGS[key]])
    if key == 'application':
        c, arguments = argument
        return pair(tag, pair(position(c), data_list([type_term(t) for t in arguments])))
    if key == 'free':
        a, s = argument
        return pair(tag, pair(position(a), sort(s)))
    a, i, s = argument
    return pair(tag, pair(position(a), pair(position(i), sort(s))))


def term_term(value):
    key, argument = single(value, TERM_TAGS)
    tag = payload([TERM_TAGS[key]])
    if key in ('constant', 'free'):
        x, t = argument
        return pair(tag, pair(position(x), type_term(t)))
    if key == 'variable':
        x, i, t = argument
        return pair(tag, pair(position(x), pair(position(i), type_term(t))))
    if key == 'bound':
        return pair(tag, position(argument))
    if key == 'abstraction':
        t, body = argument
        return pair(tag, pair(type_term(t), term_term(body)))
    t, u = argument
    return pair(tag, pair(term_term(t), term_term(u)))


def entity_term(value):
    key, argument = single(value, ENTITY_TAGS)
    return pair(payload([ENTITY_TAGS[key]]), term_term(argument))


def answer_term(answer):
    """The native presentation of an answer (development_native_answer_data)."""
    assert isinstance(answer, dict) and set(answer) == ANSWER_FIELDS, 'An answer has exactly its declared fields.'
    return pair(data_list([name(n) for n in answer['names']]),
                pair(data_list([entity_term(e) for e in answer['removed']]),
                     data_list([entity_term(e) for e in answer['added']])))


def delimited(bits):
    word = []
    for b in bits:
        word += [True, b]
    return word + [False]


def digit_natural_path(n):
    return delimited(binary_digits(n))


def digit_address_word(octets):
    word = digit_natural_path(len(octets))
    for o in octets:
        word += digit_natural_path(o)
    return word


def term_word(term):
    """The digit word of a term without targets (finite_term_word_with)."""
    word, pending = [], [term]
    while pending:
        current = pending.pop()
        if current[0] == 'payload':
            word += [False, False] + digit_address_word(current[1])
        else:
            word.append(True)
            pending += [current[2], current[1]]
    return word


def shared_word(term):
    """The shared word of a term without targets: the empty table of artifact rows, then the term's word."""
    return digit_natural_path(0) + term_word(term)


def packed(bits):
    """Octets of the bits followed by one terminating bit and zero padding, most significant bit first."""
    bits = list(bits) + [True]
    bits += [False] * (-len(bits) % 8)
    return bytes(int(''.join('1' if b else '0' for b in bits[i:i + 8]), 2) for i in range(0, len(bits), 8))


def answer_octets(answer):
    return packed(shared_word(answer_term(answer)))


# Reading: the inverse of each layer, refusing everything that is not exactly an encoding.

class Refused(ValueError):
    """The bits or the term present nothing of the expected kind."""


def unpacked(octets):
    """All bits of the octets, most significant first; the padding stays for the reader to strip."""
    return [bool(o >> (7 - i) & 1) for o in octets for i in range(8)]


def unpadded(bits):
    """The word before one terminating bit and zero padding."""
    end = len(bits)
    while end and not bits[end - 1]:
        end -= 1
    if not end:
        raise Refused('No terminating bit.')
    return bits[:end - 1]


class BitReader:
    def __init__(self, bits):
        self.bits, self.at = bits, 0

    def bit(self):
        if self.at >= len(self.bits):
            raise Refused('The word ends early.')
        self.at += 1
        return self.bits[self.at - 1]

    def natural(self):
        digits = []
        while self.bit():
            digits.append(self.bit())
        if digits and not digits[-1]:
            raise Refused('A natural has a leading zero digit.')
        return sum(1 << i for i, b in enumerate(digits) if b)

    def address(self):
        return [self.natural() for _ in range(self.natural())]

    def term(self):
        stack, done = [], []
        # Each pending entry is a pair awaiting its children; done collects finished subterms.
        while True:
            if self.bit():
                stack.append(2)
                continue
            if self.bit():
                raise Refused('A target has no reader here.')
            current = ('payload', tuple(self.address()))
            while stack and stack[-1] == 1:
                stack.pop()
                current = ('pair', done.pop(), current)
            if not stack:
                return current
            stack[-1] = 1
            done.append(current)


def shared_word_term(bits):
    """The term a shared word of a term without targets presents (finite_shared_word_read)."""
    reader = BitReader(bits)
    if reader.natural() != 0:
        raise Refused('A word with artifact rows has no reader here.')
    term = reader.term()
    if reader.at != len(bits):
        raise Refused('Bits follow the term.')
    return term


def octets_term(octets):
    return shared_word_term(unpadded(unpacked(octets)))


def read_payload(term):
    if term[0] != 'payload':
        raise Refused('Expected a payload.')
    return list(term[1])


def read_pair(term):
    if term[0] != 'pair':
        raise Refused('Expected a pair.')
    return term[1], term[2]


def read_list(term):
    items = []
    while term[0] == 'pair':
        items.append(term[1])
        term = term[2]
    if read_payload(term) != []:
        raise Refused('A list ends in a nonempty payload.')
    return items


def read_position(term):
    digits = read_payload(term)
    if any(d not in (0, 1) for d in digits) or (digits and digits[-1] != 1):
        raise Refused('Not a binary natural.')
    return sum(1 << i for i, d in enumerate(digits) if d)


def read_name(term):
    octets = read_payload(term)
    if any(o >= 128 for o in octets):
        raise Refused('A name is ASCII.')
    return ''.join(chr(o) for o in octets)


def tagged(term, tags):
    head, body = read_pair(term)
    code = read_payload(head)
    names = [key for key, value in tags.items() if [value] == code]
    if len(names) != 1:
        raise Refused('Unknown constructor.')
    return names[0], body


def read_type(term):
    key, body = tagged(term, TYPE_TAGS)
    a, rest = read_pair(body)
    if key == 'application':
        return {key: [read_position(a), [read_type(t) for t in read_list(rest)]]}
    if key == 'free':
        return {key: [read_position(a), [read_position(p) for p in read_list(rest)]]}
    i, s = read_pair(rest)
    return {key: [read_position(a), read_position(i), [read_position(p) for p in read_list(s)]]}


def read_term(term):
    key, body = tagged(term, TERM_TAGS)
    if key == 'bound':
        return {key: read_position(body)}
    x, rest = read_pair(body)
    if key in ('constant', 'free'):
        return {key: [read_position(x), read_type(rest)]}
    if key == 'variable':
        i, t = read_pair(rest)
        return {key: [read_position(x), read_position(i), read_type(t)]}
    if key == 'abstraction':
        return {key: [read_type(x), read_term(rest)]}
    return {key: [read_term(x), read_term(rest)]}


def read_entity(term):
    key, body = tagged(term, ENTITY_TAGS)
    return {key: read_term(body)}


def packet_json(term):
    """The native packet a presented optional packet holds (development_named_native_packet_data)."""
    present = read_list(term)
    if not present:
        return None
    (packet,) = present
    names, rest = read_pair(packet)
    constant, rest = read_pair(rest)
    support, rest = read_pair(rest)
    context, incumbent = read_pair(rest)
    return {'names': [read_name(n) for n in read_list(names)], 'constant': read_term(constant),
            'support': [read_position(p) for p in read_list(support)],
            'context': [read_entity(e) for e in read_list(context)],
            'incumbent': [read_entity(e) for e in read_list(incumbent)]}


def answer_json(term):
    names, rest = read_pair(term)
    removed, added = read_pair(rest)
    return {'names': [read_name(n) for n in read_list(names)], 'removed': [read_entity(e) for e in read_list(removed)],
            'added': [read_entity(e) for e in read_list(added)]}


# The host transport of native packets and answers: bytes moved, nothing decided.

import build  # noqa: E402
import execution_support as investigate  # noqa: E402
import proved_code  # noqa: E402
from evidence_io import write_json  # noqa: E402

POLY = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
STATES = {'development_seed': 'Native_Development_Seed', 'development_machinery': 'Native_Development_Machinery'}
SUBJECT = re.compile(r"[A-Za-z][A-Za-z_0-9']*(\.[A-Za-z][A-Za-z_0-9']*)*")


def active_base(base):
    return (base or Path(json.loads(isabelle_places.ACTIVE_CONTEXT.read_text())['directory'])).resolve()


def run(name, command, log, timeout):
    with log.open('w') as stream:
        try:
            code = build.run_session([str(c) for c in command], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                     timeout=timeout)
        except subprocess.TimeoutExpired:
            code = 'timeout'
    return {'name': name, 'exit_code': code, 'log': str(log)}


def exported(base, state, output, timeout):
    """The module of the state's native export, exported from the accepted base."""
    module = STATES[state]
    step = run('export', [sys.executable, '-B', TOOLS / 'export_proved_code.py', '--context', base, '--project', ROOT,
                          '--output', output / 'export', '--module', module + ':' + module.lower() + '.ML'],
               output / 'export.log', timeout)
    assert step['exit_code'] == 0, 'Export failed.'
    return module, output / 'export' / (module.lower() + '.proof.json')


def presented(module, proof, report, subject, output, timeout, bits=None):
    command = [sys.executable, '-B', TOOLS / 'check_presented_report.py', '--proof', proof, '--poly', POLY,
               '--project', ROOT, '--theory', module, '--module', module, '--report', report, '--subject', subject,
               '--workers', '4', '--timeout', timeout, '--output', output]
    step = run(output.name, command + ([] if bits is None else ['--bits', bits]), output.parent / (output.name + '.log'),
               timeout + 60)
    assert step['exit_code'] == 0, 'The presentation of ' + report + ' failed.'
    return json.loads((output / 'receipt.json').read_text())['word']


def packet_main(args):
    """Present the native packet of the request named by its subject and read it back."""
    assert args.state in STATES and SUBJECT.fullmatch(args.subject)
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh output directory.'
    output.mkdir(parents=True)
    base = active_base(args.base)
    module, proof = exported(base, args.state, output, args.timeout)
    word = presented(module, proof, args.state + '_native_packet_value', args.subject, output / 'packet', args.timeout)
    with gzip.open(output / 'packet' / 'report.word.gz', 'rb') as stream:
        packet = packet_json(octets_term(stream.read()))
    assert packet is not None, 'No issued request has this subject.'
    record = {'request': {'state': args.state, 'subject': args.subject}, 'packet': packet, 'packet_word': word}
    write_json(output / 'packet.json', record)
    print(json.dumps({'packet_word': word, 'names': len(packet['names']), 'context': len(packet['context']),
                      'incumbent': len(packet['incumbent'])}))
    return 0


def validated(answer):
    assert isinstance(answer, dict) and set(answer) == ANSWER_FIELDS, 'An answer has exactly its declared fields.'
    request = answer['request']
    assert isinstance(request, dict) and set(request) == {'state', 'subject'}
    assert request['state'] in STATES and SUBJECT.fullmatch(request['subject'])
    return answer


def summary_program(state, subject, bits):
    def program(engine, _inputs):
        return ('use ' + investigate.ml_string(str(engine)) + ';\n'
                'structure N = ' + STATES[state] + ';\n'
                'fun octet_bits w = List.tabulate (8, fn i => Word8.andb (Word8.>> (w, Word.fromInt (7 - i)), 0w1) = 0w1);\n'
                'val bits = let val stream = BinIO.openIn ' + investigate.ml_string(str(bits)) + ';\n'
                '  val octets = BinIO.inputAll stream in BinIO.closeIn stream;\n'
                '  List.concat (Word8Vector.foldr (fn (w, acc) => octet_bits w :: acc) [] octets) end;\n'
                'fun nat n = IntInf.toString (N.integer_of_nat n);\n'
                'fun words xs = "[" ^ String.concatWith "," (map (fn s => "\\"" ^ s ^ "\\"") xs) ^ "]";\n'
                'fun nats xs = "[" ^ String.concatWith "," (map nat xs) ^ "]";\n'
                'val () = case N.' + state + '_native_summary ' + investigate.ml_string(subject) + ' bits of\n'
                '    NONE => print "SUMMARY null\\n"\n'
                '  | SOME (read, (accepted, (counts, (excess, sizes)))) =>\n'
                '      print ("SUMMARY {\\"read\\":" ^ Bool.toString read ^ ",\\"accepted\\":" ^ Bool.toString accepted ^\n'
                '        ",\\"counts\\":" ^ nats counts ^ ",\\"excess\\":" ^ words excess ^ ",\\"sizes\\":" ^ nats sizes ^ "}\\n");\n')
    return program


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def judge_main(args):
    """Judge a native answer: its octets are presented to the native judgment of the request it names."""
    answer = validated(json.loads(args.answer.read_text()))
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh output directory.'
    output.mkdir(parents=True)
    state, subject = answer['request']['state'], answer['request']['subject']
    octets = answer_octets({k: answer[k] for k in ANSWER_FIELDS - {'request'}} | {'request': None})
    bits = output / 'answer.octets'
    bits.write_bytes(octets)
    base = active_base(args.base)
    module, proof = exported(base, state, output, args.timeout)
    word = presented(module, proof, state + '_native_judgment_value', subject, output / 'judgment', args.timeout, bits)
    receipt = proved_code.checked_execution(
        proof, POLY, output / 'summary', required_theories=[module], inputs={'subject': subject},
        input_paths=[bits], program=summary_program(state, subject, bits), assess=lambda _i, text: text,
        question='Which reasons does the native judgment of this answer retain?',
        boundary='A diagnostic reading of the exported native judgment; the presented word is the evidence.',
        timeout=args.timeout, project=ROOT)
    assert receipt['status'] == 'accepted', receipt.get('error')
    lines = [line for line in receipt['assessment'].splitlines() if line.startswith('SUMMARY ')]
    assert len(lines) == 1, 'Expected one judgment summary.'
    summary = json.loads(lines[0][len('SUMMARY '):])
    record = {'answer': answer, 'answer_sha256': hashlib.sha256(canonical(answer)).hexdigest(),
              'answer_octets_sha256': hashlib.sha256(octets).hexdigest(), 'native': True,
              'harness_sha256': investigate.file_hash(Path(__file__)),
              'base_receipt_sha256': investigate.file_hash(base / 'accepted-context.json'),
              'status': 'judged', 'judgment_word': word, 'summary': summary}
    write_json(output / 'answer.json', record)
    if args.retain is not None:
        write_json(args.retain, record)
    print(json.dumps({'judgment_word': word, 'summary': summary}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    packet = commands.add_parser('packet', help='Present and read back the native packet of a request.')
    packet.add_argument('--state', required=True, choices=sorted(STATES))
    packet.add_argument('--subject', required=True)
    judge = commands.add_parser('judge', help='Judge a native answer natively.')
    judge.add_argument('--answer', type=Path, required=True)
    judge.add_argument('--retain', type=Path, help='Write the retained record of the judged answer here.')
    for command in (packet, judge):
        command.add_argument('--output', type=Path, required=True)
        command.add_argument('--base', type=Path, help='Accepted context; defaults to the active one.')
        command.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    return packet_main(args) if args.command == 'packet' else judge_main(args)


if __name__ == '__main__':
    raise SystemExit(main())
