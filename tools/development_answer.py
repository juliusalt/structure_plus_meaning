#!/usr/bin/env python3
"""Check an executor's answer to a development request and present its native verdict.

The harness moves bytes and invokes the checked tools; it decides nothing. It places the answer's
declared parts (new definitions, the equation and its proof) inside a fixed frame, re-exports the
requested state from the same roots in the answer's checked context, and exports the native verdict
of the request on the two states. Isabelle accepts or refuses the theories; the exported verdict
computation judges the difference; the presented word is the retained evidence. Answer content is
never read beyond being placed, and no generated text is retained: the answer file, the base context
and the verdict word reproduce it.

An answer to a request of the refinement layer is framed where it would be adopted: its theory
imports exactly the theories the layer's import boundary imports, and the request state is defined
beside it from the boundary itself. The theory Isabelle accepts is therefore the theory adoption
installs, and there is one acceptance, not a second one in another context. The theory is named by
the answer's own content, so its name is stable across replays and unique in the session; that name
is a transport choice, not a correspondence. Once an answer's theory is part of the repository, the
answer is adopted: the harness does not frame it again and judges the published state as the answer
to the request that state presents, which is an unchanged answer when the adoption is exact.

Before an answer is framed, Isabelle reads its declared parts with the outer syntax of the frame
(Development_Answer_Parts), in a session of its own that holds the parts only as ML strings. An answer
whose parts hold anything but definitional commands, theorem statements and their proofs, document text,
one proposition and one proof is refused with Isabelle's reason, and its theory is never processed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

import build
import execution_support as investigate
import proved_code
from evidence_io import write_json

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
POLY = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
HEAPS = Path('/tmp/structural-isabelle/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux')
ENV_HOME = {'USER_HOME': '/tmp/structural-isabelle', 'PYTHONDONTWRITEBYTECODE': '1'}

# The requested states the harness can frame. A seeded state is defined by a repository theory,
# which also defines its requests and its loop state. A demanded state is exported by a generated
# request theory from the refinement layer, with the subject constant as its only root, and its
# request and loop state are computed natively in the verification theory. The theories named
# here are fixed bootstrap parameters of the transport, not choices about any answer.
STATES = {'development_seed': {'kind': 'development_seed', 'context': 'Native_Control_Seed_Subject',
                               'verdicts': 'Development_Seed_Verification'},
          'refinement_layer': {'kind': 'refinement_layer', 'context': 'Development_Request',
                               'layer': 'Native_Execution_Refinements', 'verdicts': 'Development_Successor'}}
# The theory that supplies the frame's fact: the code equations in effect for the subject.
FRAME_FACTS = 'Isabelle_Constant_Closure'
# The theory that reads an answer's declared parts in the frame's syntax before the answer's theory exists.
PARTS = 'Development_Answer_Parts'
FIELDS = {'request', 'definitions', 'equation', 'proof'}
QUALIFIED = re.compile(r'[A-Za-z][A-Za-z_0-9]*(\.[A-Za-z][A-Za-z_0-9]*)+')


def request_theory(state, subject):
    return ('theory Development_Request\n  imports ' + state['layer'] + ' Isabelle_Entity_Export ' + state['verdicts'] + '\nbegin\n\n'
            'local_setup \\<open>Isabelle_Entity_Export.define \\<^binding>\\<open>development_demanded\\<close>\n'
            '  [("_subject", [\\<^term>\\<open>' + subject + '\\<close>])]\\<close>\n\n'
            'declare development_demanded_context_def [code] development_demanded_roots_def [code]\n'
            '  development_demanded_subject_def [code]\n\n' + DEMANDED + 'end\n')


DEMANDED = (
    'definition development_demanded_state :: isabelle_rooted_context where\n'
    '  "development_demanded_state=(development_demanded_roots,development_demanded_context)"\n\n'
    'definition development_demanded_constants :: "nat list" where\n'
    '  "development_demanded_constants=List.map_filter isabelle_head_constant development_demanded_roots"\n\n'
    'definition development_demanded_unanswered :: "development_problem fset" where\n'
    '  "development_demanded_unanswered={||}"\n\n'
    'definition development_demanded_requests :: "development_problem fset \\<Rightarrow> development_request list" where\n'
    '  "development_demanded_requests answered=List.map_filter (development_refinement_request development_demanded_context\n'
    '    Development_Residual Development_Generated) development_demanded_constants"\n\n'
    'definition development_demanded_loop_state :: "development_problem fset \\<Rightarrow> development_loop" where\n'
    '  "development_demanded_loop_state answered=(development_demanded_state,\n'
    '    development_refinement_problems development_demanded_context Development_Residual Development_Generated\n'
    '      development_demanded_constants,\n'
    '    development_refinement_dependencies development_demanded_context Development_Residual Development_Generated\n'
    '      development_demanded_constants,answered,[])"\n\n')


def answer_name(answer):
    """The answer's theory name, derived from its canonical content alone."""
    canonical = json.dumps(answer, sort_keys=True, separators=(',', ':')).encode()
    return 'Development_Answer_' + hashlib.sha256(canonical).hexdigest()[:12]


def frame_imports(state, project=ROOT):
    """The frame of an answer: where it is adopted for the refinement layer, above the state otherwise."""
    if 'layer' not in state:
        return [state['context']]
    layer = project / 'theories' / (state['layer'] + '.thy')
    return [*investigate.theory_imports(layer.read_text(), state['layer']), FRAME_FACTS]


def answer_theory(state, answer, project=ROOT):
    subject = answer['request']['subject']
    return ('theory ' + answer_name(answer) + '\n  imports ' + ' '.join(frame_imports(state, project)) + '\nbegin\n\n'
            'local_setup \\<open>Isabelle_Constant_Closure.note_code_equations \\<^binding>\\<open>development_demanded_code\\<close>\n'
            '  ' + json.dumps(subject) + '\\<close>\n\n'
            + placed_parts(answer)[0] + '\n\n'
            'declare [[code drop: ' + subject + ']]\n\n'
            'lemma development_answer [code]:\n  "' + placed_parts(answer)[1] + '"\n'
            + placed_parts(answer)[2] + '\n\nend\n')


def placed_parts(answer):
    """The three parts exactly as the answer's theory places them."""
    return answer['definitions'].strip(), answer['equation'], answer['proof'].rstrip()


def parts_theory(state, answer, project=ROOT):
    """The theory that reads the answer's parts with the outer syntax of the answer's frame.

It imports exactly the frame's imports, so it reads with the keywords the answer's theory would be
read with, and it holds the parts only as ML strings: nothing in them is processed as theory text."""
    definitions, equation, proof = placed_parts(answer)
    return ('theory Development_Answer_Parts_Check\n  imports ' + ' '.join([*frame_imports(state, project), PARTS])
            + '\nbegin\n\nML \\<open>Development_Answer_Parts.check \\<^theory>\n  ('
            + investigate.ml_string(definitions) + ',\n   ' + investigate.ml_string(equation) + ',\n   '
            + investigate.ml_string(proof) + ')\\<close>\n\nend\n')


def adopted(answer, project=ROOT):
    """An answer whose theory is a theory of the project is part of its published state."""
    return (project / 'theories' / (answer_name(answer) + '.thy')).is_file()


def verification_theory(name, state, subject, theory=None):
    """The verdict of the answer framed in theory; without a theory, of the published state itself."""
    literal = "STR ''" + subject + "''"
    if theory is None:
        answer_state = ('definition development_answer_context :: isabelle_context where\n'
                        '  "development_answer_context=' + name + '_context"\n\n'
                        'definition development_answer_state :: isabelle_rooted_context where\n'
                        '  "development_answer_state=' + name + '_state"\n\n'
                        'definition development_answer_introduced_positions :: "nat list" where\n'
                        '  "development_answer_introduced_positions=[]"\n\n')
    else:
        answer_state = ('local_setup \\<open>Isabelle_Entity_Export.define_again \\<^binding>\\<open>development_answer\\<close>\n'
                        '  (@{thm ' + name + '_roots_def}, @{thm ' + name + '_context_def}) \\<^theory>\\<open>' + theory + '\\<close>\\<close>\n\n'
                        'declare development_answer_context_def [code] development_answer_roots_def [code]\n'
                        '  development_answer_introduced_def [code]\n\n'
                        'definition development_answer_state :: isabelle_rooted_context where\n'
                        '  "development_answer_state=(development_answer_roots,development_answer_context)"\n\n'
                        'definition development_answer_introduced_positions :: "nat list" where\n'
                        '  "development_answer_introduced_positions=List.map_filter isabelle_head_constant development_answer_introduced"\n\n')
    imports = [state['context'], *([theory] if theory else []), state['verdicts'], 'Development_Refinement_Repair',
               'Development_Admitted_Publication']
    return ('theory Development_Answer_Verification\n  imports ' + ' '.join(imports) + '\n'
            'begin\n\n' + answer_state +
            'definition development_answer_verdict :: "development_problem fset \\<Rightarrow>\n'
            '    (development_constant_verdict\\<times>development_refinement_repair) option" where\n'
            '  "development_answer_verdict answered=map_option (\\<lambda>r. (development_refinement_verdict ' + name + '_state r\n'
            '    development_answer_state,development_refinement_repair ' + name + '_state r development_answer_state\n'
            '      development_answer_introduced_positions))\n'
            '    (development_named_request ' + name + '_context (' + name + '_requests answered) ' + literal + ')"\n\n'
            'definition development_answer_successor :: "development_problem fset \\<Rightarrow>\n'
            '    (development_problem fset\\<times>development_generation list\\<times>development_problem list\\<times>bool list) option" where\n'
            '  "development_answer_successor answered=Option.bind (development_named_request ' + name + '_context\n'
            '    (' + name + '_requests answered) ' + literal + ') (\\<lambda>r. map_option (\\<lambda>(S2,ps,D,closed,history).\n'
            '      (closed,List.map_filter (\\<lambda>entry. case entry of Development_Answer_Record G \\<Rightarrow> Some G | _ \\<Rightarrow> None) history,\n'
            '       development_ready_problems D closed ps,map (development_request_current\n'
            '        (snd ' + name + '_state) (snd development_answer_state)) (' + name + '_requests answered)))\n'
            '      (development_successor (' + name + '_loop_state answered) r development_answer_state))"\n\n'
            'definition development_answer_verdict_value :: "development_problem fset \\<Rightarrow> finite_factor_term" where\n'
            '  "development_answer_verdict_value answered=finite_pair_presentation (finite_option_presentation\n'
            '    (finite_pair_presentation development_verdict_data development_refinement_repair_data))\n'
            '    (finite_option_presentation (finite_pair_presentation (finite_collection_presentation development_problem_data)\n'
            '      (finite_pair_presentation (finite_sequence_presentation development_generation_data)\n'
            '        (finite_pair_presentation development_problems_data (finite_sequence_presentation finite_boolean_data)))))\n'
            '    (development_answer_verdict answered,development_answer_successor answered)"\n\n'
            'definition development_answer_admitted_publication :: "development_problem fset \\<Rightarrow>\n'
            '    development_answer_publication option" where\n'
            '  "development_answer_admitted_publication answered=map_option (\\<lambda>r. development_admitted_publication\n'
            '    ' + name + '_state r development_answer_state development_answer_introduced_positions)\n'
            '    (development_named_request ' + name + '_context (' + name + '_requests answered) ' + literal + ')"\n\n'
            'definition development_answer_publication_value :: "development_problem fset \\<Rightarrow> finite_factor_term" where\n'
            '  "development_answer_publication_value answered=finite_option_presentation development_answer_publication_data\n'
            '    (development_answer_admitted_publication answered)"\n\n'
            'definition development_answer_names :: "nat list \\<Rightarrow> String.literal list" where\n'
            '  "development_answer_names=List.map_filter (isabelle_name_at (fst development_answer_context))"\n\n'
            'definition development_answer_summary :: "development_problem fset \\<Rightarrow>\n'
            '    (bool\\<times>nat list\\<times>String.literal list\\<times>String.literal list\\<times>bool\\<times>bool\\<times>nat\\<times>bool) option" where\n'
            '  "development_answer_summary answered=map_option (\\<lambda>(v,(e,ds,r,v2,a2)). (development_verdict_accepted v,\n'
            '    development_verdict_counts v@(case development_answer_successor answered of None \\<Rightarrow> []\n'
            '      | Some (closed,history,ready,current) \\<Rightarrow> [length history,length ready,length (filter id current)]),\n'
            '    development_answer_names (development_verdict_excess v),\n'
            '    development_answer_names development_answer_introduced_positions,\n'
            '    a2,development_extension_accepted e,length ds,case development_answer_admitted_publication answered of\n'
            '      None \\<Rightarrow> False | Some P \\<Rightarrow> development_answer_published P))\n'
            '    (development_answer_verdict answered)"\n\n'
            'export_code development_answer_verdict_value development_answer_publication_value development_answer_summary\n'
            '  ' + name + '_unanswered\n'
            '  finite_term_shared_word_fold integer_of_nat\n'
            '  in Eval module_name Development_Answer_Verification file_prefix "development_answer_verification"\n\n'
            'end\n')


def packet_theory(name, state, subject):
    """The theory whose export is the packet of the request the state presents for the subject."""
    imports = state['context'] + ' ' + state['verdicts'] + ' Development_Request_Packets'
    request = ('the (development_named_request ' + name + '_context (' + name + '_requests ' + name + '_unanswered) '
               "STR ''" + subject + "'')")
    return ('theory Development_Request_Packet\n  imports ' + imports + '\nbegin\n\n'
            'ML \\<open>\n'
            '  val text = Development_Request_Packets.packet \\<^context>\n'
            '    {state = ' + json.dumps(state['kind']) + ', subject = ' + json.dumps(subject) + ',\n'
            '     context = \\<^term>\\<open>' + name + '_context\\<close>, request = \\<^term>\\<open>' + request + '\\<close>}\n'
            '  val () = Development_Request_Packets.export_packet \\<^theory> "packet.json" text\n'
            '\\<close>\n\nend\n')


def summary_program(name):
    return lambda engine, _inputs: summary_text(engine, name)


def summary_text(engine, name):
    return ('use ' + investigate.ml_string(str(engine)) + ';\n'
            'structure N = Development_Answer_Verification;\n'
            'fun nat n = IntInf.toString (N.integer_of_nat n);\n'
            'fun words xs = "[" ^ String.concatWith "," (map (fn s => "\\"" ^ s ^ "\\"") xs) ^ "]";\n'
            'val () = case N.development_answer_summary N.' + name + '_unanswered of\n'
            '    NONE => print "SUMMARY null\\n"\n'
            '  | SOME (accepted, (counts, (excess, (introduced, (repaired, (extension, (definitions, published))))))) =>\n'
            '      print ("SUMMARY {\\"accepted\\":" ^ Bool.toString accepted ^ ",\\"counts\\":[" ^\n'
            '      String.concatWith "," (map nat counts) ^ "],\\"excess\\":" ^ words excess ^ ",\\"introduced\\":" ^\n'
            '      words introduced ^ ",\\"repaired\\":" ^ Bool.toString repaired ^ ",\\"extension\\":" ^\n'
            '      Bool.toString extension ^ ",\\"definition_problems\\":" ^ nat definitions ^\n'
            '      ",\\"published\\":" ^ Bool.toString published ^ "}\\n");\n')


def validate(answer):
    """Refuse an answer that is not exactly the declared presentation before anything is built."""
    assert isinstance(answer, dict) and set(answer) == FIELDS
    assert all(isinstance(answer[k], str) for k in FIELDS - {'request'})
    assert isinstance(answer['request'], dict) and set(answer['request']) == {'state', 'subject'}
    assert answer['request']['state'] in STATES and QUALIFIED.fullmatch(answer['request']['subject'])
    return answer


def run(name, command, log, timeout):
    started = time.monotonic()
    with log.open('w') as stream:
        try:
            code = build.run_session([str(c) for c in command], cwd=ROOT, env={**os.environ, **ENV_HOME},
                                     stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired:
            code = 'timeout'
    return {'name': name, 'exit_code': code, 'seconds': round(time.monotonic() - started, 2), 'log': str(log)}


REFUSAL = re.compile(r"The answer's (?:definitions|equation|proof) part is refused: [^\n]*")


def parts_refusal(*paths):
    """The reason Isabelle gave for refusing an answer's parts, read from the logs of the reading."""
    for path in paths:
        for log in ([path] if path.is_file() else sorted(path.rglob('*.log')) if path.is_dir() else []):
            found = REFUSAL.search(log.read_text(errors='replace'))
            if found:
                return found.group(0).rstrip()
    return None


def overlay(output, generated):
    """A project whose theories are the repository's and the generated ones, declared in its ROOT."""
    project = output / 'project'
    (project / 'theories').mkdir(parents=True)
    root = (ROOT / 'ROOT').read_text()
    (project / 'ROOT').write_text(root.rstrip('\n') + ''.join('\n    ' + name for name in generated) + '\n')
    sources = {source.stem: source for source in (ROOT / 'theories').glob('*.thy')}
    assert not set(generated) & set(sources), 'A generated theory would replace a repository theory.'
    for source in sources.values():
        (project / 'theories' / source.name).symlink_to(source)
    for name, text in generated.items():
        (project / 'theories' / (name + '.thy')).write_text(text)
    return project


def active_base(base):
    return (base or Path(json.loads(Path('/tmp/structural-active-context.json').read_text())['directory'])).resolve()


def packet_main(args):
    """Build the request theory and export the packet of the request it presents for the subject."""
    state = STATES[args.state]
    assert QUALIFIED.fullmatch(args.subject)
    name = 'development_demanded' if 'layer' in state else args.state
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh packet directory.'
    generated = {}
    if 'layer' in state:
        generated['Development_Request'] = request_theory(state, args.subject)
    generated['Development_Request_Packet'] = packet_theory(name, state, args.subject)
    project = overlay(output, generated)
    session = 'Development_Packet_' + hashlib.sha256((args.state + args.subject).encode()).hexdigest()[:12]
    record = {'status': 'failed', 'state': args.state, 'subject': args.subject, 'session': session}
    try:
        step = run('proof', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', active_base(args.base),
                             '--project', project, '--output', output / 'proof', '--session', session, '--without-heap',
                             '--threads', '16', '--timeout', args.timeout, 'Development_Request_Packet'],
                   output / 'proof.log', args.timeout + 60)
        record['steps'] = [step]
        assert step['exit_code'] == 0, 'The request theory was not accepted.'
        command = json.loads((output / 'proof' / 'result.json').read_text())['command']
        export = ['isabelle', 'export', '-n']
        for i, item in enumerate(command[:-1]):
            if item == '-d':
                export += ['-d', command[i + 1]]
        export += ['-d', str(output / 'proof'), '-x', '*:request/packet.json', '-O', str(output / 'export'), session]
        record['steps'].append(run('export', export, output / 'export.log', 120))
        paths = list((output / 'export').rglob('packet.json'))
        assert len(paths) == 1, 'Expected one exported packet.'
        packet = json.loads(paths[0].read_text())
        (output / 'packet.json').write_text(json.dumps(packet, indent=1) + '\n')
        record.update(status='presented', packet=str(output / 'packet.json'))
    except (AssertionError, OSError, ValueError, KeyError) as error:
        record['error'] = str(error)
    finally:
        for suffix in ('.db', '.gz'):
            (HEAPS / 'log' / (session + suffix)).unlink(missing_ok=True)
        leftover = HEAPS / 'log' / session
        if leftover.is_dir():
            shutil.rmtree(leftover)
        else:
            leftover.unlink(missing_ok=True)
    write_json(output / 'packet-record.json', record)
    print(json.dumps({k: record[k] for k in ('status', 'packet', 'error') if k in record}))
    return 0 if record['status'] == 'presented' else 1


def main():
    if not __debug__:
        raise ValueError('Answer checks require Python assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    judged = commands.add_parser('answer', help='Judge an answer.')
    judged.add_argument('--answer', type=Path, required=True)
    judged.add_argument('--retain', type=Path, help='Write the retained record of a judged answer here.')
    presented = commands.add_parser('packet', help='Present the packet of a request.')
    presented.add_argument('--state', required=True, choices=sorted(STATES))
    presented.add_argument('--subject', required=True)
    for command in (judged, presented):
        command.add_argument('--output', type=Path, required=True)
        command.add_argument('--base', type=Path, help='Accepted context with a stored heap; defaults to the active one.')
        command.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    if args.command == 'packet':
        return packet_main(args)
    raw = args.answer.read_bytes()
    answer = validate(json.loads(raw))
    state = STATES[answer['request']['state']]
    digest = hashlib.sha256(raw).hexdigest()
    base = active_base(args.base)
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh answer directory.'
    name = 'development_demanded' if 'layer' in state else answer['request']['state']
    generated = {}
    if 'layer' in state:
        generated['Development_Request'] = request_theory(state, answer['request']['subject'])
    theory = None if adopted(answer) else answer_name(answer)
    if theory is not None:
        generated[theory] = answer_theory(state, answer)
    generated['Development_Answer_Verification'] = verification_theory(name, state, answer['request']['subject'], theory)
    project = overlay(output, generated)
    session = 'Development_Judgment_' + digest[:12]
    parts_session = 'Development_Parts_' + digest[:12]
    steps = []
    record = {'status': 'failed', 'answer': str(args.answer.resolve()), 'answer_sha256': digest,
              'request': answer['request'], 'base': str(base), 'session': session, 'steps': steps,
              'theory': answer_name(answer), 'adopted': theory is None}
    try:
        if theory is not None:
            parts = overlay(output / 'parts', {'Development_Answer_Parts_Check': parts_theory(state, answer)})
            steps.append(run('parts', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', base,
                                       '--project', parts, '--output', output / 'parts' / 'proof', '--session',
                                       parts_session, '--without-heap', '--threads', '4', '--timeout', args.timeout,
                                       'Development_Answer_Parts_Check'], output / 'parts.log', args.timeout + 60))
            if steps[-1]['exit_code'] != 0:
                reason = parts_refusal(output / 'parts.log', output / 'parts')
                assert reason is not None, "The answer's parts could not be read."
                record.update(status='refused', refusal=reason, accepted=False)
        if record['status'] != 'refused':
            steps.append(run('proof', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', base,
                                       '--project', project, '--output', output / 'proof', '--session', session,
                                       '--without-heap', '--threads', '16', '--timeout', args.timeout,
                                       'Development_Answer_Verification'], output / 'proof.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The answer or its verification theory was not accepted.'
            steps.append(run('export', [sys.executable, '-B', TOOLS / 'export_proved_code.py', '--proof',
                                        output / 'proof' / 'result.json', '--project', project, '--output', output / 'export',
                                        '--module', 'Development_Answer_Verification:development_answer_verification.ML'],
                             output / 'export.log', 300))
            assert steps[-1]['exit_code'] == 0, 'Export failed.'
            proof = output / 'export' / 'development_answer_verification.proof.json'
            steps.append(run('verdict', [sys.executable, '-B', TOOLS / 'check_presented_report.py', '--proof', proof,
                                         '--poly', POLY, '--project', project, '--theory', 'Development_Answer_Verification',
                                         '--module', 'Development_Answer_Verification', '--report',
                                         'development_answer_verdict_value', '--scope', name + '_unanswered',
                                         '--workers', '4', '--timeout', args.timeout, '--output', output / 'verdict'],
                             output / 'verdict.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The verdict presentation failed.'
            steps.append(run('publication', [sys.executable, '-B', TOOLS / 'check_presented_report.py', '--proof', proof,
                                             '--poly', POLY, '--project', project, '--theory', 'Development_Answer_Verification',
                                             '--module', 'Development_Answer_Verification', '--report',
                                             'development_answer_publication_value', '--scope', name + '_unanswered',
                                             '--workers', '4', '--timeout', args.timeout, '--output', output / 'publication'],
                             output / 'publication.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The publication presentation failed.'
            receipt = proved_code.checked_execution(
                proof, POLY, output / 'summary', required_theories=['Development_Answer_Verification'], inputs={},
                input_paths=[], program=summary_program(name), assess=lambda _i, text: text,
                question='Which reasons does the native verdict of this answer retain?',
                boundary='A diagnostic reading of the exported verdict; the presented word is the evidence.',
                timeout=args.timeout, project=project)
            assert receipt['status'] == 'accepted', receipt.get('error')
            lines = [line for line in receipt['assessment'].splitlines() if line.startswith('SUMMARY ')]
            assert len(lines) == 1, 'Expected one verdict summary.'
            summary = json.loads(lines[0][len('SUMMARY '):])
            word = json.loads((output / 'verdict' / 'receipt.json').read_text())['word']
            publication = json.loads((output / 'publication' / 'receipt.json').read_text())['word']
            record.update(status='judged', verdict_word=word, publication_word=publication, summary=summary,
                          accepted=bool(summary and summary['accepted']))
    except (AssertionError, OSError, ValueError, KeyError) as error:
        record['error'] = str(error)
    finally:
        for name_of_session in (session, parts_session):
            for suffix in ('.db', '.gz'):
                (HEAPS / 'log' / (name_of_session + suffix)).unlink(missing_ok=True)
            leftover = HEAPS / 'log' / name_of_session
            if leftover.is_dir():
                shutil.rmtree(leftover)
            else:
                leftover.unlink(missing_ok=True)
    write_json(output / 'answer.json', record)
    if args.retain is not None and record['status'] in ('judged', 'refused'):
        write_json(args.retain, retained_record(answer, digest, base, record))
    print(json.dumps({k: record[k] for k in ('status', 'accepted', 'summary', 'verdict_word', 'publication_word',
                                              'refusal', 'error') if k in record}))
    return 0 if record['status'] in ('judged', 'refused') else 1


def retained_record(answer, digest, base, record):
    """The retained boundary of a judgment: the answer, the harness and base it was judged with, the outcome."""
    receipt = base / 'accepted-context.json'
    return {'answer': answer, 'answer_sha256': digest, 'harness_sha256': investigate.file_hash(Path(__file__)),
            'base_receipt_sha256': investigate.file_hash(receipt) if receipt.is_file() else None,
            'status': record['status'], 'steps': {step['name']: step['exit_code'] for step in record['steps']},
            **({'summary': record['summary'], 'verdict_word': record['verdict_word'],
                'publication_word': record['publication_word']} if record['status'] == 'judged'
               else {'refusal': record['refusal']})}


if __name__ == '__main__':
    raise SystemExit(main())
