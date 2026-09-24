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
is a transport choice, not a correspondence.

Whether an answer is adopted is decided by its evidence (`adoption_evidence`), never by a file name: the
request's state adopts through its boundary, a retained receipt binds the answer's digest, the installed
theory has the digest that receipt retained, and ROOT declares it and the boundary imports it. The harness
decides its case before any Isabelle run. With no theory of the answer's name in the workspace, the answer
is framed and judged. With one, the harness judges nothing: it reports `adopted` with the evidence when
every connection holds, and `obstructed` with the connections that failed otherwise; the published state is
never judged against itself, and the connection no workspace content establishes (the published state is the
answer state the judgment produced) is reported as `unverified`.

Before an answer is framed, Isabelle reads its declared parts with the outer syntax of the frame
(Development_Answer_Parts), in a theory of the answer's own that imports exactly the frame's imports and
Development_Answer_Parts and holds the parts only as ML strings. That theory is read alone, or beside other
answers' theories in one session (`read_parts`, `--parts`), each theory writing its own outcome, so no
answer's reading sees another's parts. An answer whose parts hold anything but definitional commands,
theorem statements and their proofs, document text, one proposition and one proof is refused with
Isabelle's reason, and its theory is never processed.

An answer whose parts are accepted is proved in a session of its own, or beside other answers in one
session (`prove_answers`, `--proof`): each answer's theory imports exactly its frame, and its verification
theory, named by the answer's content, imports the request state and that theory alone, so no answer's
theories import another's. A shared session's outcome is one, so a shared proof is given to an answer only
when the whole session was accepted; the export, the verdict, the publication and the summary are each
answer's own, read from its own verification theory. A parts reading that leaves neither an acceptance nor
a refusal is no judgment: the harness says so (`judgment: false`).
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
import isabelle_places
import proved_code
from evidence_io import write_json

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
POLY = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
HEAPS = isabelle_places.USER_HOME / '.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux'
ENV_HOME = {'USER_HOME': str(isabelle_places.USER_HOME), 'PYTHONDONTWRITEBYTECODE': '1'}

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
# The retained adoption receipts, found by the digest of the answer they bind.
ADOPTIONS = Path('validation') / 'development-adoptions'
# The connection of an adoption that nothing the workspace holds establishes.
UNVERIFIED = ('The published state is the answer state this answer\'s judgment produced: its incumbent for the '
              'subject is the answer\'s statement and nothing else it reads has changed since but by later adoptions '
              'and refinements. Its native record, the answer\'s generation selected at the problem\'s locus in a '
              'persistent native published state, does not exist for the refinement layer.')
FIELDS = {'request', 'definitions', 'equation', 'proof'}
# The ML structure every verification theory exports; each answer's theory of it has a name of its own.
VERIFICATION_MODULE = 'Development_Answer_Verification'
UNREAD = "The answer's parts could not be read."
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


def answer_digest(answer):
    """The SHA-256 of the answer's canonical content, which its theory name abbreviates."""
    return hashlib.sha256(json.dumps(answer, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def answer_name(answer):
    """The answer's theory name, derived from its canonical content alone."""
    return 'Development_Answer_' + answer_digest(answer)[:12]


def adoption_receipts(project=ROOT):
    """Every retained adoption receipt of the project, by its file name."""
    return {path.name: json.loads(path.read_text()) for path in sorted((project / ADOPTIONS).glob('*.json'))}


def adoption_evidence(answer, project=ROOT, receipt=None):
    """Each connection of the answer's adoption, checked on the project's own content.

    The connections: the request's state adopts through its boundary; exactly one retained receipt, found by
    the answer's digest (or the supplied one), binds it as adopted, not a control and not withdrawn; the
    theory the receipt names at installation has the digest it retained there; ROOT declares the answer's theory
    once and the boundary imports it.
    `present` is whether a theory of the answer's name stands at all; `obstruction` lists the connections
    that failed; `unverified` is the residual no workspace content establishes."""
    state = STATES[answer['request']['state']]
    name, digest = answer_name(answer), answer_digest(answer)
    theory = project / 'theories' / (name + '.thy')
    candidates = {'supplied': receipt} if receipt is not None else {
        file: found for file, found in adoption_receipts(project).items() if found.get('answer_digest') == digest}
    bound = sorted(file for file, found in candidates.items()
                   if found.get('answer_digest') == digest and found.get('status') == 'adopted'
                   and found.get('control') is False and 'withdrawn' not in found)
    installation = candidates[bound[0]].get('steps', {}).get('installation', {}) if len(bound) == 1 else {}
    retained = installation.get('theory_sha256')
    named = installation.get('theory') or 'theories/' + name + '.thy'
    present = hashlib.sha256((project / named).read_bytes()).hexdigest() if (project / named).is_file() else None
    boundary = state.get('layer')
    root = (project / 'ROOT').read_text().split() if (project / 'ROOT').is_file() else []
    layer = project / 'theories' / ((boundary or '') + '.thy')
    imports = investigate.theory_imports(layer.read_text(), boundary) if boundary and layer.is_file() else []
    connections = {
        'state': {'state': answer['request']['state'], 'boundary': boundary, 'holds': boundary is not None},
        'receipt': {'answer_digest': digest, 'found': sorted(candidates), 'bound': bound, 'holds': len(bound) == 1},
        'installed': {'theory': named, 'retained_sha256': retained, 'present_sha256': present,
                      'holds': present is not None and present == retained},
        'declared': {'declarations': root.count(name), 'holds': root.count(name) == 1},
        'imported': {'boundary': boundary, 'holds': name in imports}}
    obstruction = [key for key, connection in connections.items() if not connection['holds']]
    return {'theory': name, 'answer_digest': digest, 'present': theory.is_file(), 'connections': connections,
            'holds': not obstruction, 'obstruction': obstruction, 'unverified': UNVERIFIED}


def adoption_report(answer, evidence, base):
    """The harness's report where a theory of the answer's name stands: no judgment, only the evidence."""
    return {'status': 'adopted' if evidence['holds'] else 'obstructed', 'answer_digest': evidence['answer_digest'],
            'request': answer['request'], 'base': str(base), 'theory': evidence['theory'], 'evidence': evidence,
            'unverified': evidence['unverified'],
            **({} if evidence['holds'] else {'obstruction': evidence['obstruction']})}


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


def parts_name(answer):
    """The theory that reads one answer's parts: one of its own per answer, named by its content."""
    return 'Development_Answer_Parts_Check_' + answer_digest(answer)[:16]


def parts_theory(state, answer, outcome, project=ROOT):
    """The theory that reads the answer's parts with the outer syntax of the answer's frame.

It imports exactly the frame's imports, so it reads with the keywords the answer's theory would be
read with, and it holds the parts only as ML strings: nothing in them is processed as theory text.
The reading writes its outcome to `outcome` (`accepted`, or `refused` and the reason Isabelle gave),
so that several answers' theories can be read in one session, each in its own theory, and a refusal
of one leaves every other's reading as it would be alone."""
    definitions, equation, proof = placed_parts(answer)
    return ('theory ' + parts_name(answer) + '\n  imports ' + ' '.join([*frame_imports(state, project), PARTS])
            + '\nbegin\n\nML \\<open>File.write (Path.explode ' + investigate.ml_string(str(outcome)) + ')\n'
            '  ((Development_Answer_Parts.check \\<^theory>\n  ('
            + investigate.ml_string(definitions) + ',\n   ' + investigate.ml_string(equation) + ',\n   '
            + investigate.ml_string(proof) + '); "accepted\\n")\n'
            '    handle ERROR message => "refused\\n" ^ message)\\<close>\n\nend\n')


def parts_outcome(outcome):
    """One answer's reading from the outcome its theory wrote: the step's exit code and the refusal.

An answer is accepted only when its theory wrote `accepted`. A theory that wrote nothing (its session
never ran it, or it failed otherwise than by a refusal) leaves no reason, as a failed reading did."""
    text = outcome.read_text() if outcome.is_file() else ''
    return (0, None) if text == 'accepted\n' else (1, parts_refusal(outcome) if text.startswith('refused\n') else None)


def remove_session_logs(session):
    for suffix in ('.db', '.gz'):
        (HEAPS / 'log' / (session + suffix)).unlink(missing_ok=True)
    leftover = HEAPS / 'log' / session
    if leftover.is_dir():
        shutil.rmtree(leftover)
    else:
        leftover.unlink(missing_ok=True)


def read_parts(answers, base, output, timeout):
    """Read the declared parts of every answer in one Isabelle session, each in a theory of its own.

Each answer's theory imports exactly its own frame and holds only its own parts, so its reading uses its
frame's keyword table and nothing another answer's parts hold is visible to it; the theories share the
session and nothing else. The readings are keyed by the answers' digests, each with the base it was read
on, so that a harness judging one of these answers takes its own reading and no other."""
    distinct = {answer_digest(answer): answer for answer in answers}
    outcomes = output / 'outcomes'
    outcomes.mkdir(parents=True)
    generated = {parts_name(answer): parts_theory(STATES[answer['request']['state']], answer, outcomes / (digest + '.txt'))
                 for digest, answer in distinct.items()}
    project = overlay(output, generated)
    session = 'Development_Parts_' + hashlib.sha256(''.join(sorted(distinct)).encode()).hexdigest()[:12]
    try:
        step = run('parts', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', base,
                             '--project', project, '--output', output / 'proof', '--session', session,
                             '--without-heap', '--threads', '4', '--timeout', timeout, *sorted(generated)],
                   output / 'parts.log', timeout + 60)
    finally:
        remove_session_logs(session)
    readings = {}
    for digest in distinct:
        code, refusal = parts_outcome(outcomes / (digest + '.txt'))
        readings[digest] = {'answer_digest': digest, 'base': str(base), 'exit_code': code, 'refusal': refusal,
                            'seconds': step['seconds'], 'answers_read': len(distinct), 'log': step['log']}
    return readings


def verification_name(answer):
    """The theory that judges one answer: one of its own per answer, named by its content, so that several
answers' verification theories can be proved in one session, none importing another."""
    return VERIFICATION_MODULE + '_' + answer_digest(answer)[:16]


def generated_theories(answer, project=ROOT):
    """The theories the harness frames for an answer: a layer state's request theory, the answer's theory and
its verification theory."""
    state = STATES[answer['request']['state']]
    subject = answer['request']['subject']
    name = 'development_demanded' if 'layer' in state else answer['request']['state']
    generated = {}
    if 'layer' in state:
        generated['Development_Request'] = request_theory(state, subject)
    theory = answer_name(answer)
    generated[theory] = answer_theory(state, answer, project)
    generated[verification_name(answer)] = verification_theory(name, state, subject, theory, verification_name(answer))
    return generated


def prove_answers(answers, base, output, timeout):
    """Prove the theories of several answers in one Isabelle session, each answer's verification theory its own.

No answer's theories import another's: they share the session and nothing else. Answers whose frames generate
different request theories cannot share one (a layer's request theory is `Development_Request` and holds its
subject), and are refused here. The session's outcome is one, accepted only when every theory was; each
reading carries it, and a caller gives a reading to an answer only when it is accepted. The session's logs
are kept for the exports read from it until `remove_session_logs(reading['session'])`, and removed at once
when it is not accepted."""
    distinct = {answer_digest(answer): answer for answer in answers}
    generated = {}
    for answer in distinct.values():
        for theory, text in generated_theories(answer).items():
            assert generated.setdefault(theory, text) == text, \
                'Answers whose frames generate different request theories cannot share a session.'
    project = overlay(output, generated)
    session = 'Development_Proofs_' + hashlib.sha256(''.join(sorted(distinct)).encode()).hexdigest()[:12]
    try:
        step = run('proof', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', base,
                             '--project', project, '--output', output / 'proof', '--session', session,
                             '--without-heap', '--threads', '16', '--timeout', timeout,
                             *sorted(verification_name(answer) for answer in distinct.values())],
                   output / 'proof.log', timeout + 60)
    except BaseException:
        remove_session_logs(session)
        raise
    if step['exit_code'] != 0:
        remove_session_logs(session)
    return {digest: {'answer_digest': digest, 'base': str(base), 'exit_code': step['exit_code'],
                     'seconds': step['seconds'], 'answers_read': len(distinct), 'log': step['log'], 'session': session,
                     'project': str(project), 'proof': str(output / 'proof' / 'result.json')} for digest in distinct}


def verification_theory(name, state, subject, theory, verification=VERIFICATION_MODULE):
    """The verdict of the answer framed in theory, against the request state."""
    literal = "STR ''" + subject + "''"
    answer_state = ('local_setup \\<open>Isabelle_Entity_Export.define_again \\<^binding>\\<open>development_answer\\<close>\n'
                        '  (@{thm ' + name + '_roots_def}, @{thm ' + name + '_context_def}) \\<^theory>\\<open>' + theory + '\\<close>\\<close>\n\n'
                        'declare development_answer_context_def [code] development_answer_roots_def [code]\n'
                        '  development_answer_introduced_def [code]\n\n'
                        'definition development_answer_state :: isabelle_rooted_context where\n'
                        '  "development_answer_state=(development_answer_roots,development_answer_context)"\n\n'
                        'definition development_answer_introduced_positions :: "nat list" where\n'
                        '  "development_answer_introduced_positions=List.map_filter isabelle_head_constant development_answer_introduced"\n\n')
    imports = [state['context'], theory, state['verdicts'], 'Development_Refinement_Repair',
               'Development_Admitted_Publication', 'Development_Loop_Presentations', 'Development_State_Presenter']
    return ('theory ' + verification + '\n  imports ' + ' '.join(imports) + '\n'
            'begin\n\n' + answer_state +
            'abbreviation development_answer_inert :: "isabelle_term \\<Rightarrow> finite_factor_term" where\n'
            '  "development_answer_inert \\<equiv> development_local_term_data (fst (snd ' + name + '_state))"\n\n'
            'definition development_answer_verdict :: "development_problem fset \\<Rightarrow>\n'
            '    (development_request\\<times>development_constant_verdict\\<times>development_refinement_repair) option" where\n'
            '  "development_answer_verdict answered=map_option (\\<lambda>r. (r,development_refinement_verdict ' + name + '_state r\n'
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
            '  "development_answer_verdict_value answered=finite_store_option id (finite_partial_pair\n'
            '    (finite_partial_option (\\<lambda>(r,v,R). finite_partial_pair (Some \\<circ> development_verdict_data)\n'
            '      (development_refinement_repair_data state_constant_key (development_local_term_data\n'
            '        (fst (snd (development_repair_state ' + name + '_state r development_answer_state\n'
            '          development_answer_introduced_positions)))) (\\<lambda>_. None) (\\<lambda>_. None) r) (v,R)))\n'
            '    (finite_partial_option (finite_partial_pair\n'
            '      (development_problems_table state_constant_key development_answer_inert (\\<lambda>_. None) (\\<lambda>_. None))\n'
            '      (finite_partial_pair (finite_partial_sequence\n'
            '          (development_generation_data state_constant_key development_answer_inert (\\<lambda>_. None) (\\<lambda>_. None)))\n'
            '        (finite_partial_pair\n'
            '          (development_problems_data state_constant_key development_answer_inert (\\<lambda>_. None) (\\<lambda>_. None))\n'
            '          (Some \\<circ> finite_sequence_presentation finite_boolean_data)))))\n'
            '    (development_answer_verdict answered,development_answer_successor answered))"\n\n'
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
            '  "development_answer_summary answered=map_option (\\<lambda>(r0,v,(e,ds,r,v2,a2)). (development_verdict_accepted v,\n'
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
            '  in Eval module_name ' + VERIFICATION_MODULE + ' file_prefix "development_answer_verification"\n\n'
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
    return (base or Path(json.loads(isabelle_places.ACTIVE_CONTEXT.read_text())['directory'])).resolve()


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
        remove_session_logs(session)
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
    judged.add_argument('--parts', type=Path, help='The reading of this answer\'s parts made by `read_parts` in a '
                        'session shared with other answers; without it the harness reads them in a session of its own.')
    judged.add_argument('--proof', type=Path, help='The accepted proof of this answer\'s theories made by `prove_answers` '
                        'in a session shared with other answers; without it the harness proves them in a session of its own.')
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
    output.mkdir(parents=True)
    evidence = adoption_evidence(answer)
    if evidence['present']:
        record = adoption_report(answer, evidence, base)
        write_json(output / 'answer.json', record)
        print(json.dumps({k: record[k] for k in ('status', 'obstruction') if k in record}))
        return 0 if record['status'] == 'adopted' else 1
    generated = generated_theories(answer)
    theory, verification = answer_name(answer), verification_name(answer)
    session = 'Development_Judgment_' + digest[:12]
    steps = []
    record = {'status': 'failed', 'answer': str(args.answer.resolve()), 'answer_sha256': digest,
              'request': answer['request'], 'base': str(base), 'session': session, 'steps': steps,
              'theory': theory, 'verification': verification}
    try:
        if args.parts is not None:
            reading = json.loads(args.parts.read_text())
            assert reading['answer_digest'] == answer_digest(answer) and reading['base'] == str(base), \
                "The supplied reading is not of this answer's parts on this base."
        else:
            reading = read_parts([answer], base, output / 'parts', args.timeout)[answer_digest(answer)]
        steps.append({'name': 'parts', **{k: reading[k] for k in ('exit_code', 'seconds', 'answers_read', 'log')}})
        if steps[-1]['exit_code'] != 0:
            reason = reading['refusal']
            if reason is None:
                record['judgment'] = False
            assert reason is not None, UNREAD
            record.update(status='refused', refusal=reason, accepted=False)
        if record['status'] != 'refused':
            if args.proof is not None:
                shared = json.loads(args.proof.read_text())
                assert shared['answer_digest'] == answer_digest(answer) and shared['base'] == str(base) \
                    and shared['exit_code'] == 0, 'The supplied proof is not an accepted proof of this answer on this base.'
                project, proof_result = Path(shared['project']), Path(shared['proof'])
                assert all((project / 'theories' / (generated_name + '.thy')).read_text() == text
                           for generated_name, text in generated.items()), \
                    "The supplied proof's project does not hold this answer's theories."
                steps.append({'name': 'proof', **{k: shared[k] for k in ('exit_code', 'seconds', 'answers_read', 'log')}})
            else:
                project, proof_result = overlay(output, generated), output / 'proof' / 'result.json'
                steps.append(run('proof', [sys.executable, '-B', TOOLS / 'prove_context.py', '--parent-project', base,
                                           '--project', project, '--output', output / 'proof', '--session', session,
                                           '--without-heap', '--threads', '16', '--timeout', args.timeout,
                                           verification], output / 'proof.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The answer or its verification theory was not accepted.'
            record['frame_sha256'] = hashlib.sha256(generated[theory].encode()).hexdigest()
            steps.append(run('export', [sys.executable, '-B', TOOLS / 'export_proved_code.py', '--proof',
                                        proof_result, '--project', project, '--output', output / 'export',
                                        '--module', verification + ':development_answer_verification.ML'],
                             output / 'export.log', 300))
            assert steps[-1]['exit_code'] == 0, 'Export failed.'
            proof = output / 'export' / 'development_answer_verification.proof.json'
            steps.append(run('verdict', [sys.executable, '-B', TOOLS / 'check_presented_report.py', '--proof', proof,
                                         '--poly', POLY, '--project', project, '--theory', verification,
                                         '--module', VERIFICATION_MODULE, '--report',
                                         'development_answer_verdict_value', '--scope', name + '_unanswered',
                                         '--workers', '4', '--timeout', args.timeout, '--output', output / 'verdict'],
                             output / 'verdict.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The verdict presentation failed.'
            steps.append(run('publication', [sys.executable, '-B', TOOLS / 'check_presented_report.py', '--proof', proof,
                                             '--poly', POLY, '--project', project, '--theory', verification,
                                             '--module', VERIFICATION_MODULE, '--report',
                                             'development_answer_publication_value', '--scope', name + '_unanswered',
                                             '--workers', '4', '--timeout', args.timeout, '--output', output / 'publication'],
                             output / 'publication.log', args.timeout + 60))
            assert steps[-1]['exit_code'] == 0, 'The publication presentation failed.'
            receipt = proved_code.checked_execution(
                proof, POLY, output / 'summary', required_theories=[verification], inputs={},
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
        remove_session_logs(session)
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
