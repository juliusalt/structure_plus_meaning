"""Execute proved requirement construction and retain every native result field."""
from pathlib import Path
import argparse
import json

import investigate
import machine_reports
import proved_code
import check_reasoning


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Requirement_Plans;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += r'''
val n = N.nat_of_integer;
val emptyTerm = N.Finite_Target (N.Finite_Whole N.finite_empty_artifact);
fun jtarget t = if N.finite_reasoning_term_equal (N.Finite_Target t) emptyTerm
  then "{\"empty_artifact\":true}" else raise Fail "Undeclared literal target in execution fixture";
'''
    code += check_reasoning.TERM_JSON_PRELUDE
    code += r'''
fun jgoal (N.Existing_Admission d) = "[\"existing\"," ^ jnat d ^ "]"
  | jgoal (N.Paired_Admission (g,h)) = "[\"pair\"," ^ jgoal g ^ "," ^ jgoal h ^ "]"
  | jgoal (N.Collected_Admission g) = "[\"list\"," ^ jgoal g ^ "]";
fun jinstruction (N.Pair_Admission_Instruction (d,a,b)) =
    "[\"pair\"," ^ jnat d ^ "," ^ jnat a ^ "," ^ jnat b ^ "]"
  | jinstruction (N.List_Admission_Instruction (d,a)) =
    "[\"list\"," ^ jnat d ^ "," ^ jnat a ^ "]";
fun jsequence (ds,(next,cs)) = "{\"entries\":" ^ jlist jnat ds ^
    ",\"next\":" ^ jnat next ^ ",\"instructions\":" ^ jlist jinstruction cs ^ "}";
fun jexecution NONE = "null"
  | jexecution (SOME (plan,accepted)) = "{\"plan\":" ^ jsequence plan ^
    ",\"holds\":" ^ Bool.toString accepted ^ "}";
fun jchecked NONE = "null" | jchecked (SOME plan) = jsequence plan;
fun jrow (k,v) = "[" ^ jterm k ^ "," ^ jterm v ^ "]";
fun enumerate f xs = List.app f (ListPair.zip (List.tabulate (length xs, fn i => i),xs));
fun emitPlan (i,(gs,(start,result))) = print ("REQUIREMENT_PLAN " ^ Int.toString i ^
  " {\"goals\":" ^ jlist jgoal gs ^ ",\"start\":" ^ jnat start ^
  ",\"result\":" ^ jsequence result ^ "}\n");
fun emitTable start (i,(xs,(ys,(observations,(original,execution))))) =
  print ("REQUIREMENT_TABLE " ^ jnat start ^ " " ^ Int.toString i ^
  " {\"left\":" ^ jlist jrow xs ^ ",\"right\":" ^ jlist jrow ys ^
  ",\"observations\":" ^ jlist Bool.toString observations ^
  ",\"table_identity\":" ^ Bool.toString original ^
  ",\"execution\":" ^ jexecution execution ^ "}\n");
val () = enumerate emitPlan N.admission_sequence_reports;
fun emitRequest (i,(gs,(start,(candidate,(supported,(allocated,(accepted,result))))))) =
  print ("CHECKED_REQUIREMENT " ^ Int.toString i ^
  " {\"goals\":" ^ jlist jgoal gs ^ ",\"start\":" ^ jnat start ^
  ",\"candidate\":" ^ jsequence candidate ^ ",\"supported\":" ^ Bool.toString supported ^
  ",\"allocated\":" ^ Bool.toString allocated ^ ",\"admitted\":" ^ Bool.toString accepted ^
  ",\"result\":" ^ jchecked result ^ "}\n");
val () = print ("REQUIREMENT_SOURCE {\"definitions\":" ^ jlist jnat N.checked_requirement_source ^ "}\n");
val () = enumerate emitRequest N.checked_requirement_reports;
fun jedge (r,(p,x)) = "[" ^ jlist jnat r ^ "," ^ jlist jnat p ^ "," ^ jlist jnat x ^ "]";
fun jbinding (a,v) = "[" ^ jlist jnat a ^ "," ^ jlist jnat v ^ "]";
fun jartifact (atoms,(edges,(counts,bindings))) =
  "{\"carrier\":" ^ jlist (jlist jnat) atoms ^ ",\"incidence\":" ^ jlist jedge edges ^
  ",\"counted_data\":" ^ jlist jbinding counts ^ ",\"functional_data\":" ^ jlist jbinding bindings ^ "}";
fun emitArtifact (i,(gs,(start,(artifact,(formed,(expected,accepted)))))) =
  print ("REQUIREMENT_ARTIFACT " ^ Int.toString i ^
  " {\"goals\":" ^ jlist jgoal gs ^ ",\"start\":" ^ jnat start ^
  ",\"artifact\":" ^ jartifact artifact ^ ",\"formed\":" ^ Bool.toString formed ^
  ",\"expected\":" ^ jchecked expected ^ ",\"admitted\":" ^ Bool.toString accepted ^ "}\n");
val () = enumerate emitArtifact N.requirement_artifact_reports;
'''
    code += 'val () = List.app (fn start => enumerate (emitTable start) (N.portable_requirement_reports start)) '
    code += investigate.ml_list(inputs['counters'], investigate.ml_nat) + ';\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    inputs = {'counters': [353, 354, 360, 1000]}

    def assess(case_inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        records = list(machine_reports.reports(path))
        plans = [r for r in records if r['tag'] == 'REQUIREMENT_PLAN']
        tables = [r for r in records if r['tag'] == 'REQUIREMENT_TABLE']
        sources = [r for r in records if r['tag'] == 'REQUIREMENT_SOURCE']
        requests = [r for r in records if r['tag'] == 'CHECKED_REQUIREMENT']
        artifacts = [r for r in records if r['tag'] == 'REQUIREMENT_ARTIFACT']
        assert len(records) == len(plans) + len(tables) + len(sources) + len(requests) + len(artifacts)
        assert len(sources) == 1 and sources[0]['indices'] == []
        assert [r['indices'] for r in artifacts] == [[i] for i in range(17)]
        assert [r['indices'] for r in requests] == [[i] for i in range(14)]
        assert [r['indices'] for r in plans] == [[i] for i in range(7)]
        assert [r['indices'] for r in tables] == [
            [counter, i] for counter in case_inputs['counters'] for i in range(9)]
        return {
            'complete_reports': records,
            'reproduction_boundary': machine_reports.boundary(path),
            'boundary': (
                'All inputs, complete artifact fields, generated plans, condition observations, and judgments are '
                'serialized from the proved module. Their semantic equations are the '
                'Isabelle-established native contracts. This reader checks report coverage '
                'and retains the complete results; it does not assign facet satisfaction '
                'or select a development action.'),
        }

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output,
        required_theories=['Requirement_Artifact_Execution'], inputs=inputs,
        input_paths=[Path(__file__)], program=program, assess=assess,
        question='What plans and actual-subject judgments do the requirement constructors produce on the complete declared controls?',
        boundary='The finite execution supplements the universal native planning and installation contracts; whole development-protocol admission remains separate.',
        timeout=60, project=args.project.resolve())
    print(json.dumps({
        'status': receipt['status'], 'error': receipt.get('error'),
        'reports': receipt.get('assessment', {}).get('reproduction_boundary'),
    }))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
