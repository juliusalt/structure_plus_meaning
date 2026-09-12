"""Construct complete source terms and application targets with the accepted native module."""
from pathlib import Path
import argparse, json, sys
import nonempty_source_case as family

WORKTREE, review = family.ROOT, family.review
sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
import investigate, proved_code, check_application_comparison as construction
import check_keyed_tables as tables

import check_finite_inference as recovery
RECOVERY = Path(recovery.__file__).resolve()

def ml_octets(xs):
    return investigate.ml_list(xs, lambda i: 'n ' + str(i))

def ml_use(u):
    return 'NONE' if u is None else '(SOME ' + ml_octets(u) + ')'

def ml_artifact(a):
    pair = lambda r: '(' + ml_octets(r[0]) + ',' + ml_octets(r[1]) + ')'
    triple = lambda r: '(' + ml_octets(r[0]) + ',(' + ml_octets(r[1]) + ',' + ml_octets(r[2]) + '))'
    return '(N.finite_enumerated_artifact ' + investigate.ml_list(a['carrier'], ml_octets) + ' ' + \
        investigate.ml_list(a['incidence'], triple) + ' ' + investigate.ml_list(a['bag'], pair) + ' ' + \
        investigate.ml_list(a['functional'], pair) + ')'

def ml_environment(e):
    artifact = lambda r: '(' + ml_use(r[0]) + ',' + ml_artifact(r[1]) + ')'
    binding = lambda r: '((' + ml_use(r[0]) + ',' + ml_octets(r[1]) + '),' + ml_use(r[2]) + ')'
    return '(N.finite_enumerated_environment ' + investigate.ml_list(e['artifacts'], artifact) + ' ' + \
        investigate.ml_list(e['bindings'], binding) + ')'

def program(engine, inputs):
    prelude = construction.PRELUDE.replace('structure N = Application_Comparison;', 'structure N = Native_Reasoning;', 1)
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n' + prelude
    code += 'val sourceEnvironment = ' + ml_environment(inputs['source']) + ';\n'
    code += 'val extendedEnvironment = ' + ml_environment(inputs['extended']) + ';\n'
    code += 'val interiors = ' + investigate.ml_list(inputs['node_interior'], ml_octets) + ';\n'
    code += r'''
fun ft t = case N.finite_self_contained_term t of SOME x => x | NONE => raise Fail "Expected complete data";
fun pl xs = N.Finite_Payload (map n xs);
fun pair a b = N.Finite_Pair (a,b);
fun seq xs = List.foldr (fn (x,ys) => pair x ys) (pl []) xs;
fun table xs = seq (map (fn (k,v) => pair k v) xs);
fun site u a = pair (ft (N.use_data_term u)) (N.Finite_Payload a);
fun root e u a = pair (pair e (ft (N.use_data_term u))) (N.Finite_Payload a);
fun jrow (k,v) = "[" ^ jterm k ^ "," ^ jterm v ^ "]";
fun rowFields (N.Finite_Pair (k,v)) = (k,v) | rowFields _ = raise Fail "Expected complete row";
val e = ft (N.finite_environment_term extendedEnvironment);
val f = ft (N.finite_environment_term sourceEnvironment);
val owner = ft (N.use_data_term (SOME [n 2]));
val callee = site (SOME [n 2]) [n 1];
val parentKey = site (SOME []) [];
val childKey = site (SOME [n 1]) [];
val premiseKey = site (SOME [n 2]) [n 24];
val claimValue = pair callee (pair (pl []) (pl []));
val claimRows = [(parentKey,claimValue),(childKey,claimValue)];
val dischargeRows = [(premiseKey,childKey)];
val joinedRows = map (fn (s,m) => case N.finite_key_fibre_values m claimRows of
 [v] => pair s v | _ => raise Fail "Actual child fibre is not singleton") dischargeRows;
val (left,right) = case N.finite_prefixed_observation_outputs owner joinedRows of
 SOME result => result | NONE => raise Fail "Actual projection failed";
val ordinary = table [(pl [24],pair callee (pl []))];
val report = pair (pl []) (pair (pair (pl []) (pair ordinary (pl []))) (pair (pl []) (pair ordinary (pl []))));
val source = seq [root e (SOME [n 2]) [n 0],root e (SOME []) [],callee,pl [7],
 root f (SOME [n 2]) [n 3],pair f (site (SOME [n 2]) [n 8]),report,table dischargeRows,
 seq (map N.Finite_Payload interiors),seq [pl [6],pl [14],pl [16]],seq [pl [3]],pl []];
val lookupParent = pair parentKey (pair (table claimRows) (seq [claimValue]));
val lookupChild = pair childKey (pair (table claimRows) (seq [claimValue]));
val joinedCall = pair (table claimRows) (pair (table dischargeRows) (seq joinedRows));
val projectionCall = pair owner (pair (seq joinedRows) (pair (seq left) (seq right)));
val conditionCalls = [(n 21,table claimRows),(n 28,lookupParent),(n 28,lookupChild),
 (n 358,projectionCall),(n 353,pair (seq left) ordinary),(n 353,pair (seq right) ordinary)];
val conditions = [N.finite_keyed_table_comparison claimRows claimRows,
 N.finite_key_fibre_holds parentKey claimRows [claimValue],N.finite_key_fibre_holds childKey claimRows [claimValue],
 true,N.finite_keyed_table_comparison (map rowFields left) [(pl [24],pair callee (pl []))],
 N.finite_keyed_table_comparison (map rowFields right) [(pl [24],pair callee (pl []))]];
val (_, (actualSchema,actualPremises)) = case List.find (fn (d,_) => d=n 359) N.inference_claim_construction_library of
 SOME x => x | NONE => raise Fail "Missing actual compiled reader";
val frontier = (n 350,source)::(n 100,joinedCall)::conditionCalls;
val request = (n 359,pair source (table claimRows));
val actualProblem = N.make_application_problem (n 359) actualSchema actualPremises
 (fs frontier) (fs [request]) (fs []);
val targets = N.application_construction_result N.Joined_Application_Observations actualProblem;
val () = print ("NONEMPTY_SOURCE {\"source\":" ^ jterm source ^ ",\"table\":" ^ jterm (table claimRows) ^
 ",\"owner\":" ^ jterm owner ^ ",\"rows\":" ^ jlist jrow claimRows ^
 ",\"discharge_rows\":" ^ jlist jrow dischargeRows ^ ",\"joined_rows\":" ^ jlist jterm joinedRows ^
 ",\"projection\":[" ^ jlist jterm left ^ "," ^ jlist jterm right ^ "],\"condition_calls\":" ^ jlist jcall conditionCalls ^
 ",\"condition_values\":" ^ jlist Bool.toString conditions ^ ",\"join_call\":" ^ jcall (n 100,joinedCall) ^ "}\n");
val () = print ("NONEMPTY_APPLICATION {\"problem\":" ^ jproblem (n 0,actualProblem) ^ ",\"targets\":" ^ jf jlocal targets ^ "}\n");
'''
    code += r"""
fun emitFibre (i,k,rows) = let val result=N.finite_key_fibre_values k rows in
 print ("FIBRE_VALUES " ^ Int.toString i ^ " {\"key\":" ^ jterm k ^ ",\"rows\":" ^ jlist jrow rows ^
  ",\"values\":" ^ jlist jterm result ^ ",\"admitted\":" ^ Bool.toString (N.finite_key_fibre_holds k rows result) ^ "}\n") end;
val ()=List.app emitFibre [
 (0,childKey,claimRows),(1,pl [200],claimRows),
 (2,childKey,claimRows @ [(childKey,claimValue)]),
 (3,childKey,claimRows @ [(pl [201],pl [256])]),
 (4,pl [256],[(pl [256],pl [])])];
val ()=print ("LEGACY_SOURCE " ^ jterm (N.finite_literal_inference_value []) ^ "\n");
"""
    return code

def assess(inputs, raw):
    source, applications, fibres, legacy = [], [], {}, []
    for line in raw.splitlines():
        if line.startswith('NONEMPTY_SOURCE '): source.append(json.loads(line.split(' ', 1)[1]))
        elif line.startswith('NONEMPTY_APPLICATION '): applications.append(json.loads(line.split(' ', 1)[1]))
        elif line.startswith('FIBRE_VALUES '):
            _, i, body = line.split(' ', 2)
            assert int(i) not in fibres
            fibres[int(i)] = json.loads(body)
        elif line.startswith('LEGACY_SOURCE '): legacy.append(json.loads(line.split(' ', 1)[1]))
    assert len(source) == len(applications) == len(legacy) == 1
    assert set(fibres) == set(range(5))
    for i, row in fibres.items():
        assert row['values'] == [v for k, v in row['rows'] if k == row['key']]
        assert row['admitted'] == (review.formed(row['key']) and tables.data(row['key']) and tables.rows_formed(row['rows']))
    assert [len(fibres[i]['values']) for i in range(5)] == [1, 0, 2, 1, 1]
    legacy_recovery = recovery.recover_argument(legacy[0], json.loads(family.ORIGINAL.read_text()))
    value, actual = source[0], applications[0]
    recovered = recovery.recover_argument(value['source'], inputs)
    assert value['condition_values'] == [True] * 6
    assert len(value['rows']) == 2 and len(value['discharge_rows']) == len(value['joined_rows']) == 1
    assert all(review.formed(t) for _, t in value['condition_calls'])
    problem = actual['problem']
    assert problem['entry'] == 359 and problem['requests'] == [[359, review.pair(value['source'], value['table'])]]
    _, _, reconstructed = construction.control_results(problem)
    assert construction.keys(actual['targets']) == construction.keys(reconstructed)
    assert len(actual['targets']) == 1 and len(actual['targets'][0]['bindings']) == 28
    assert len(actual['targets'][0]['premises']) == 7
    assert value['projection'] == [[review.pair(review.payload(24), review.pair(
        review.pair(value['owner'], review.payload(1)), review.payload()))]] * 2
    return {'fibre_values': fibres, 'legacy_source_recovery': legacy_recovery, 'source': value, 'application_problem': problem, 'native_application_targets': actual['targets'],
            'source_recovery': recovered,
            'boundary': 'Native formatting, complete data operations and compatible application construction use the accepted module. This stage reconstructs the source specification and complete prospective application. Source-leaf truth and local-reader admission are established by the separate source and correspondence theorems.'}

def main():
    parser = argparse.ArgumentParser()
    for name in ['proof', 'poly', 'output']: parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    receipt = proved_code.checked_execution(args.proof, args.poly, args.output, project=WORKTREE,
        required_theories=['Finite_Keyed_Fibre_Values', 'Inference_Claim_Input_Execution', 'Factor_Inference_Claim_Compilation', 'Factor_Application_Execution',
                           'Factor_Executable_Environment_Values', 'Factor_Prefixed_Observation_Execution'],
        inputs=family.source_specification(), input_paths=[Path(__file__), Path(family.__file__), RECOVERY, family.ORIGINAL],
        program=program, assess=assess, timeout=180,
        question='Reconstruct the complete nonempty source terms and actual child-reader application from the retained source specification.',
        boundary='The source specification is explicit complete data. The native constructor supplies the application and its binding coverage; source admission is established separately by the source theories.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error')}))
    return int(receipt['status'] != 'accepted')

if __name__ == '__main__': raise SystemExit(main())
