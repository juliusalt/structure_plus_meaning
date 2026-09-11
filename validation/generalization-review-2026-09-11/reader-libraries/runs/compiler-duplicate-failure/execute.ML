use "\047\116\109\112\047\110\097\116\105\118\101\045\105\110\118\101\115\116\105\103\097\116\105\111\110\045\114\101\112\111\114\116\045\100\105\097\103\110\111\115\116\105\099\045\099\111\109\112\105\108\097\116\105\111\110\049\050\047\101\120\112\111\114\116\047\078\097\116\105\118\101\095\073\110\118\101\115\116\105\103\097\116\105\111\110\095\082\101\112\111\114\116\095\068\105\097\103\110\111\115\116\105\099\095\099\111\109\112\105\108\097\116\105\111\110\049\050\046\070\097\099\116\111\114\095\082\101\097\115\111\110\105\110\103\095\069\120\101\099\117\116\105\111\110\047\099\111\100\101\047\110\097\116\105\118\101\095\114\101\097\115\111\110\105\110\103\046\077\076";

structure N = Native_Reasoning;
val n = N.nat_of_integer;
val fs = N.fset_of_list;
val emptyTarget = N.Finite_Whole N.finite_empty_artifact;
val emptyTerm = N.Finite_Target emptyTarget;
fun jnat x = IntInf.toString (N.integer_of_nat x);
fun jlist f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
fun elements a = case N.fset a of N.Set xs => xs | N.Coset _ => raise Fail "Nonfinite representation";
fun jf f a = jlist f (elements a);
fun jtarget t = if N.finite_reasoning_term_equal (N.Finite_Target t) emptyTerm
 then "{\"empty_artifact\":true}" else raise Fail "Unexpected artifact outside the complete declared control family";
fun jterm (N.Finite_Payload b) = "{\"payload\":" ^ jlist jnat b ^ "}"
 | jterm (N.Finite_Pair (a,b)) = "{\"pair\":[" ^ jterm a ^ "," ^ jterm b ^ "]}"
 | jterm (N.Finite_Target t) = jtarget t;
fun jpattern (N.Finite_Variable v) = "{\"var\":" ^ jnat v ^ "}"
 | jpattern (N.Finite_Pattern_Payload b) = "{\"payload\":" ^ jlist jnat b ^ "}"
 | jpattern (N.Finite_Pattern_Pair (a,b)) = "{\"pair\":[" ^ jpattern a ^ "," ^ jpattern b ^ "]}"
 | jpattern (N.Finite_Pattern_Target t) = jtarget t;
fun jcall (d,t) = "[" ^ jnat d ^ "," ^ jterm t ^ "]";
fun jbinding (v,t) = "[" ^ jnat v ^ "," ^ jterm t ^ "]";
fun jpremise (s,(d,t)) = "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jterm t ^ "]";
fun jsymbolic (s,(d,p)) = "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jpattern p ^ "]";
fun jmaterial (s,m) = "[" ^ jnat s ^ "," ^ jlist jpattern
 [N.finite_material_source m,N.finite_material_atoms m,N.finite_material_edges m,
  N.finite_material_counts m,N.finite_material_functions m] ^ "]";
fun jschema s = "{\"head\":" ^ jpattern (N.finite_schema_conclusion s) ^
 ",\"premises\":" ^ jf jsymbolic (N.finite_schema_premises s) ^
 ",\"materials\":" ^ jf jmaterial (N.finite_schema_materials s) ^ "}";
fun jlibrary (d,(s,ps)) = "{\"entry\":" ^ jnat d ^ ",\"schema\":" ^ jschema s ^
 ",\"enumeration\":" ^ jlist jsymbolic ps ^ "}";
fun emitCompiledLibrary id rows = print
 ("COMPILED_LIBRARY " ^ Int.toString id ^ " " ^ jlist jlibrary rows ^ "\n");
fun japplication (d,(s,(t,(v,h)))) = "{\"entry\":" ^ jnat d ^ ",\"schema\":" ^ jschema s ^
 ",\"conclusion\":" ^ jterm t ^ ",\"bindings\":" ^ jf jbinding v ^ ",\"premises\":" ^ jf jpremise h ^ "}";
fun jreason (q,(h,(s,p))) = "{\"conclusion\":" ^ jcall q ^ ",\"premises\":" ^ jf jpremise h ^
 ",\"premise\":" ^ jnat s ^ ",\"condition\":" ^ jcall p ^ "}";
fun emit id (formed,(applications,(residual,(demand,reasons)))) = print
 ("REASONING_RESULT " ^ Int.toString id ^ " {\"input_formed\":" ^ Bool.toString formed ^
 ",\"applications\":" ^ jf japplication applications ^ ",\"residual\":" ^ jf jpremise residual ^
 ",\"demand\":" ^ jf jcall demand ^ ",\"reasons\":" ^ jf jreason reasons ^ "}\n");
fun emitViews id index (u,rows) = let
 val outputs = case N.finite_binding_observation_outputs u rows of NONE => "null"
  | SOME (xs,ys) => "[" ^ jlist jterm xs ^ "," ^ jlist jterm ys ^ "]";
 val frontier = N.finite_binding_observation_frontier u rows
 in print ("BINDING_RESULT " ^ Int.toString id ^ " " ^ Int.toString index ^
  " {\"outputs\":" ^ outputs ^ ",\"frontier\":" ^ jlist jcall frontier ^ "}\n") end;
fun emitConstructionFrontier id index library initial = print
 ("CONSTRUCTION_FRONTIER " ^ Int.toString id ^ " " ^ Int.toString index ^ " " ^
  jf jcall (N.natural_construction_frontier (n (IntInf.fromInt index)) library (fs initial)) ^ "\n");
fun emitConstructionSeed id u row = print
 ("CONSTRUCTION_SEED " ^ Int.toString id ^ " " ^ jlist jcall (N.finite_binding_list_seed u row) ^ "\n");
fun jinstruction (N.Pair_Admission_Instruction (d,a,b)) = "[\"pair\"," ^ jnat d ^ "," ^ jnat a ^ "," ^ jnat b ^ "]"
 | jinstruction (N.List_Admission_Instruction (d,a)) = "[\"list\"," ^ jnat d ^ "," ^ jnat a ^ "]";
fun emitInput start = let val (admitted,((root,(next,instructions)),decisions)) = N.generated_input_execution (n start)
 in print ("INPUT_RESULT " ^ IntInf.toString start ^ " {\"domain_admitted\":" ^ Bool.toString admitted ^
 ",\"root\":" ^ jnat root ^ ",\"next\":" ^ jnat next ^ ",\"instructions\":" ^ jlist jinstruction instructions ^
 ",\"decisions\":" ^ jlist Bool.toString decisions ^ "}\n") end;

fun jentryPremise (s,d) = "[" ^ jnat s ^ "," ^ jnat d ^ "]";
fun jentryRule (d,h) = "[" ^ jnat d ^ "," ^ jf jentryPremise h ^ "]";
fun jentryReason (d,(h,(s,e))) = "[" ^ jnat d ^ "," ^ jf jentryPremise h ^
 "," ^ jnat s ^ "," ^ jnat e ^ "]";
fun emitCoverage id (formed,(rules,(blocked,(demand,reasons)))) = print
 ("COVERAGE_RESULT " ^ Int.toString id ^ " {\"input_formed\":" ^ Bool.toString formed ^
 ",\"rules\":" ^ jf jentryRule rules ^ ",\"blocked\":" ^ jf jpremise blocked ^
 ",\"demand\":" ^ jf jnat demand ^ ",\"reasons\":" ^ jf jentryReason reasons ^ "}\n");
val () = emitCompiledLibrary 0 (N.natural_compiled_library [(n 21,(N.make (N.Finite_Variable (n 0)) (fs [(n 0,(n 20,N.Finite_Variable (n 0))),(n 0,(n 20,N.Finite_Variable (n 0)))]) (fs [])))]);
val () = emitConstructionFrontier 0 0 ((N.natural_compiled_library [(n 21,(N.make (N.Finite_Variable (n 0)) (fs [(n 0,(n 20,N.Finite_Variable (n 0))),(n 0,(n 20,N.Finite_Variable (n 0)))]) (fs [])))])) [(n 20,N.Finite_Payload [n 7])];
val () = emit 0 (N.natural_chained_investigation (n 0) (N.natural_compiled_library [(n 21,(N.make (N.Finite_Variable (n 0)) (fs [(n 0,(n 20,N.Finite_Variable (n 0))),(n 0,(n 20,N.Finite_Variable (n 0)))]) (fs [])))]) [(n 20,N.Finite_Payload [n 7])] (fs [(n 20,N.Finite_Payload [n 7])]) (fs [(n 0,(n 21,N.Finite_Payload [n 7]))]));
val () = emitCoverage 0 (N.natural_library_coverage [(n 21,(N.make (N.Finite_Variable (n 0)) (fs [(n 0,(n 20,N.Finite_Variable (n 0))),(n 0,(n 20,N.Finite_Variable (n 0)))]) (fs []),[(n 0,(n 20,N.Finite_Variable (n 0)))]))] (fs [(n 20,N.Finite_Payload [n 7])]) (fs [(n 0,(n 21,N.Finite_Payload [n 7]))]));
val () = List.app emitInput [0,335,336,337,1000,10000000000000000000000000];
