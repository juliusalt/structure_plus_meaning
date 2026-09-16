"""Serialize complete requested calls, bindings, applications, rules and answers."""

TERM = r'''
datatype 'a term_output_part = Term_Value of 'a | Term_Text of string;
fun jterm value = let
  fun output [] chunks = String.concat (rev chunks)
    | output (Term_Text s :: rest) chunks = output rest (s :: chunks)
    | output (Term_Value (N.Finite_Payload p) :: rest) chunks =
        output rest ("}" :: jaddress p :: "{\"payload\":" :: chunks)
    | output (Term_Value (N.Finite_Target t) :: rest) chunks =
        output rest ("}" :: jtarget t :: "{\"target\":" :: chunks)
    | output (Term_Value (N.Finite_Pair (t,u)) :: rest) chunks =
        output (Term_Value t :: Term_Text "," :: Term_Value u :: Term_Text "]}" :: rest)
          ("{\"pair\":[" :: chunks)
  in output [Term_Value value] [] end;
'''

PRELUDE = TERM + r'''
fun jcallWith definition (d,t) = "[" ^ definition d ^ "," ^ jterm t ^ "]";
fun jbindingWith variable (a,t) = "[" ^ variable a ^ "," ^ jterm t ^ "]";
fun jpremiseWith socket definition (s,q) = "[" ^ socket s ^ "," ^ jcallWith definition q ^ "]";
fun japplicationWith variable socket definition key (d,(c,(t,(v,h)))) =
  "{\"definition\":" ^ definition d ^ ",\"clause\":" ^ key c ^ ",\"term\":" ^ jterm t ^
  ",\"bindings\":" ^ jf (jbindingWith variable) v ^
  ",\"premises\":" ^ jf (jpremiseWith socket definition) h ^ "}";
fun jruleWith socket definition (q,h) =
  "[" ^ jcallWith definition q ^ "," ^ jf (jpremiseWith socket definition) h ^ "]";
fun janswerWith definition NONE = "null"
  | janswerWith definition (SOME a) = jf (jcallWith definition) a;
'''
