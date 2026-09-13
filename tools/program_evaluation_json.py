"""Serialize complete requested calls, bindings, applications, rules and answers."""

PRELUDE = r'''
fun jterm (N.Finite_Payload p) = "{\"payload\":" ^ jaddress p ^ "}"
  | jterm (N.Finite_Pair (t,u)) = "{\"pair\":[" ^ jterm t ^ "," ^ jterm u ^ "]}"
  | jterm (N.Finite_Target t) = "{\"target\":" ^ jtarget t ^ "}";
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
