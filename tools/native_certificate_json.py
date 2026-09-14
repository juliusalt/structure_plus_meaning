"""Serialize complete original native proof trees and certificate families."""

PRELUDE = r'''fun jproof (N.Schema_Proof (c,v,b)) = "{\"clause\":" ^ jaddress c ^
  ",\"bindings\":" ^ jf (jbindingWith jaddress) v ^ ",\"children\":" ^
  jf (fn (s,p) => "{\"socket\":" ^ jaddress s ^ ",\"proof\":" ^ jproof p ^ "}") b ^ "}";
fun jcertificate (q,p) = "{\"claim\":" ^ jcall q ^ ",\"proof\":" ^ jproof p ^ "}";
fun jderivation NONE = "null"
  | jderivation (SOME (p,(a,t))) = "{\"program\":" ^ jprogram p ^
      ",\"answer\":" ^ jf jcall a ^ ",\"certificates\":" ^ jf jcertificate t ^ "}";
'''


INSTANCES = r'''fun jinstantiated (p,q) = "{\"proof\":" ^ jproof p ^ ",\"claim\":" ^ jcall q ^ "}";
fun jpath ss = jlist jaddress ss;
fun jpaths r = jf (fn (ss,n) => "[" ^ jpath ss ^ "," ^ jinstantiated n ^ "]") r;
'''
