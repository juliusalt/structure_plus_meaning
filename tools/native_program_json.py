"""Serialize complete finite native coordinates, artifacts, schemas and programs."""

COORDINATES = r'''
fun elements a = case N.fset a of N.Set xs => xs | N.Coset _ => raise Fail "Nonfinite representation";
fun jf f a = jlist f (elements a);
fun jaddress a = jlist jnat a;
fun juse NONE = "null" | juse (SOME a) = jaddress a;
fun jsite (u,r) = "[" ^ juse u ^ "," ^ jaddress r ^ "]";
'''

ARTIFACT_ROWS = r'''
fun jedge (r,(s,t)) = "[" ^ jaddress r ^ "," ^ jaddress s ^ "," ^ jaddress t ^ "]";
fun jdata (r,p) = "[" ^ jaddress r ^ "," ^ jaddress p ^ "]";
fun jartifact (carrier,(incidence,(counts,functions))) =
  "{\"carrier\":" ^ jlist jaddress carrier ^ ",\"incidence\":" ^ jlist jedge incidence ^
  ",\"counted_data\":" ^ jlist jdata counts ^ ",\"functional_data\":" ^ jlist jdata functions ^ "}";
fun jartifactRow (u,a) = "[" ^ juse u ^ "," ^ jartifact a ^ "]";
fun jbinding (k,v) = "[" ^ jsite k ^ "," ^ juse v ^ "]";
fun jenvironment (artifacts,bindings) =
  "{\"artifacts\":" ^ jlist jartifactRow artifacts ^ ",\"bindings\":" ^ jlist jbinding bindings ^ "}";
'''

TARGETS = r'''
fun jtarget (N.Finite_Whole a) = "{\"whole_artifact\":" ^ jartifact (N.finite_artifact_rows a) ^ "}"
  | jtarget (N.Finite_Anchor (a,r)) = "{\"anchored_artifact\":[" ^
      jartifact (N.finite_artifact_rows a) ^ "," ^ jaddress r ^ "]}";
'''

SCHEMAS = TARGETS + r'''fun jpatternWith variable (N.Finite_Variable a) = "{\"variable\":" ^ variable a ^ "}"
  | jpatternWith variable (N.Finite_Pattern_Payload p) = "{\"payload\":" ^ jaddress p ^ "}"
  | jpatternWith variable (N.Finite_Pattern_Pair (p,q)) =
      "{\"pair\":[" ^ jpatternWith variable p ^ "," ^ jpatternWith variable q ^ "]}"
  | jpatternWith variable (N.Finite_Pattern_Target t) = "{\"target\":" ^ jtarget t ^ "}";
fun jschemaWith variable socket definition s =
  let val pattern = jpatternWith variable
      fun premise (k,(d,p)) = "[" ^ socket k ^ "," ^ definition d ^ "," ^ pattern p ^ "]"
      fun material (k,m) = "[" ^ socket k ^ ",{\"source\":" ^ pattern (N.finite_material_source m) ^
        ",\"atoms\":" ^ pattern (N.finite_material_atoms m) ^
        ",\"edges\":" ^ pattern (N.finite_material_edges m) ^
        ",\"counts\":" ^ pattern (N.finite_material_counts m) ^
        ",\"functions\":" ^ pattern (N.finite_material_functions m) ^ "}]"
  in "{\"conclusion\":" ^ pattern (N.finite_schema_conclusion s) ^
    ",\"premises\":" ^ jf premise (N.finite_schema_premises s) ^
    ",\"materials\":" ^ jf material (N.finite_schema_materials s) ^ "}" end;
fun jpattern p = jpatternWith jaddress p;
fun jschema s = jschemaWith jaddress jaddress jsite s;
'''

PROGRAMS = r'''
fun jprogramWith variable socket definition key p =
  let fun interface (d,q) = "[" ^ definition d ^ "," ^ jpatternWith variable q ^ "]"
      fun clause ((d,c),s) = "[[" ^ definition d ^ "," ^ key c ^ "]," ^
        jschemaWith variable socket definition s ^ "]"
  in "{\"interfaces\":" ^ jf interface (N.finite_system_interfaces p) ^
    ",\"clauses\":" ^ jf clause (N.finite_system_clauses p) ^ "}" end;
fun jprogram p = jprogramWith jaddress jaddress jsite jaddress p;
'''
