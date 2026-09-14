"""Serialize complete graph fields with an explicit coordinate formatter."""

_TEMPLATE = r'''fun jnode N.Finite_Assertion = "{\"kind\":\"assertion\"}"
  | jnode (N.Finite_Inference (c,v)) = "{\"kind\":\"inference\",\"clause\":" ^ __COORDINATE_JSON__ c ^
      ",\"bindings\":" ^ jf (jbindingWith __COORDINATE_JSON__) v ^ "}";
fun jgraphWith key g = "{\"inferences\":" ^
  jf (fn (n,v) => "[" ^ key n ^ "," ^ jnode v ^ "]") (N.finite_graph_inferences g) ^
  ",\"discharges\":" ^ jf (fn ((n,s),q) => "[[" ^ key n ^ "," ^ __COORDINATE_JSON__ s ^ "]," ^ key q ^ "]")
    (N.finite_graph_discharges g) ^ "}";
'''

def prelude(coordinate):
    return _TEMPLATE.replace("__COORDINATE_JSON__", coordinate)
