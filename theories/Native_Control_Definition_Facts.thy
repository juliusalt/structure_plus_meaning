theory Native_Control_Definition_Facts
  imports Isabelle_Constant_Closure
begin

text \<open>A locale's exported derived equation can carry its assumptions even
  when the original constant was defined unconditionally. This operation only
  retrieves the existing kernel definition identified by Isabelle's definition
  registry. It does not add an axiom, admit a proposition, or use an oracle.\<close>

ML \<open>
structure Native_Control_Definition_Facts =
struct
fun note binding constant lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val definitions = Isabelle_Constant_Closure.kernel_definitions thy constant;
    val (name, proposition) = (case definitions of [definition] => definition
      | _ => error "Expected exactly one existing kernel definition");
    val definition = Thm.axiom thy name;
    val _ = if Thm.prop_of definition aconv proposition andalso null (Thm.hyps_of definition)
      then () else error "The existing kernel definition boundary changed";
  in snd (Local_Theory.note ((binding, []), [definition]) lthy) end;
end;
\<close>

end
