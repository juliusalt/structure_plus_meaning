theory Factor_Finite_Term_Encoding
  imports Factor_Executable_Terms Factor_Finite_Reference_Tables RRA_Finite_Syntax_Construction
begin

fun finite_term_syntax :: "finite_factor_term\<Rightarrow>finite_exact_artifact" where
  "finite_term_syntax (Finite_Target t)=finite_literal_syntax t"
| "finite_term_syntax (Finite_Payload v)=finite_payload_syntax v"
| "finite_term_syntax (Finite_Pair x y)=finite_pair_syntax (finite_term_syntax x) (finite_term_syntax y)"

lemma finite_term_syntax_exact [simp]:
  "decode_finite_object (finite_term_syntax t)=term_syntax (decode_finite_term t)"
  by (induction t) simp_all

fun finite_term_literal_bindings :: "finite_factor_term\<Rightarrow>(local_address\<times>finite_exact_artifact) fset" where
  "finite_term_literal_bindings (Finite_Target t)={|([4],finite_target_artifact t)|}"
| "finite_term_literal_bindings (Finite_Payload v)={||}"
| "finite_term_literal_bindings (Finite_Pair x y)=
    finite_slot_keys (Cons 2) (finite_term_literal_bindings x) |\<union>|
    finite_slot_keys (Cons 3) (finite_term_literal_bindings y)"

lemma finite_term_literal_bindings_exact:
  "map_relation_values decode_finite_object (fset (finite_term_literal_bindings t))=
    term_literal_bindings (decode_finite_term t)"
proof (induction t)
  case (Finite_Target t)
  then show ?case by (simp add: map_relation_values_def)
next
  case (Finite_Payload v)
  then show ?case by (simp add: map_relation_values_def)
next
  case (Finite_Pair x y)
  show ?case
    by (simp only: finite_term_literal_bindings.simps decode_finite_term.simps
      term_literal_bindings.simps finite_reference_union_values finite_slot_keys_values Finite_Pair.IH)
      (simp add: map_slot_keys_def)
qed

definition finite_term_syntax_interior where
  "finite_term_syntax_interior t=
    finite_carrier (finite_structure (finite_term_syntax t)) |-| fimage fst (finite_term_literal_bindings t)"

lemma finite_term_literal_domain:
  "fset (fimage fst (finite_term_literal_bindings t))=
    rel_dom (term_literal_bindings (decode_finite_term t))"
  by (simp only: finite_term_literal_bindings_exact[symmetric] map_relation_values_domain
    rel_dom_image fimage.rep_eq map_relation_values_domain[unfolded rel_dom_image])

lemma finite_term_syntax_interior_exact:
  "fset (finite_term_syntax_interior t)=term_syntax_interior (decode_finite_term t)"
proof -
  have slots: "fset (fimage fst (finite_term_literal_bindings t))=
      rel_dom (term_literal_bindings (decode_finite_term t))"
    by (rule finite_term_literal_domain)
  have carrier: "fset (finite_carrier (finite_structure (finite_term_syntax t)))=
      term_syntax_interior (decode_finite_term t) \<union> fset (fimage fst (finite_term_literal_bindings t))"
    using term_syntax_carrier[of "decode_finite_term t"]
    by (simp only: finite_term_syntax_exact[symmetric] decode_finite_object_carrier slots)
  have separate: "term_syntax_interior (decode_finite_term t) \<inter>
      fset (fimage fst (finite_term_literal_bindings t))={}"
    by (simp only: slots; rule term_syntax_slot_boundary)
  show ?thesis
    using carrier separate by (auto simp: finite_term_syntax_interior_def)
qed

lemma finite_term_syntax_formed:
  "finite_term_formed t \<Longrightarrow> finite_exact_formed (finite_term_syntax t)"
  by (simp only: finite_exact_formed_correct finite_term_syntax_exact)
    (rule term_syntax_formed; simp only: finite_term_formed_correct[symmetric])

export_code finite_term_syntax finite_term_literal_bindings finite_term_syntax_interior checking SML

text \<open>
  The complete finite term supplies both quotation syntax and every literal
  reference. Whole and anchored targets retain their actual artifact values.
  The interior is derived from the actual carrier and full reference domain.
  These operations preserve malformed inputs for the separate formation guard.
\<close>

end
