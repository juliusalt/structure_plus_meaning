theory Factor_Finite_Proof_Rows
  imports Factor_Finite_Term_Encoding Factor_Finite_Citation_Syntax Factor_Proof_Rows
begin

definition finite_binding_row_syntax where
  "finite_binding_row_syntax a t=
    finite_pair_syntax (finite_external_occurrence_syntax a) (finite_term_syntax t)"

definition finite_binding_row_interior where
  "finite_binding_row_interior t={|[],[0],[1],[2],[2,5]|} |\<union>| fimage (Cons 3) (finite_term_syntax_interior t)"

definition finite_binding_row_slots where
  "finite_binding_row_slots t={|[2,4]|} |\<union>| fimage (Cons 3) (fimage fst (finite_term_literal_bindings t))"

definition finite_binding_row_literals where
  "finite_binding_row_literals t=finite_slot_keys (Cons 3) (finite_term_literal_bindings t)"

lemma finite_binding_row_syntax_exact [simp]:
  "decode_finite_object (finite_binding_row_syntax a t)=binding_row_syntax a (decode_finite_term t)"
  by (simp add: finite_binding_row_syntax_def binding_row_syntax_def)

lemma finite_binding_row_interior_exact [simp]:
  "fset (finite_binding_row_interior t)=binding_row_interior (decode_finite_term t)"
  by (simp add: finite_binding_row_interior_def binding_row_interior_def finite_term_syntax_interior_exact)

lemma finite_binding_row_slots_exact [simp]:
  "fset (finite_binding_row_slots t)=binding_row_slots (decode_finite_term t)"
  by (simp add: finite_binding_row_slots_def binding_row_slots_def
    finite_term_literal_bindings_exact[symmetric] map_relation_values_domain rel_dom_image
    map_relation_values_domain[unfolded rel_dom_image] image_image)

lemma finite_binding_row_literals_exact:
  "map_relation_values decode_finite_object (fset (finite_binding_row_literals t))=
    binding_row_literals (decode_finite_term t)"
  by (simp only: finite_binding_row_literals_def finite_slot_keys_values finite_term_literal_bindings_exact)

definition finite_discharge_row_syntax where
  "finite_discharge_row_syntax a b=
    finite_pair_syntax (finite_external_occurrence_syntax a) (finite_external_occurrence_syntax b)"

definition finite_discharge_row_interior :: "local_address fset" where
  "finite_discharge_row_interior={|[],[0],[1],[2],[2,5],[3],[3,5]|}"

definition finite_discharge_row_slots :: "local_address fset" where
  "finite_discharge_row_slots={|[2,4],[3,4]|}"

lemma finite_discharge_row_syntax_exact [simp]:
  "decode_finite_object (finite_discharge_row_syntax a b)=discharge_row_syntax a b"
  by (simp add: finite_discharge_row_syntax_def discharge_row_syntax_def)

lemma finite_discharge_row_interior_exact [simp]:
  "fset finite_discharge_row_interior=discharge_row_interior"
  by (simp add: finite_discharge_row_interior_def discharge_row_interior_def)

lemma finite_discharge_row_slots_exact [simp]:
  "fset finite_discharge_row_slots=discharge_row_slots"
  by (simp add: finite_discharge_row_slots_def discharge_row_slots_def)

export_code finite_binding_row_syntax finite_binding_row_interior finite_binding_row_slots
  finite_binding_row_literals finite_discharge_row_syntax finite_discharge_row_interior
  finite_discharge_row_slots checking SML

end
