theory RRA_Digit_Environment_Loading
  imports RRA_Digit_Generation_Readings Functional_Enumeration_Indexes
    "HOL-Library.Option_ord" "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

lemma finite_functional_rows_fset:
  "finite_relation_functional rows \<Longrightarrow> fset_of_list (finite_functional_rows rows)=rows"
proof -
  assume functional: "finite_relation_functional rows"
  have listed: "set (finite_functional_rows rows)=fset rows"
    using functional_rows_index.found_pairs[OF functional] by simp
  show ?thesis by (simp only: fset_inject[symmetric] fset_of_list.rep_eq listed)
qed

lemma digit_allocated_load_view:
  "map_option digit_allocated_view (load_digit_allocated A B)=
    (if finite_environment_formed (finite_enumerated_environment A B)
      then Some (finite_compact_use_head (fimage fst (fset_of_list A)) None,finite_enumerated_environment A B)
      else None)"
proof -
  have view: "digit_allocated_view=(\<lambda>q.
    encoded_bounded_view read_digit_use_path read_digit_address_path (raw_digit_allocated q))"
    by (rule ext; rule digit_allocated_view_raw)
  have project: "map_option digit_allocated_view (load_digit_allocated A B)=
    map_option (encoded_bounded_view read_digit_use_path read_digit_address_path)
      (map_option raw_digit_allocated (load_digit_allocated A B))"
    by (simp only: option.map_comp comp_def view)
  show ?thesis by (simp add: project digit_allocated_load_raw encoded_bounded_load_def
    encoded_bounded_rows_def encoded_bounded_view_def
    digit_environment.view_representation[OF digit_environment.rows_exact])
qed

definition load_digit_environment ::
  "local_address option finite_artifact_environment\<Rightarrow>digit_allocated_environment option" where
  "load_digit_environment E=(if finite_environment_formed E then
    load_digit_allocated (finite_functional_rows (finite_environment_artifacts E))
      (finite_functional_rows (finite_environment_bindings E)) else None)"

lemma formed_environment_functional_rows:
  assumes formed: "finite_environment_formed E"
  shows "finite_enumerated_environment (finite_functional_rows (finite_environment_artifacts E))
    (finite_functional_rows (finite_environment_bindings E))=E"
proof -
  have artifacts: "finite_relation_functional (finite_environment_artifacts E)"
    and bindings: "finite_relation_functional (finite_environment_bindings E)"
    using formed by (simp only: finite_environment_formed_def; blast)+
  show ?thesis by (simp only: finite_enumerated_environment_def
    finite_functional_rows_fset[OF artifacts] finite_functional_rows_fset[OF bindings]) simp
qed

theorem load_digit_environment_exact:
  "map_option digit_allocated_view (load_digit_environment E)=
    (if finite_environment_formed E then Some (finite_compact_use_head (finite_environment_uses E) None,E) else None)"
proof (cases "finite_environment_formed E")
  case True
  have functional: "finite_relation_functional (finite_environment_artifacts E)"
    using True by (simp only: finite_environment_formed_def; blast)
  show ?thesis by (simp only: load_digit_environment_def True if_True digit_allocated_load_view
    formed_environment_functional_rows[OF True] finite_functional_rows_fset[OF functional] finite_environment_uses_def)
next
  case False then show ?thesis by (simp only: load_digit_environment_def if_False option.map)
qed

text \<open>
  Initialization enumerates the complete formed input once using the existing
  functional-relation construction. It preserves every original artifact and
  binding and the actual initial allocation bound. Malformed input stays
  unavailable. Subsequent reading uses the resulting persistent index.
\<close>

end
