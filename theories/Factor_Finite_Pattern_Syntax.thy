theory Factor_Finite_Pattern_Syntax
  imports RRA_Finite_Syntax_Construction Factor_Executable_Terms Factor_Finite_Reference_Tables Finite_List_Rekey
begin

section \<open>Complete finite patterns instantiate the original recursive syntax constructor\<close>

definition finite_variable_syntax :: "local_address \<Rightarrow> finite_exact_artifact" where
  "finite_variable_syntax a=\<lparr>finite_structure=\<lparr>
    finite_carrier={|[],a|},finite_incidence={|([],[],a)|}\<rparr>,finite_data=finite_empty_basis\<rparr>"

lemma decode_finite_variable_syntax [simp]:
  "decode_finite_object (finite_variable_syntax a)=variable_syntax a"
  by (simp add: finite_variable_syntax_def variable_syntax_def decode_finite_object_def decode_finite_structure_def)

fun finite_pattern_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> finite_exact_artifact" where
  "finite_pattern_syntax f (Finite_Variable a)=finite_variable_syntax (f a)"
| "finite_pattern_syntax f (Finite_Pattern_Target t)=finite_literal_syntax t"
| "finite_pattern_syntax f (Finite_Pattern_Payload v)=finite_payload_syntax v"
| "finite_pattern_syntax f (Finite_Pattern_Pair p q)=
    finite_bound_pair_syntax (finite_pattern_syntax f p) (finite_pattern_syntax f q)"

lemma decode_finite_pattern_syntax [simp]:
  "decode_finite_object (finite_pattern_syntax f p)=pattern_syntax f (decode_finite_pattern p)"
  by (induction p) simp_all

fun finite_pattern_literal_bindings :: "'a finite_term_pattern \<Rightarrow> (local_address\<times>finite_exact_artifact) fset" where
  "finite_pattern_literal_bindings (Finite_Variable a)={||}"
| "finite_pattern_literal_bindings (Finite_Pattern_Target t)={|([4],finite_target_artifact t)|}"
| "finite_pattern_literal_bindings (Finite_Pattern_Payload v)={||}"
| "finite_pattern_literal_bindings (Finite_Pattern_Pair p q)=
    finite_slot_keys (Cons 2) (finite_pattern_literal_bindings p) |\<union>|
    finite_slot_keys (Cons 3) (finite_pattern_literal_bindings q)"

lemma finite_pattern_literal_bindings_exact:
  "map_relation_values decode_finite_object (fset (finite_pattern_literal_bindings p))=
    pattern_literal_bindings (decode_finite_pattern p)"
proof (induction p)
  case (Finite_Variable a)
  then show ?case by (simp add: map_relation_values_def)
next
  case (Finite_Pattern_Target t)
  then show ?case by (simp add: map_relation_values_def)
next
  case (Finite_Pattern_Payload v)
  then show ?case by (simp add: map_relation_values_def)
next
  case (Finite_Pattern_Pair p q)
  show ?case
    by (simp only: finite_pattern_literal_bindings.simps decode_finite_pattern.simps
      pattern_literal_bindings.simps finite_reference_union_values finite_slot_keys_values Finite_Pattern_Pair.IH)
      (simp add: map_slot_keys_def)
qed

definition finite_binder_coordinates :: "'a::linorder fset \<Rightarrow> 'a \<Rightarrow> local_address" where
  "finite_binder_coordinates V=(let xs=sorted_list_of_fset V;
    ys=map (\<lambda>n. 6#unary_address n) [0..<length xs] in listed_rekey xs ys [])"

lemma finite_binder_coordinates_properties:
  "binder_addressing (fset V) (finite_binder_coordinates V)"
proof -
  let ?xs="sorted_list_of_fset V"
  let ?ys="map (\<lambda>n. 6#unary_address n) [0..<length ?xs]"
  have keys: "distinct ?xs" and distinct_values: "distinct ?ys" by (simp_all add: distinct_map inj_on_def)
  have lengths: "length ?xs=length ?ys" by simp
  have injective: "inj_on (finite_binder_coordinates V) (fset V)"
    using listed_rekey_properties(1)[OF lengths keys distinct_values, where b="[]"]
    by (simp add: finite_binder_coordinates_def Let_def)
  have mapped: "map (finite_binder_coordinates V) ?xs=?ys"
    using listed_rekey_properties(2)[OF lengths keys distinct_values, where b="[]"]
    by (simp add: finite_binder_coordinates_def Let_def)
  have image: "finite_binder_coordinates V ` fset V=set ?ys"
    using arg_cong[OF mapped, of set] by simp
  have addresses: "octets_formed (finite_binder_coordinates V a)" if "a\<in>fset V" for a
  proof -
    have position: "finite_binder_coordinates V a\<in>set ?ys" using image that by blast
    then obtain n where shape: "finite_binder_coordinates V a=6#unary_address n" by auto
    show ?thesis using unary_address_formed[of n] by (simp add: shape octets_formed_def)
  qed
  have boundary: "finite_binder_coordinates V ` fset V\<subseteq>binder_addresses" using image by auto
  show ?thesis using injective addresses boundary by (auto simp: binder_addressing_def finite_addressing_def)
qed

lemma finite_pattern_syntax_formed:
  assumes "finite_pattern_formed p" "binder_addressing (pattern_variables (decode_finite_pattern p)) f"
  shows "finite_exact_formed (finite_pattern_syntax f p)"
  by (simp only: finite_exact_formed_correct decode_finite_pattern_syntax)
    (rule pattern_syntax_formed; use assms in \<open>simp_all add: finite_pattern_formed_correct\<close>)

text \<open>
  Variables, repeated variables, payloads, literal targets and paired patterns
  retain their complete original fields. The executable artifact decodes to
  the existing pattern constructor; its complete literal table decodes to the
  original reference requirements. The complete finite variable family
  supplies an explicit injective placement. Its positions depend on that
  local family's size rather than the numeric magnitude of its input keys.
\<close>

end
