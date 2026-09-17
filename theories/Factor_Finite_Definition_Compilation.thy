theory Factor_Finite_Definition_Compilation
  imports Factor_Finite_Schema_Forests Factor_Finite_Interface_Syntax Factor_Definition_Code
begin

section \<open>Finite code fields are projections of the existing definition constructor\<close>

record finite_definition_code =
  finite_definition_artifact :: finite_exact_artifact
  finite_definition_interface :: "local_address finite_term_pattern"
  finite_definition_clauses :: "(local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) fset"
  finite_definition_literals :: "(local_address\<times>finite_exact_artifact) fset"
  finite_definition_callees :: "(local_address\<times>local_address option definition_site) fset"

definition decode_finite_definition_code :: "finite_definition_code\<Rightarrow>definition_code" where
  "decode_finite_definition_code K=\<lparr>code_artifact=decode_finite_object (finite_definition_artifact K),
    code_interface=decode_finite_pattern (finite_definition_interface K),
    code_clauses=map_relation_values decode_finite_schema (fset (finite_definition_clauses K)),
    code_literals=map_relation_values decode_finite_object (fset (finite_definition_literals K)),
    code_callees=fset (finite_definition_callees K)\<rparr>"

definition finite_definition_wrapper :: "finite_exact_artifact\<Rightarrow>local_address\<Rightarrow>
    finite_exact_artifact\<Rightarrow>local_address list\<Rightarrow>finite_exact_artifact" where
  "finite_definition_wrapper R r S rs=finite_record_wrapper
    (finite_family_wrapper (finite_syntax_union R S) [1,0]
      (fset_of_list (zip (family_ports (length rs)) (map (Cons 3) rs))))
    [] [[0,0],[0,1]] [2#r,[1,0]]"

lemma decode_finite_definition_wrapper [simp]:
  "decode_finite_object (finite_definition_wrapper R r S rs)=
    definition_wrapper (decode_finite_object R) r (decode_finite_object S) rs"
  by (simp add: finite_definition_wrapper_def definition_wrapper_def fset_of_list.rep_eq)

definition finite_compile_definition :: "'a::linorder finite_term_pattern\<Rightarrow>
    ('c::linorder\<times>('a,'s::linorder,local_address option definition_site) finite_factor_schema) fset\<Rightarrow>
    finite_definition_code option" where
  "finite_compile_definition p Cs=(if finite_pattern_formed p \<and> finite_relation_functional Cs then
    (let rows=finite_functional_rows Cs; f=finite_binder_coordinates (finite_pattern_variables p) in
      case finite_compile_schema_forest (map snd rows) of None \<Rightarrow> None
      | Some (S,rs,As,A,B) \<Rightarrow>
        (case finite_interface_code f p of (R,r) \<Rightarrow> Some \<lparr>
          finite_definition_artifact=finite_definition_wrapper R r S rs,
          finite_definition_interface=map_finite_term_pattern (Cons 2 \<circ> f) p,
          finite_definition_clauses=fset_of_list (zip (family_ports (length rs))
            (map (finite_rename_schema (Cons 3) (Cons 3) id) As)),
          finite_definition_literals=finite_slot_keys (Cons 2) (finite_pattern_literal_bindings p) |\<union>|
            finite_slot_keys (Cons 3) A,
          finite_definition_callees=finite_slot_keys (Cons 3) B\<rparr>))
    else None)"

lemma finite_compile_definition_domain:
  "finite_compile_definition p Cs=None \<longleftrightarrow>
    \<not>finite_pattern_formed p \<or> \<not>finite_relation_functional Cs \<or>
    (\<exists>S\<in>rel_ran (fset Cs). finite_compile_schema S=None)"
proof (cases "finite_pattern_formed p \<and> finite_relation_functional Cs")
  case False
  then show ?thesis by (auto simp: finite_compile_definition_def)
next
  case True
  have functional: "finite_relation_functional Cs" using True by blast
  have range: "set (map snd (finite_functional_rows Cs))=rel_ran (fset Cs)"
    by (simp only: set_map finite_functional_rows_exact[OF functional] rel_ran_image)
  have empty: "finite_compile_definition p Cs=None \<longleftrightarrow>
    finite_compile_schema_forest (map snd (finite_functional_rows Cs))=None"
    using True by (auto simp: finite_compile_definition_def Let_def split: option.splits prod.splits)
  show ?thesis using True by (simp only: empty finite_compile_schema_forest_domain range; auto)
qed

corollary finite_compile_definition_total:
  assumes "finite_pattern_formed p" "finite_relation_functional Cs"
    "\<forall>S\<in>rel_ran (fset Cs). finite_schema_formed S \<and>
      fBall (finite_schema_dependencies S) (\<lambda>d. octets_formed (snd d))"
  shows "\<exists>K. finite_compile_definition p Cs=Some K"
  using assms by (cases "finite_compile_definition p Cs")
    (auto simp: finite_compile_definition_domain finite_compile_schema_domain)

theorem finite_compile_definition_correct:
  assumes result: "finite_compile_definition p Cs=Some K"
  shows "definition_code_for (decode_finite_pattern p)
    (map_relation_values decode_finite_schema (fset Cs)) (decode_finite_definition_code K)"
proof -
  have guard: "finite_pattern_formed p \<and> finite_relation_functional Cs"
    using result by (auto simp: finite_compile_definition_def Let_def split: option.splits prod.splits if_splits)
  have pf: "finite_pattern_formed p" and functional: "finite_relation_functional Cs" using guard by blast+
  let ?p="decode_finite_pattern p"
  let ?rows="finite_functional_rows Cs"
  let ?os="map fst ?rows"
  let ?Ss="map snd ?rows"
  let ?Ss'="map decode_finite_schema ?Ss"
  let ?f="finite_binder_coordinates (finite_pattern_variables p)"
  let ?Li="pattern_literal_bindings ?p"
  obtain R r where interface_result: "finite_interface_code ?f p=(R,r)" by (metis surjective_pairing)
  obtain S rs As A B where forest_result: "finite_compile_schema_forest ?Ss=Some (S,rs,As,A,B)"
    using result by (auto simp: finite_compile_definition_def Let_def guard interface_result split: option.splits prod.splits)
  have binders: "binder_addressing (pattern_variables ?p) ?f"
    using finite_binder_coordinates_properties[of "finite_pattern_variables p"]
    by (simp only: finite_pattern_variables_correct)
  note interface_properties=finite_interface_code_properties[OF pf binders interface_result]
  have interface: "exact_formed (decode_finite_object R)" "inj_on ?f (pattern_variables ?p)"
    "reference_table_formed ?Li ({}::(local_address\<times>local_address option definition_site) set)"
    "rel_dom ?Li\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    "\<forall>E::local_address option artifact_environment. \<forall>u.
      environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
      syntax_references E u ?Li {} \<longrightarrow> (\<exists>I J. scoped_pattern_at E u r (rename_pattern ?f ?p) I J \<and>
        rra_carrier (object_structure (decode_finite_object R))=I\<union>J)"
    using interface_properties binders by (auto simp: finite_exact_formed_correct binder_addressing_def finite_addressing_def)
  let ?A="map_relation_values decode_finite_object (fset A)"
  let ?B="fset B"
  let ?As="map decode_finite_schema As"
  note forest_properties=finite_compile_schema_forest_correct[OF forest_result]
  have as_length: "length As=length ?Ss" by (rule forest_properties(4))
  have clauses: "exact_formed (decode_finite_object S)"
    "bag_count (object_data (decode_finite_object S))=(\<lambda>_. 0)"
    "length rs=length ?Ss'" "length ?As=length ?Ss'" "reference_table_formed ?A ?B"
    "rel_dom ?A\<union>rel_dom ?B\<subseteq>rra_carrier (object_structure (decode_finite_object S))"
    "rel_ran ?B=(\<Union>T\<in>set ?Ss'. schema_dependencies T)"
    "set rs\<subseteq>rra_carrier (object_structure (decode_finite_object S))"
    "\<forall>i<length ?Ss'. schema_alpha_variant (?Ss'!i) (?As!i)"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object S) \<longrightarrow>
      syntax_references E u ?A ?B \<longrightarrow> (\<forall>i<length ?Ss'. native_schema_at E u (rs!i) (?As!i))"
    using forest_properties by (auto simp: finite_exact_formed_correct as_length)
  interpret code: definition_list_construction ?p ?Ss' "decode_finite_object R" "decode_finite_object S" r ?f ?Li ?A ?B rs ?As
    by (rule definition_list_construction.intro[OF interface clauses])
  have fields: "finite_definition_artifact K=finite_definition_wrapper R r S rs"
    "finite_definition_interface K=map_finite_term_pattern (Cons 2 \<circ> ?f) p"
    "finite_definition_clauses K=fset_of_list (zip (family_ports (length rs))
      (map (finite_rename_schema (Cons 3) (Cons 3) id) As))"
    "finite_definition_literals K=finite_slot_keys (Cons 2) (finite_pattern_literal_bindings p) |\<union>| finite_slot_keys (Cons 3) A"
    "finite_definition_callees K=finite_slot_keys (Cons 3) B"
    using result by (auto simp: finite_compile_definition_def Let_def guard interface_result forest_result)
  let ?K="decode_finite_definition_code K"
  have actual: "code_artifact ?K=code.artifact" "code_interface ?K=rename_pattern code.variables ?p"
    "code_literals ?K=code.literals" "code_callees ?K=code.callees"
  proof -
    show "code_artifact ?K=code.artifact"
      by (simp add: decode_finite_definition_code_def fields(1))
    show "code_interface ?K=rename_pattern code.variables ?p"
      by (simp add: decode_finite_definition_code_def fields(2) decode_finite_pattern_map)
    show "code_literals ?K=code.literals"
      by (simp only: decode_finite_definition_code_def definition_code.select_convs fields(4)
        finite_reference_union_values finite_slot_keys_values finite_pattern_literal_bindings_exact)
    show "code_callees ?K=code.callees"
      by (simp add: decode_finite_definition_code_def fields(5))
  qed
  have native_clauses: "code_clauses ?K=set (zip code.ports code.schemas)"
    by (simp add: decode_finite_definition_code_def fields(3) fset_of_list.rep_eq map_relation_values_def
      zip_map2 image_image map_map comp_def split_def finite_rename_schema_correct)
  let ?C="map_relation_values decode_finite_schema (fset Cs)"
  have enum: "set (zip ?os ?Ss')=?C"
    by (simp only: listed_relation_values finite_functional_rows_exact[OF functional])
  have source_length: "length ?os=length ?Ss'" by simp
  have key_length: "length ?os=length code.ports" using code.properties(5) by simp
  have target_length: "length code.ports=length code.schemas" using code.properties(5,7) by simp
  let ?h="listed_rekey ?os code.ports []"
  have rekey: "inj_on ?h (set ?os)" "map ?h ?os=code.ports"
    by (rule listed_rekey_properties[OF key_length finite_functional_rows_distinct_keys[OF functional] code.properties(6)])+
  have family: "schema_family_variant ?h ?C (set (zip code.ports code.schemas))"
    using schema_family_variant_from_lists[OF source_length target_length code.properties(6) rekey code.properties(8)]
    by (simp only: enum)
  have source_range: "rel_ran ?C=set ?Ss'" using zip_range[OF source_length] by (simp only: enum)
  have correspondence: "\<exists>g h. inj_on g (pattern_variables ?p) \<and>
    code_interface ?K=rename_pattern g ?p \<and> schema_family_variant h ?C (code_clauses ?K)"
    by (rule exI[of _ code.variables], rule exI[of _ "?h"])
      (use code.properties(4) family in \<open>simp only: actual(2) native_clauses; blast\<close>)
  show ?thesis unfolding definition_code_for_def
    using correspondence code.properties(1-3,9-12)
    by (simp only: actual native_clauses source_range; blast)
qed

text \<open>
  The complete interface and original keyed clause family are the inputs.
  Every clause is compiled, all private blocks are assembled, and the complete
  native family receives its source correspondence. The resulting finite
  record decodes to the existing definition-code contract. Its interface and
  clause fields are proved projections, while the actual artifact and its
  literal and callee references supply native recovery.
\<close>

end
