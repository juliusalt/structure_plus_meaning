theory Factor_Finite_Proof_Tables
  imports Factor_Finite_Proof_Rows Factor_Finite_Syntax_Blocks Finite_Functional_Enumeration Factor_Proof_Tables
    "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder" "HOL-Library.Option_ord"
begin

definition finite_binding_row_block ::
    "(local_address option definition_site\<times>finite_factor_term)\<Rightarrow>local_address option finite_syntax_block" where
  "finite_binding_row_block q=(case q of (d,t) \<Rightarrow>
    (finite_binding_row_syntax (snd d) t,finite_binding_row_literals t,{|([2,4],d)|}))"

definition finite_discharge_row_block ::
    "(local_address option definition_site\<times>local_address option definition_site)\<Rightarrow>
      local_address option finite_syntax_block" where
  "finite_discharge_row_block q=(case q of (s,n) \<Rightarrow>
    (finite_discharge_row_syntax (snd s) (snd n),{||},{|([2,4],s),([3,4],n)|}))"

definition finite_binding_table_ready where
  "finite_binding_table_ready V=(finite_relation_functional V \<and>
    fBall V (\<lambda>(d,t). octets_formed (snd d) \<and> finite_term_formed t))"

definition finite_discharge_table_ready where
  "finite_discharge_table_ready D=(finite_relation_functional D \<and>
    fBall D (\<lambda>(s,n). octets_formed (snd s) \<and> octets_formed (snd n)))"

definition finite_compile_binding_table where
  "finite_compile_binding_table V=(if finite_binding_table_ready V then
    Some (finite_table_block (map finite_binding_row_block (finite_functional_rows V))) else None)"

definition finite_compile_discharge_table where
  "finite_compile_discharge_table D=(if finite_discharge_table_ready D then
    Some (finite_table_block (map finite_discharge_row_block (finite_functional_rows D))) else None)"

lemma finite_compile_binding_table_domain:
  "(\<exists>B. finite_compile_binding_table V=Some B) \<longleftrightarrow> finite_binding_table_ready V"
  by (cases "finite_binding_table_ready V")
    (simp only: finite_compile_binding_table_def if_True if_False option.inject option.distinct; blast)+

lemma finite_compile_discharge_table_domain:
  "(\<exists>B. finite_compile_discharge_table D=Some B) \<longleftrightarrow> finite_discharge_table_ready D"
  by (cases "finite_discharge_table_ready D")
    (simp only: finite_compile_discharge_table_def if_True if_False option.inject option.distinct; blast)+

lemma finite_binding_table_rows:
  assumes ready: "finite_binding_table_ready V"
  shows "distinct (map fst (finite_functional_rows V))"
    "set (map (\<lambda>(d,t). (d,decode_finite_term t)) (finite_functional_rows V))=decode_finite_term_bindings V"
proof -
  have functional: "finite_relation_functional V" using ready by (simp only: finite_binding_table_ready_def; blast)
  show "distinct (map fst (finite_functional_rows V))"
    by (rule finite_functional_rows_distinct_keys[OF functional])
  show "set (map (\<lambda>(d,t). (d,decode_finite_term t)) (finite_functional_rows V))=decode_finite_term_bindings V"
    by (simp only: set_map finite_functional_rows_exact[OF functional]
      decode_finite_term_bindings_def map_relation_values_def)
qed

lemma finite_discharge_table_rows:
  assumes ready: "finite_discharge_table_ready D"
  shows "distinct (map fst (finite_functional_rows D))" "set (finite_functional_rows D)=fset D"
proof -
  have functional: "finite_relation_functional D"
    using ready by (simp only: finite_discharge_table_ready_def; blast)
  show "distinct (map fst (finite_functional_rows D))"
    by (rule finite_functional_rows_distinct_keys[OF functional])
  show "set (finite_functional_rows D)=fset D"
    by (rule finite_functional_rows_exact[OF functional])
qed


locale finite_binding_table_construction =
  fixes V :: "(local_address option definition_site\<times>finite_factor_term) fset"
  assumes ready: "finite_binding_table_ready V"
begin

abbreviation rows where "rows \<equiv> finite_functional_rows V"
abbreviation decoded where "decoded \<equiv> map (\<lambda>(d,t). (d,decode_finite_term t)) rows"
abbreviation block where "block \<equiv> finite_table_block (map finite_binding_row_block rows)"

lemma row_set: "set rows=fset V"
  by (rule finite_functional_rows_exact) (use ready in \<open>simp add: finite_binding_table_ready_def\<close>)

sublocale native: binding_table_construction decoded
proof (rule binding_table_construction.intro)
  show "distinct (map fst decoded)"
    using finite_binding_table_rows(1)[OF ready] by (simp add: comp_def split_def)
  show "\<forall>q\<in>set decoded. octets_formed (snd (fst q)) \<and> term_formed (snd q)"
    using ready by (auto simp: finite_binding_table_ready_def row_set finite_term_formed_correct)
qed

lemma fields:
  "decode_finite_object (finite_block_artifact block)=native.table.framed"
  "map_relation_values decode_finite_object (fset (finite_block_literals block))=native.table.literals"
  "fset (finite_block_callees block)=native.table.callees"
  by (simp_all add: finite_table_block_fields finite_binding_row_block_def
    finite_binding_row_literals_exact comp_def split_def)

lemma boundaries:
  "fset (finite_block_slots block)=native.table.table_slots"
  "fset (finite_block_interior block)=native.table.table_interior"
  using finite_block_boundary[where B=block and I="native.table.table_interior" and K="native.table.table_slots"]
  by (simp_all only: fields native.table.carrier native.table.boundary native.table.reference_domain)

lemma properties:
  "exact_formed (decode_finite_object (finite_block_artifact block))"
  "bag_count (object_data (decode_finite_object (finite_block_artifact block)))=(\<lambda>_. 0)"
  "[]\<in>rra_carrier (object_structure (decode_finite_object (finite_block_artifact block)))"
  "reference_table_formed (map_relation_values decode_finite_object (fset (finite_block_literals block)))
    (fset (finite_block_callees block))"
  "rra_carrier (object_structure (decode_finite_object (finite_block_artifact block)))=
    fset (finite_block_interior block)\<union>fset (finite_block_slots block)"
  "fset (finite_block_interior block)\<inter>fset (finite_block_slots block)={}"
  "fset (finite_block_slots block)=
    rel_dom (map_relation_values decode_finite_object (fset (finite_block_literals block)))\<union>
      rel_dom (fset (finite_block_callees block))"
  "rel_ran (fset (finite_block_callees block))=rel_dom (decode_finite_term_bindings V)"
  using native.table.frame.formed native.table.frame.counts native.table.frame.root
    native.table.reference_table native.table.carrier native.table.boundary
    native.table.reference_domain native.reference_range
  by (simp_all only: fields boundaries finite_binding_table_rows(2)[OF ready])

theorem recovers:
  assumes ef: "environment_formed E" and art: "artifact_at E u (decode_finite_object (finite_block_artifact block))"
    and refs: "syntax_references E u
      (map_relation_values decode_finite_object (fset (finite_block_literals block))) (fset (finite_block_callees block))"
  shows "native_binding_table_at E u [] (decode_finite_term_bindings V)
    (fset (finite_block_interior block)) (fset (finite_block_slots block))"
  using native.recovers[OF ef art[unfolded fields] refs[unfolded fields]]
  by (simp only: boundaries finite_binding_table_rows(2)[OF ready])

end

locale finite_discharge_table_construction =
  fixes D :: "(local_address option definition_site\<times>local_address option definition_site) fset"
  assumes ready: "finite_discharge_table_ready D"
begin

abbreviation rows where "rows \<equiv> finite_functional_rows D"
abbreviation block where "block \<equiv> finite_table_block (map finite_discharge_row_block rows)"

sublocale native: discharge_table_construction rows
proof (rule discharge_table_construction.intro)
  show "distinct (map fst rows)" by (rule finite_discharge_table_rows(1)[OF ready])
  show "\<forall>q\<in>set rows. octets_formed (snd (fst q)) \<and> octets_formed (snd (snd q))"
    using ready by (auto simp: finite_discharge_table_ready_def finite_discharge_table_rows(2)[OF ready])
qed

lemma fields:
  "decode_finite_object (finite_block_artifact block)=native.table.framed"
  "map_relation_values decode_finite_object (fset (finite_block_literals block))=native.table.literals"
  "fset (finite_block_callees block)=native.table.callees"
  apply (simp_all only: finite_table_block_fields)
  by (simp_all add: finite_discharge_row_block_def
    map_relation_values_def comp_def split_def)

lemma boundaries:
  "fset (finite_block_slots block)=native.table.table_slots"
  "fset (finite_block_interior block)=native.table.table_interior"
  using finite_block_boundary[where B=block and I="native.table.table_interior" and K="native.table.table_slots"]
  by (simp_all only: fields native.table.carrier native.table.boundary native.table.reference_domain)

lemma properties:
  "exact_formed (decode_finite_object (finite_block_artifact block))"
  "bag_count (object_data (decode_finite_object (finite_block_artifact block)))=(\<lambda>_. 0)"
  "[]\<in>rra_carrier (object_structure (decode_finite_object (finite_block_artifact block)))"
  "reference_table_formed (map_relation_values decode_finite_object (fset (finite_block_literals block)))
    (fset (finite_block_callees block))"
  "rra_carrier (object_structure (decode_finite_object (finite_block_artifact block)))=
    fset (finite_block_interior block)\<union>fset (finite_block_slots block)"
  "fset (finite_block_interior block)\<inter>fset (finite_block_slots block)={}"
  "fset (finite_block_slots block)=
    rel_dom (map_relation_values decode_finite_object (fset (finite_block_literals block)))\<union>
      rel_dom (fset (finite_block_callees block))"
  "rel_ran (fset (finite_block_callees block))=rel_dom (fset D)\<union>rel_ran (fset D)"
  using native.table.frame.formed native.table.frame.counts native.table.frame.root
    native.table.reference_table native.table.carrier native.table.boundary
    native.table.reference_domain native.reference_range
  by (simp_all only: fields boundaries finite_discharge_table_rows(2)[OF ready])

theorem recovers:
  assumes ef: "environment_formed E" and art: "artifact_at E u (decode_finite_object (finite_block_artifact block))"
    and refs: "syntax_references E u
      (map_relation_values decode_finite_object (fset (finite_block_literals block))) (fset (finite_block_callees block))"
  shows "native_discharge_table_at E u [] (fset D)
    (fset (finite_block_interior block)) (fset (finite_block_slots block))"
  using native.recovers[OF ef art[unfolded fields] refs[unfolded fields]]
  by (simp only: boundaries finite_discharge_table_rows(2)[OF ready])

end

export_code finite_compile_binding_table finite_compile_discharge_table checking SML

text \<open>
  Each functional relation is enumerated by its actual keys. Every binding
  value and every indexed target remains present. Values do not require an
  ordering. Empty tables use the same complete family construction. Conflicting
  keys and malformed row values return no code. The recovery proofs instantiate the original
  native table constructions, including their complete reference ranges and
  position partitions. Installation still requires the actual formed environment
  and its exact artifact and reference readings.
\<close>

end
