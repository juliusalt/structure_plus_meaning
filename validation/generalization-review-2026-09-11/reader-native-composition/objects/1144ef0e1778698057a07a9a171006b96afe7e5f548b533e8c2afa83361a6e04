theory Factor_Proof_Rows
  imports Factor_Proof_Copy Factor_Reference_Environments Factor_Reference_Forests
begin

section \<open>Embedding citations and term quotations from their complete syntax\<close>

lemma external_syntax_embedded_site:
  assumes ef: "environment_formed E" and art: "artifact_at E u S"
    and address: "octets_formed (snd d)"
    and addressing: "finite_addressing (rra_carrier (object_structure (external_occurrence_syntax (snd d)))) f"
    and reads: "object_reads_agree (push_object f (external_occurrence_syntax (snd d))) S
      (f ` rra_carrier (object_structure (external_occurrence_syntax (snd d))))"
    and refs: "syntax_references E u L C" and entry: "(f [4],d) \<in> C"
  shows "site_citation_at E u (f []) d (f ` {[],[5]}) {f [4]}"
proof -
  let ?R = "external_occurrence_syntax (snd d)"
  have original: "citation_at ?R [] (External [4] (snd d)) {[],[5]}"
    by (rule external_occurrence_syntax_recovers[OF address])
  have copied: "citation_at (push_object f ?R) (f []) (External (f [4]) (snd d)) (f ` {[],[5]})"
    using citation_at_push[OF original addressing] by simp
  have sf: "exact_formed S" using ef art unfolding environment_formed_def by blast
  have ri: "object_reads_agree (push_object f ?R) S (f ` {[],[5]})"
    by (rule object_reads_agree_mono[OF reads]) (auto simp: external_occurrence_syntax_def)
  have cite: "citation_at S (f []) (External (f [4]) (snd d)) (f ` {[],[5]})"
    by (rule citation_at_read_transport[OF copied sf ri])
  have actual: "binds_slot E u (f [4]) (fst d) \<and>
    (\<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d))"
    using refs entry unfolding syntax_references_def by blast
  have location: "citation_location E u (External (f [4]) (snd d)) (fst d) (snd d)"
    using actual by simp
  show ?thesis unfolding site_citation_at_def
    by (rule conjI[OF ef], rule exI[of _ S], rule exI[of _ "External (f [4]) (snd d)"])
       (use art cite location in simp)
qed

lemma term_syntax_embedded:
  assumes tf: "term_formed t" and ef: "environment_formed E" and art: "artifact_at E u S"
    and addressing: "finite_addressing (rra_carrier (object_structure (term_syntax t))) f"
    and reads: "object_reads_agree (push_object f (term_syntax t)) S
      (f ` rra_carrier (object_structure (term_syntax t)))"
    and refs: "syntax_references E u (map_slot_keys f (term_literal_bindings t)) C"
  shows "term_quoted_at E u (f []) t (f ` term_syntax_interior t)
    (f ` rel_dom (term_literal_bindings t))"
proof -
  have ri: "object_reads_agree (push_object f (term_syntax t)) S (f ` term_syntax_interior t)"
    by (rule object_reads_agree_mono[OF reads]) (auto simp: term_syntax_carrier)
  have slots: "\<forall>k\<in>rel_dom (term_literal_bindings t).
    external_slot_values (term_environment t) None k = external_slot_values E u (f k)"
  proof (intro ballI)
    fix k assume key: "k \<in> rel_dom (term_literal_bindings t)"
    obtain R where member: "(k,R) \<in> term_literal_bindings t" using key by (auto simp: rel_dom_def)
    have mapped: "(f k,R) \<in> map_slot_keys f (term_literal_bindings t)"
      by (rule map_slot_keys_member[OF member])
    have actual: "external_slot_values E u (f k) = {R}"
      using refs mapped unfolding syntax_references_def by blast
    have unique: "{T. (k,T) \<in> term_literal_bindings t} = {R}"
      using term_literal_bindings_functional[of t] member by (auto simp: single_valued_def)
    show "external_slot_values (term_environment t) None k = external_slot_values E u (f k)"
      by (simp add: actual unique)
  qed
  show ?thesis by (rule term_quotation_transport[OF term_syntax_recovers[OF tf]
        term_environment_source addressing ri slots ef art])
qed

section \<open>A site and a term form a complete binding row\<close>

definition binding_row_syntax :: "local_address \<Rightarrow> factor_term \<Rightarrow> exact_artifact" where
  "binding_row_syntax a t = pair_syntax (external_occurrence_syntax a) (term_syntax t)"

definition binding_row_interior :: "factor_term \<Rightarrow> local_address set" where
  "binding_row_interior t = {[],[0],[1],[2],[2,5]} \<union> Cons 3 ` term_syntax_interior t"

abbreviation binding_row_literals where
  "binding_row_literals t \<equiv> map_slot_keys (Cons 3) (term_literal_bindings t)"

definition binding_row_slots :: "factor_term \<Rightarrow> local_address set" where
  "binding_row_slots t = {[2,4]} \<union> Cons 3 ` rel_dom (term_literal_bindings t)"

lemma binding_row_formed:
  assumes "octets_formed a" "term_formed t"
  shows "exact_formed (binding_row_syntax a t)"
  unfolding binding_row_syntax_def
  by (rule pair_syntax_formed[OF external_occurrence_syntax_formed[OF assms(1)] term_syntax_formed[OF assms(2)]])
     (simp_all add: external_occurrence_syntax_properties(1))

lemma binding_row_root [simp]: "[] \<in> rra_carrier (object_structure (binding_row_syntax a t))"
  by (simp add: binding_row_syntax_def)

lemma binding_row_interior_root [simp]: "[] \<in> binding_row_interior t"
  by (simp add: binding_row_interior_def)

lemma binding_row_counts [simp]: "bag_count (object_data (binding_row_syntax a t)) = (\<lambda>_. 0)"
  by (simp add: binding_row_syntax_def)

lemma binding_row_carrier:
  "rra_carrier (object_structure (binding_row_syntax a t)) = binding_row_interior t \<union> binding_row_slots t"
  by (auto simp: binding_row_syntax_def pair_syntax_def external_occurrence_syntax_def
      term_syntax_carrier binding_row_interior_def binding_row_slots_def)

lemma binding_row_boundary:
  "binding_row_interior t \<inter> binding_row_slots t = {}"
  using term_syntax_slot_boundary[of t]
  by (auto simp: binding_row_interior_def binding_row_slots_def)

lemma binding_row_reference_table:
  fixes d :: "'u definition_site"
  assumes tf: "term_formed t"
  shows "reference_table_formed (binding_row_literals t) {([2,4],d)}"
proof -
  have left: "reference_table_formed ({} :: (local_address \<times> exact_artifact) set) {([4],d)}"
    by (rule reference_table_callees) (auto simp: single_valued_def)
  have right: "reference_table_formed (term_literal_bindings t) ({} :: (local_address \<times> 'u definition_site) set)"
    by (rule reference_table_literals[OF term_literal_bindings_finite term_literal_bindings_functional
          term_literal_bindings_formed[OF tf]])
  show ?thesis using reference_table_disjoint_copies[OF left right]
    by (simp add: map_slot_keys_def)
qed

lemma binding_row_reference_domain:
  "rel_dom (binding_row_literals t) \<union> rel_dom {([2,4],d)} = binding_row_slots t"
  by (simp only: map_slot_keys_domain) (auto simp: rel_dom_def binding_row_slots_def)

theorem binding_row_recovers:
  assumes address: "octets_formed (snd d)" and tf: "term_formed t"
    and ef: "environment_formed E" and art: "artifact_at E u (binding_row_syntax (snd d) t)"
    and refs: "syntax_references E u (binding_row_literals t) {([2,4],d)}"
  shows "native_application_at E u [] d t (binding_row_interior t) (binding_row_slots t)"
proof -
  let ?R = "binding_row_syntax (snd d) t"
  have formed: "exact_formed ?R" by (rule binding_row_formed[OF address tf])
  have rec: "record_at ?R [] [[0],[1]] [[2],[3]]"
    using pair_syntax_record[of "external_occurrence_syntax (snd d)" "term_syntax t"] formed
    by (simp add: binding_row_syntax_def)
  have la: "finite_addressing (rra_carrier (object_structure (external_occurrence_syntax (snd d)))) (Cons 2)"
    by (rule prefix_addressing[OF external_occurrence_syntax_formed[OF address]]) simp
  have lr: "object_reads_agree (push_object (Cons 2) (external_occurrence_syntax (snd d))) ?R
    (Cons 2 ` rra_carrier (object_structure (external_occurrence_syntax (snd d))))"
    unfolding binding_row_syntax_def by (rule pair_syntax_reads_left[OF external_occurrence_syntax_properties(2)])
  have cite: "site_citation_at E u [2] d {[2],[2,5]} {[2,4]}"
    using external_syntax_embedded_site[OF ef art address la lr refs] by simp
  have ra: "finite_addressing (rra_carrier (object_structure (term_syntax t))) (Cons 3)"
    by (rule prefix_addressing[OF term_syntax_formed[OF tf]]) simp
  have rr: "object_reads_agree (push_object (Cons 3) (term_syntax t)) ?R
    (Cons 3 ` rra_carrier (object_structure (term_syntax t)))"
    unfolding binding_row_syntax_def by (rule pair_syntax_reads_right[OF term_syntax_no_counts])
  have quoted: "term_quoted_at E u [3] t (Cons 3 ` term_syntax_interior t)
    (Cons 3 ` rel_dom (term_literal_bindings t))"
    using term_syntax_embedded[OF tf ef art ra rr refs] by simp
  have top: "insert [] (set [[0],[1]]) \<inter> ({[2],[2,5]} \<union> Cons 3 ` term_syntax_interior t) = {}" by auto
  have children: "{[2],[2,5]} \<inter> Cons 3 ` term_syntax_interior t = {}" by auto
  have interior: "insert [] (set [[0],[1]] \<union> {[2],[2,5]} \<union> Cons 3 ` term_syntax_interior t) = binding_row_interior t"
    by (auto simp: binding_row_interior_def)
  have boundary: "insert [] (set [[0],[1]] \<union> {[2],[2,5]} \<union> Cons 3 ` term_syntax_interior t) \<inter>
    ({[2,4]} \<union> Cons 3 ` rel_dom (term_literal_bindings t)) = {}"
    using binding_row_boundary[of t] by (simp only: interior binding_row_slots_def)
  show ?thesis using native_application_from_site_term[OF ef art rec cite quoted top children boundary]
    by (simp only: interior binding_row_slots_def)
qed

section \<open>Two sites form a complete premise-link row\<close>

definition discharge_row_syntax :: "local_address \<Rightarrow> local_address \<Rightarrow> exact_artifact" where
  "discharge_row_syntax a b = pair_syntax (external_occurrence_syntax a) (external_occurrence_syntax b)"

definition discharge_row_interior :: "local_address set" where
  "discharge_row_interior = {[],[0],[1],[2],[2,5],[3],[3,5]}"

definition discharge_row_slots :: "local_address set" where
  "discharge_row_slots = {[2,4],[3,4]}"

lemma discharge_row_formed:
  assumes "octets_formed a" "octets_formed b"
  shows "exact_formed (discharge_row_syntax a b)"
  unfolding discharge_row_syntax_def
  by (rule pair_syntax_formed[OF external_occurrence_syntax_formed[OF assms(1)]
        external_occurrence_syntax_formed[OF assms(2)]])
     (simp_all add: external_occurrence_syntax_properties(1))

lemma discharge_row_root [simp]: "[] \<in> rra_carrier (object_structure (discharge_row_syntax a b))"
  by (simp add: discharge_row_syntax_def)

lemma discharge_row_interior_root [simp]: "[] \<in> discharge_row_interior"
  by (simp add: discharge_row_interior_def)

lemma discharge_row_counts [simp]: "bag_count (object_data (discharge_row_syntax a b)) = (\<lambda>_. 0)"
  by (simp add: discharge_row_syntax_def)

lemma discharge_row_carrier:
  "rra_carrier (object_structure (discharge_row_syntax a b)) = discharge_row_interior \<union> discharge_row_slots"
  by (auto simp: discharge_row_syntax_def pair_syntax_def external_occurrence_syntax_def
      discharge_row_interior_def discharge_row_slots_def)

lemma discharge_row_boundary:
  "discharge_row_interior \<inter> discharge_row_slots = {}"
  by (simp add: discharge_row_interior_def discharge_row_slots_def)

lemma discharge_row_reference_table:
  "reference_table_formed {} {([2,4],d),([3,4],e)}"
  by (rule reference_table_callees) (auto simp: single_valued_def)

lemma discharge_row_reference_domain:
  "rel_dom {([2,4],d),([3,4],e)} = discharge_row_slots"
  by (auto simp: rel_dom_def discharge_row_slots_def)

theorem discharge_row_recovers:
  assumes da: "octets_formed (snd d)" and ea: "octets_formed (snd e)"
    and ef: "environment_formed E" and art: "artifact_at E u (discharge_row_syntax (snd d) (snd e))"
    and refs: "syntax_references E u {} {([2,4],d),([3,4],e)}"
  shows "native_site_link_at E u [] d e discharge_row_interior discharge_row_slots"
proof -
  let ?R = "discharge_row_syntax (snd d) (snd e)"
  have formed: "exact_formed ?R" by (rule discharge_row_formed[OF da ea])
  have rec: "record_at ?R [] [[0],[1]] [[2],[3]]"
    using pair_syntax_record[of "external_occurrence_syntax (snd d)" "external_occurrence_syntax (snd e)"] formed
    by (simp add: discharge_row_syntax_def)
  have la: "finite_addressing (rra_carrier (object_structure (external_occurrence_syntax (snd d)))) (Cons 2)"
    by (rule prefix_addressing[OF external_occurrence_syntax_formed[OF da]]) simp
  have lr: "object_reads_agree (push_object (Cons 2) (external_occurrence_syntax (snd d))) ?R
    (Cons 2 ` rra_carrier (object_structure (external_occurrence_syntax (snd d))))"
    unfolding discharge_row_syntax_def by (rule pair_syntax_reads_left[OF external_occurrence_syntax_properties(2)])
  have left: "site_citation_at E u [2] d {[2],[2,5]} {[2,4]}"
    using external_syntax_embedded_site[OF ef art da la lr refs] by simp
  have ra: "finite_addressing (rra_carrier (object_structure (external_occurrence_syntax (snd e)))) (Cons 3)"
    by (rule prefix_addressing[OF external_occurrence_syntax_formed[OF ea]]) simp
  have rr: "object_reads_agree (push_object (Cons 3) (external_occurrence_syntax (snd e))) ?R
    (Cons 3 ` rra_carrier (object_structure (external_occurrence_syntax (snd e))))"
    unfolding discharge_row_syntax_def by (rule pair_syntax_reads_right[OF external_occurrence_syntax_properties(2)])
  have right: "site_citation_at E u [3] e {[3],[3,5]} {[3,4]}"
    using external_syntax_embedded_site[OF ef art ea ra rr refs] by simp
  show ?thesis unfolding native_site_link_at_def
    by (rule conjI[OF ef], rule exI[of _ ?R], rule exI[of _ "[[0],[1]]"],
        rule exI[of _ "[2]"], rule exI[of _ "[3]"], rule exI[of _ "{[2],[2,5]}"],
        rule exI[of _ "{[2,4]}"], rule exI[of _ "{[3],[3,5]}"], rule exI[of _ "{[3,4]}"])
       (use art rec left right in \<open>auto simp: discharge_row_interior_def discharge_row_slots_def\<close>)
qed

text \<open>
  Row bytes depend on the cited local addresses and quoted terms. The actual
  target uses come from explicit environment bindings. The carrier equations
  account for every position in each row, including its exposed slots, and
  recovery works in every formed environment satisfying those references.
\<close>

end
