theory Factor_Prospective_Encoding
  imports Factor_Pattern_Encoding
begin

section \<open>A callee address is data; its artifact comes from the environment\<close>

definition external_occurrence_syntax :: "local_address \<Rightarrow> exact_artifact" where
  "external_occurrence_syntax a =
    \<lparr>object_structure = \<lparr>rra_carrier = {[],[4],[5]}, rra_incidence = {([],[],[4]),([],[4],[5])}\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {([5],a)}\<rparr>\<rparr>"

lemma external_occurrence_syntax_literal:
  "external_occurrence_syntax a = literal_syntax (Occurrence_Anchor (R,a))"
  by (simp add: external_occurrence_syntax_def)

lemma external_occurrence_syntax_formed:
  assumes "octets_formed a"
  shows "exact_formed (external_occurrence_syntax a)"
  using assms by (auto simp: external_occurrence_syntax_def exact_formed_def object_formed_def
      rra_formed_def basis_formed_def basis_values_def bag_support_def single_valued_def octets_formed_def)

lemma external_occurrence_syntax_properties:
  "[] \<in> rra_carrier (object_structure (external_occurrence_syntax a))"
  "bag_count (object_data (external_occurrence_syntax a)) = (\<lambda>_. 0)"
  "binder_silent (external_occurrence_syntax a)"
  by (auto simp: external_occurrence_syntax_def binder_silent_def headed_incidence_def
      restrict_basis_def empty_basis_def basis_identity fun_eq_iff)

lemma external_occurrence_syntax_recovers:
  assumes formed: "octets_formed a"
  shows "citation_at (external_occurrence_syntax a) [] (External [4] a) {[],[5]}"
proof -
  have payload: "payload_at (external_occurrence_syntax a) [5] a"
    by (auto simp: external_occurrence_syntax_def payload_at_def restrict_basis_def basis_identity fun_eq_iff)
  have raw: "raw_citation_at (external_occurrence_syntax a) [] (External [4] a) {[],[5]}"
    by (rule raw_citation_at.external[OF _ _ _ payload])
       (auto simp: external_occurrence_syntax_def headed_incidence_def)
  show ?thesis using raw external_occurrence_syntax_formed[OF formed]
    by (auto simp: citation_at_def external_occurrence_syntax_def restrict_basis_def empty_basis_def basis_identity fun_eq_iff)
qed

definition prospective_syntax ::
  "('a \<Rightarrow> local_address) \<Rightarrow> local_address \<Rightarrow> 'a term_pattern \<Rightarrow> exact_artifact" where
  "prospective_syntax f a p = bound_pair_syntax (external_occurrence_syntax a) (pattern_syntax f p)"

definition prospective_interior :: "'a term_pattern \<Rightarrow> local_address set" where
  "prospective_interior p = {[],[0],[1],[2],[2,5]} \<union> Cons 3 ` pattern_syntax_interior p"

definition prospective_slots :: "'a term_pattern \<Rightarrow> local_address set" where
  "prospective_slots p = insert [2,4] (Cons 3 ` rel_dom (pattern_literal_bindings p))"

lemma prospective_syntax_root [simp]:
  "[] \<in> rra_carrier (object_structure (prospective_syntax f a p))"
  by (simp add: prospective_syntax_def)

lemma prospective_syntax_no_counts [simp]:
  "bag_count (object_data (prospective_syntax f a p)) = (\<lambda>_. 0)"
  by (simp add: prospective_syntax_def)

lemma prospective_syntax_silent [simp]: "binder_silent (prospective_syntax f a p)"
  unfolding prospective_syntax_def
  by (rule bound_pair_silent[OF external_occurrence_syntax_properties(3) pattern_syntax_silent])

lemma prospective_interior_outside:
  "prospective_interior p \<inter> binder_addresses = {}"
  by (auto simp: prospective_interior_def)

lemma prospective_slots_outside:
  "prospective_slots p \<inter> binder_addresses = {}"
  by (auto simp: prospective_slots_def)

lemma prospective_syntax_formed:
  assumes "octets_formed a" "pattern_formed p" "binder_addressing (pattern_variables p) f"
  shows "exact_formed (prospective_syntax f a p)"
  unfolding prospective_syntax_def
  by (rule bound_pair_syntax_formed[OF external_occurrence_syntax_formed[OF assms(1)]
        pattern_syntax_formed[OF assms(2,3)]])
     (simp_all add: external_occurrence_syntax_properties)

lemma prospective_syntax_record:
  assumes "exact_formed (prospective_syntax f a p)"
  shows "record_at (prospective_syntax f a p) [] [[0],[1]] [[2],[3]]"
  using bound_pair_record assms unfolding prospective_syntax_def by blast

lemma prospective_syntax_callee:
  assumes af: "octets_formed a" and pf: "pattern_formed p"
    and addressing: "binder_addressing (pattern_variables p) f"
  shows "citation_at (prospective_syntax f a p) [2] (External [2,4] a) {[2],[2,5]}"
proof -
  let ?L = "external_occurrence_syntax a"
  have lf: "exact_formed ?L" by (rule external_occurrence_syntax_formed[OF af])
  have cite: "citation_at ?L [] (External [4] a) {[],[5]}" by (rule external_occurrence_syntax_recovers[OF af])
  have addr: "finite_addressing (rra_carrier (object_structure ?L)) (syntax_prefix 2)"
    by (rule syntax_prefix_addressing[OF lf]) simp_all
  have copied: "citation_at (push_object (syntax_prefix 2) ?L) [2] (External [2,4] a) {[2],[2,5]}"
    using citation_at_push[OF cite addr] by (simp add: syntax_prefix_def)
  have full: "object_reads_agree (push_object (syntax_prefix 2) ?L) (prospective_syntax f a p)
    (syntax_prefix 2 ` rra_carrier (object_structure ?L))"
    unfolding prospective_syntax_def
    by (rule bound_pair_reads_left[OF external_occurrence_syntax_properties(2) pattern_syntax_silent])
  have inside: "{[2],[2,5]} \<subseteq> syntax_prefix 2 ` rra_carrier (object_structure ?L)"
    by (auto simp: external_occurrence_syntax_def syntax_prefix_def)
  have reads: "object_reads_agree (push_object (syntax_prefix 2) ?L) (prospective_syntax f a p) {[2],[2,5]}"
    by (rule object_reads_agree_mono[OF full inside])
  show ?thesis by (rule citation_at_read_transport[OF copied prospective_syntax_formed[OF af pf addressing] reads])
qed

lemma prospective_syntax_argument:
  assumes pf: "pattern_formed p" and addressing: "binder_addressing (pattern_variables p) f"
    and scope: "f ` pattern_variables p \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
    and ef: "environment_formed E" and art: "artifact_at E u (prospective_syntax f a p)"
    and slots: "\<forall>k\<in>rel_dom (pattern_literal_bindings p).
      external_slot_values E u (3#k) = {R. (k,R) \<in> pattern_literal_bindings p}"
  shows "pattern_quoted_at E u V [3] (rename_pattern f p)
    (Cons 3 ` pattern_syntax_interior p) (Cons 3 ` rel_dom (pattern_literal_bindings p))"
proof -
  have source: "pattern_quoted_at (pattern_environment f p) None V [] (rename_pattern f p)
    (pattern_syntax_interior p) (rel_dom (pattern_literal_bindings p))"
    by (rule pattern_syntax_recovers[OF pf addressing scope boundary])
  have addr: "finite_addressing (rra_carrier (object_structure (pattern_syntax f p))) (syntax_prefix 3)"
    by (rule syntax_prefix_addressing[OF pattern_syntax_formed[OF pf addressing]]) simp_all
  have reads: "object_reads_agree (push_object (syntax_prefix 3) (pattern_syntax f p)) (prospective_syntax f a p)
    (syntax_prefix 3 ` pattern_syntax_interior p)"
    unfolding prospective_syntax_def
    by (rule object_reads_agree_mono[OF bound_pair_reads_right[OF pattern_syntax_no_counts
          external_occurrence_syntax_properties(3)]])
       (auto simp: pattern_syntax_carrier[OF addressing])
  have agreement: "\<forall>k\<in>rel_dom (pattern_literal_bindings p).
    external_slot_values (pattern_environment f p) None k = external_slot_values E u (syntax_prefix 3 k)"
  proof (intro ballI)
    fix k assume member: "k \<in> rel_dom (pattern_literal_bindings p)"
    have outside: "k \<notin> binder_addresses" using pattern_literal_slots_outside[of p] member by blast
    show "external_slot_values (pattern_environment f p) None k = external_slot_values E u (syntax_prefix 3 k)"
      using slots member outside by (simp add: syntax_prefix_def)
  qed
  have injective: "inj (syntax_prefix 3)" by (rule syntax_prefix_injective) simp
  have copied: "pattern_quoted_at E u (syntax_prefix 3 ` V) (syntax_prefix 3 [])
    (rename_pattern (syntax_prefix 3) (rename_pattern f p))
    (syntax_prefix 3 ` pattern_syntax_interior p) (syntax_prefix 3 ` rel_dom (pattern_literal_bindings p))"
    by (rule pattern_quotation_transport[OF source pattern_environment_source addr reads agreement injective ef art])
  show ?thesis using copied
    by (simp only: syntax_prefix_root syntax_prefix_image_binders[OF boundary]
        renamed_pattern_prefix[OF addressing] syntax_prefix_image_outside[OF pattern_syntax_interior_outside]
        syntax_prefix_image_outside[OF pattern_literal_slots_outside])
qed

theorem prospective_syntax_recovers:
  assumes pf: "pattern_formed p" and addressing: "binder_addressing (pattern_variables p) f"
    and scope: "f ` pattern_variables p \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
    and ef: "environment_formed E" and art: "artifact_at E u (prospective_syntax f a p)"
    and slots: "\<forall>k\<in>rel_dom (pattern_literal_bindings p).
      external_slot_values E u (3#k) = {R. (k,R) \<in> pattern_literal_bindings p}"
    and binding: "binds_slot E u [2,4] v" and target: "artifact_at E v R" and anchor: "anchor_formed (R,a)"
  shows "prospective_call_at E u V [] (v,a) (rename_pattern f p) (prospective_interior p) (prospective_slots p)"
proof -
  have af: "octets_formed a" using anchor by (auto simp: anchor_formed_def exact_formed_def)
  have sf: "exact_formed (prospective_syntax f a p)" by (rule prospective_syntax_formed[OF af pf addressing])
  have rec: "record_at (prospective_syntax f a p) [] [[0],[1]] [[2],[3]]"
    by (rule prospective_syntax_record[OF sf])
  have cite: "citation_at (prospective_syntax f a p) [2] (External [2,4] a) {[2],[2,5]}"
    by (rule prospective_syntax_callee[OF af pf addressing])
  have loc: "citation_location E u (External [2,4] a) v a" using binding target anchor by auto
  have arg: "pattern_quoted_at E u V [3] (rename_pattern f p)
    (Cons 3 ` pattern_syntax_interior p) (Cons 3 ` rel_dom (pattern_literal_bindings p))"
    by (rule prospective_syntax_argument[OF pf addressing scope boundary ef art slots])
  have top_separate: "insert [] (set [[0],[1]]) \<inter> ({[2],[2,5]} \<union> Cons 3 ` pattern_syntax_interior p) = {}"
    by auto
  have child_separate: "{[2],[2,5]} \<inter> Cons 3 ` pattern_syntax_interior p = {}" by auto
  have key_separate: "prospective_interior p \<inter> (prospective_slots p \<union> V) = {}"
    using boundary pattern_syntax_slot_boundary[of p]
    by (auto simp: prospective_interior_def prospective_slots_def)
  show ?thesis unfolding prospective_call_at_def
    apply (rule conjI[OF ef])
    apply (rule exI[of _ "prospective_syntax f a p"], rule exI[of _ "[[0],[1]]"],
        rule exI[of _ "[2]"], rule exI[of _ "[3]"], rule exI[of _ "External [2,4] a"],
        rule exI[of _ "{[2],[2,5]}"], rule exI[of _ "Cons 3 ` pattern_syntax_interior p"],
        rule exI[of _ "Cons 3 ` rel_dom (pattern_literal_bindings p)"])
    using art rec cite loc arg top_separate child_separate key_separate
    by (auto simp: prospective_interior_def prospective_slots_def)
qed

lemma prospective_syntax_carrier:
  assumes addressing: "binder_addressing (pattern_variables p) f"
  shows "rra_carrier (object_structure (prospective_syntax f a p)) =
    prospective_interior p \<union> prospective_slots p \<union> f ` pattern_variables p"
proof -
  have vars: "f ` pattern_variables p \<subseteq> binder_addresses"
    using addressing by (simp add: binder_addressing_def)
  have right: "syntax_prefix 3 ` rra_carrier (object_structure (pattern_syntax f p)) =
    Cons 3 ` pattern_syntax_interior p \<union> Cons 3 ` rel_dom (pattern_literal_bindings p) \<union> f ` pattern_variables p"
    by (simp only: pattern_syntax_carrier[OF addressing] image_Un
        syntax_prefix_image_outside[OF pattern_syntax_interior_outside]
        syntax_prefix_image_outside[OF pattern_literal_slots_outside]
        syntax_prefix_image_binders[OF vars])
  have left: "syntax_prefix 2 ` rra_carrier (object_structure (external_occurrence_syntax a)) =
    {[2],[2,4],[2,5]}"
    by (auto simp: external_occurrence_syntax_def syntax_prefix_def)
  show ?thesis
    by (simp only: prospective_syntax_def bound_pair_syntax_def structured_object.select_convs
        rra_structure.select_convs left right)
       (auto simp: prospective_interior_def prospective_slots_def)
qed

section \<open>A closed witness for every prospective call pattern\<close>

definition prospective_environment ::
  "('a \<Rightarrow> local_address) \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    'a term_pattern \<Rightarrow> local_address option artifact_environment" where
  "prospective_environment f R a p =
    pattern_environment f (Pattern_Pair (Pattern_Target (Occurrence_Anchor (R,a))) p)"

lemma prospective_environment_formed:
  assumes anchor: "anchor_formed (R,a)" and pf: "pattern_formed p"
    and addressing: "binder_addressing (pattern_variables p) f"
  shows "environment_formed (prospective_environment f R a p)"
proof -
  have formed: "pattern_formed (Pattern_Pair (Pattern_Target (Occurrence_Anchor (R,a))) p)"
    using anchor pf by simp
  have scope: "binder_addressing (pattern_variables (Pattern_Pair (Pattern_Target (Occurrence_Anchor (R,a))) p)) f"
    using addressing by simp
  show ?thesis unfolding prospective_environment_def by (rule pattern_environment_formed[OF formed scope])
qed

lemma prospective_environment_source:
  "artifact_at (prospective_environment f R a p) None (prospective_syntax f a p)"
  by (simp add: prospective_environment_def pattern_environment_def prospective_syntax_def external_occurrence_syntax_def)

lemma prospective_environment_target:
  "artifact_at (prospective_environment f R a p) (Some [2,4]) R"
  by (auto simp: prospective_environment_def pattern_environment_def)

lemma prospective_environment_binding:
  "binds_slot (prospective_environment f R a p) None [2,4] (Some [2,4])"
  by (auto simp: prospective_environment_def pattern_environment_def rel_dom_def)

lemma prospective_environment_argument_slots:
  "external_slot_values (prospective_environment f R a p) None (3#k) =
    {S. (k,S) \<in> pattern_literal_bindings p}"
  by (auto simp: prospective_environment_def pattern_environment_def)

theorem prospective_environment_recovers:
  assumes anchor: "anchor_formed (R,a)" and pf: "pattern_formed p"
    and addressing: "binder_addressing (pattern_variables p) f"
    and scope: "f ` pattern_variables p \<subseteq> V" and boundary: "V \<subseteq> binder_addresses"
  shows "prospective_call_at (prospective_environment f R a p) None V []
    (Some [2,4],a) (rename_pattern f p) (prospective_interior p) (prospective_slots p)"
  by (rule prospective_syntax_recovers[OF pf addressing scope boundary
        prospective_environment_formed[OF anchor pf addressing] prospective_environment_source
        _ prospective_environment_binding prospective_environment_target anchor])
     (simp add: prospective_environment_argument_slots)

lemma prospective_environment_closed:
  assumes "environment_formed (prospective_environment f R a p)"
  shows "environment_closed (prospective_environment f R a p) {None} ((\<lambda>k. (None,k)) ` prospective_slots p)"
proof -
  let ?q = "Pattern_Pair (Pattern_Target (Occurrence_Anchor (R,a))) p"
  have domain: "rel_dom (pattern_literal_bindings ?q) = prospective_slots p"
    by (simp only: pattern_literal_slots prospective_slots_def) auto
  have closed: "environment_closed (prospective_environment f R a p) {None}
    ((\<lambda>k. (None,k)) ` rel_dom (pattern_literal_bindings ?q))"
    using literal_environment_closed[of "pattern_syntax f ?q" "pattern_literal_bindings ?q"] assms
    by (simp add: prospective_environment_def pattern_environment_def)
  show ?thesis using closed domain by simp
qed

theorem prospective_pattern_representation_total:
  assumes anchor: "anchor_formed (R,a)" and pf: "pattern_formed p"
  shows "\<exists>f. binder_addressing (pattern_variables p) f \<and>
    prospective_call_at (prospective_environment f R a p) None (f ` pattern_variables p) []
      (Some [2,4],a) (rename_pattern f p) (prospective_interior p) (prospective_slots p) \<and>
    environment_closed (prospective_environment f R a p) {None} ((\<lambda>k. (None,k)) ` prospective_slots p) \<and>
    rra_carrier (object_structure (prospective_syntax f a p)) =
      prospective_interior p \<union> prospective_slots p \<union> f ` pattern_variables p"
proof -
  obtain f where addressing: "binder_addressing (pattern_variables p) f"
    using binder_addressing_exists[OF pattern_variables_finite, of p] by blast
  have boundary: "f ` pattern_variables p \<subseteq> binder_addresses"
    using addressing by (simp add: binder_addressing_def)
  have call: "prospective_call_at (prospective_environment f R a p) None (f ` pattern_variables p) []
    (Some [2,4],a) (rename_pattern f p) (prospective_interior p) (prospective_slots p)"
    by (rule prospective_environment_recovers[OF anchor pf addressing _ boundary]) simp
  have closed: "environment_closed (prospective_environment f R a p) {None} ((\<lambda>k. (None,k)) ` prospective_slots p)"
    by (rule prospective_environment_closed[OF prospective_environment_formed[OF anchor pf addressing]])
  show ?thesis using addressing call closed prospective_syntax_carrier[OF addressing, of a] by blast
qed

text \<open>
  The callee address is a finite opaque operand in the citation leaf. The raw
  code contains no target artifact value or use identifier. Its environment
  supplies the actual callee use and formed target anchor, so this constructor
  can be used while assembling mutually referring finite definitions. The
  argument remains a generic pattern over its explicit shared binder boundary.
\<close>

end
