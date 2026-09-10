theory Factor_Table_Metadata
  imports Factor_Native_Tables
begin

section \<open>Bindings and premise links use the same complete table geometry\<close>

abbreviation native_binding_table_at where
  "native_binding_table_at E u r V I K \<equiv>
    native_table_at E u r (\<lambda>a q J A. native_application_at E u a (fst q) (snd q) J A) V I K"

abbreviation native_discharge_table_at where
  "native_discharge_table_at E u r D I K \<equiv>
    native_table_at E u r (\<lambda>a q J A. native_site_link_at E u a (fst q) (snd q) J A) D I K"

lemma native_binding_table_properties:
  assumes read: "native_binding_table_at E u r V I K"
  shows "finite V" "single_valued V" "r \<in> I" "finite I" "finite K" "I \<inter> K = {}"
    "\<forall>a t. (a,t) \<in> V \<longrightarrow> a \<in> environment_positions E \<and> term_formed t"
proof -
  have rows: "\<And>a q J A. native_application_at E u a (fst q) (snd q) J A \<Longrightarrow> finite J \<and> finite A"
  proof -
    fix a q J A assume row: "native_application_at E u a (fst q) (snd q) J A"
    show "finite J \<and> finite A" using native_application_properties[OF row] by blast
  qed
  show "finite V" by (rule native_table_properties(1)[OF read]) (rule rows, assumption)
  show "single_valued V" by (rule native_table_properties(2)[OF read]) (rule rows, assumption)
  show "r \<in> I" by (rule native_table_properties(3)[OF read]) (rule rows, assumption)
  show "finite I" by (rule native_table_properties(4)[OF read]) (rule rows, assumption)
  show "finite K" by (rule native_table_properties(5)[OF read]) (rule rows, assumption)
  show "I \<inter> K = {}" by (rule native_table_properties(6)[OF read]) (rule rows, assumption)
  show "\<forall>a t. (a,t) \<in> V \<longrightarrow> a \<in> environment_positions E \<and> term_formed t"
  proof (intro allI impI)
    fix a t assume member: "(a,t) \<in> V"
    obtain b J A where row: "native_application_at E u b a t J A"
      using native_table_row_origin[OF read member] by auto
    show "a \<in> environment_positions E \<and> term_formed t"
      using native_application_target[OF row] native_application_properties[OF row] by blast
  qed
qed

lemma native_discharge_table_properties:
  assumes read: "native_discharge_table_at E u r D I K"
  shows "finite D" "single_valued D" "r \<in> I" "finite I" "finite K" "I \<inter> K = {}"
    "\<forall>s n. (s,n) \<in> D \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E"
proof -
  have rows: "\<And>a q J A. native_site_link_at E u a (fst q) (snd q) J A \<Longrightarrow> finite J \<and> finite A"
  proof -
    fix a q J A assume row: "native_site_link_at E u a (fst q) (snd q) J A"
    show "finite J \<and> finite A" using native_site_link_properties[OF row] by blast
  qed
  show "finite D" by (rule native_table_properties(1)[OF read]) (rule rows, assumption)
  show "single_valued D" by (rule native_table_properties(2)[OF read]) (rule rows, assumption)
  show "r \<in> I" by (rule native_table_properties(3)[OF read]) (rule rows, assumption)
  show "finite I" by (rule native_table_properties(4)[OF read]) (rule rows, assumption)
  show "finite K" by (rule native_table_properties(5)[OF read]) (rule rows, assumption)
  show "I \<inter> K = {}" by (rule native_table_properties(6)[OF read]) (rule rows, assumption)
  show "\<forall>s n. (s,n) \<in> D \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E"
  proof (intro allI impI)
    fix s n assume member: "(s,n) \<in> D"
    obtain b J A where row: "native_site_link_at E u b s n J A"
      using native_table_row_origin[OF read member] by auto
    show "s \<in> environment_positions E \<and> n \<in> environment_positions E"
      using native_site_link_properties[OF row] by blast
  qed
qed

lemma native_binding_table_carrier:
  assumes read: "native_binding_table_at E u r V I K" and art: "artifact_at E u R"
  shows "I \<union> K \<subseteq> rra_carrier (object_structure R)"
  by (rule native_table_carrier[OF read art]; rule native_application_carrier[OF _ art]; assumption)

lemma native_discharge_table_carrier:
  assumes read: "native_discharge_table_at E u r D I K" and art: "artifact_at E u R"
  shows "I \<union> K \<subseteq> rra_carrier (object_structure R)"
  by (rule native_table_carrier[OF read art]; rule native_site_link_carrier[OF _ art]; assumption)

text \<open>
  Binding rows recover the existing site-and-term application syntax. Premise
  rows recover two located sites. Both use the same complete table geometry,
  including injective decoded keys, disjoint interiors, and exposed slots.
  These grammar projections precede the proof-node datatype and derivation.
\<close>

end
