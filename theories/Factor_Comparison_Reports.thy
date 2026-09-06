theory Factor_Comparison_Reports
  imports Factor_Program_Changes Factor_Correspondence_Reports
begin

section \<open>Definition boundaries induce complete call boundaries\<close>

definition system_boundary_calls :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow> ('d\<times>factor_term) set" where
  "system_boundary_calls P U={(d,t). d\<in>U \<and> schema_call_formed P d t}"

lemma system_comparison_calls_boundary:
  "system_comparison_calls P Q roots =
    system_boundary_calls P (system_comparison_definitions P Q roots)"
  by (simp add: system_comparison_calls_def system_boundary_calls_def)

lemma system_boundary_calls_projection:
  assumes formed: "schema_system_formed P" and inside: "U\<subseteq>system_definitions P"
  shows "rel_dom (system_boundary_calls P U)=U"
proof
  show "rel_dom (system_boundary_calls P U)\<subseteq>U"
    by (auto simp: system_boundary_calls_def rel_dom_def)
  show "U\<subseteq>rel_dom (system_boundary_calls P U)"
  proof
    fix d assume member: "d\<in>U"
    have actual: "d\<in>system_definitions P" using inside member by blast
    obtain t where call: "schema_call_formed P d t" using schema_call_inhabited[OF formed actual] by blast
    show "d\<in>rel_dom (system_boundary_calls P U)" using member call
      by (auto simp: system_boundary_calls_def rel_dom_def)
  qed
qed

lemma system_boundary_calls_empty:
  assumes "schema_system_formed P" "U\<subseteq>system_definitions P"
  shows "system_boundary_calls P U={} \<longleftrightarrow> U={}"
proof
  assume "system_boundary_calls P U={}"
  then show "U={}" using system_boundary_calls_projection[OF assms] by simp
next
  assume "U={}"
  then show "system_boundary_calls P U={}" by (simp add: system_boundary_calls_def)
qed

section \<open>Structural migration and judgment reports have different carriers\<close>

definition system_report_coverage ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'t,'e,'k) schema_system \<Rightarrow>
    'd set \<Rightarrow> 'e set \<Rightarrow> ('d option\<times>'e option) set \<Rightarrow>
    ('d\<times>factor_term,'e\<times>factor_term) correspondence_reports \<Rightarrow> bool" where
  "system_report_coverage P Q U V M R \<longleftrightarrow>
    schema_system_formed P \<and> schema_system_formed Q \<and>
    U\<subseteq>system_definitions P \<and> V\<subseteq>system_definitions Q \<and>
    correspondence_complete U V M \<and>
    report_coverage (system_boundary_calls P U) (system_boundary_calls Q V) R"

definition system_report_sound ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'t,'e,'k) schema_system \<Rightarrow>
    ('d\<times>factor_term,'e\<times>factor_term) correspondence_reports \<Rightarrow> bool" where
  "system_report_sound P Q R \<longleftrightarrow>
    (\<forall>q\<in>reported_preservation R. \<exists>x y.
      q=(Some x,Some y) \<and> (x\<in>positive_meaning P\<longleftrightarrow>y\<in>positive_meaning Q)) \<and>
    (\<forall>x p i. ((Some x,None),(p,i))\<in>R \<longrightarrow> i) \<and>
    (\<forall>y p i. ((None,Some y),(p,i))\<in>R \<longrightarrow> i)"

lemma system_report_migration_finite:
  assumes "system_report_coverage P Q U V M R"
  shows "finite M"
proof -
  have complete: "correspondence_complete U V M" and formed: "schema_system_formed P" "schema_system_formed Q"
    and inside: "U\<subseteq>system_definitions P" "V\<subseteq>system_definitions Q"
    using assms by (auto simp: system_report_coverage_def)
  have finite: "finite U" "finite V"
    using finite_subset[OF inside(1) system_definitions_finite[OF formed(1)]]
      finite_subset[OF inside(2) system_definitions_finite[OF formed(2)]] by blast+
  show ?thesis by (rule correspondence_complete_finite[OF complete finite])
qed

theorem system_report_every_call:
  assumes complete: "system_report_coverage P Q U V M R"
  shows "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>R}=system_boundary_calls P U"
    and "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>R}=system_boundary_calls Q V"
  using report_coverage_endpoints[of "system_boundary_calls P U" "system_boundary_calls Q V" R] complete
  by (auto simp: system_report_coverage_def)

theorem system_report_interpretation_formed:
  assumes complete: "system_report_coverage P Q U V M R"
    and related: "((d,t),(e,u))\<in>reported_interpretation R"
  shows "d\<in>U \<and> e\<in>V \<and> schema_call_formed P d t \<and> schema_call_formed Q e u"
proof -
  obtain p i where row: "((Some (d,t),Some (e,u)),(p,i))\<in>R"
    using related by (auto simp: reported_interpretation_def correspondence_pairs_def rel_dom_def)
  have left: "(d,t)\<in>system_boundary_calls P U"
    by (subst system_report_every_call(1)[OF complete, symmetric]) (use row in blast)
  have right: "(e,u)\<in>system_boundary_calls Q V"
    by (subst system_report_every_call(2)[OF complete, symmetric]) (use row in blast)
  show ?thesis using left right by (simp add: system_boundary_calls_def)
qed

theorem system_report_preserved:
  assumes complete: "system_report_coverage P Q U V M R" and sound: "system_report_sound P Q R"
    and claimed: "(Some (d,t),Some (e,u))\<in>reported_preservation R"
  shows "((d,t),(e,u))\<in>reported_interpretation R"
    and "schema_call_formed P d t \<and> schema_call_formed Q e u"
    and "(d,t)\<in>positive_meaning P \<longleftrightarrow> (e,u)\<in>positive_meaning Q"
proof -
  show related: "((d,t),(e,u))\<in>reported_interpretation R"
    using claimed by (auto simp: reported_interpretation_def correspondence_pairs_def reported_preservation_def rel_dom_def)
  show "schema_call_formed P d t \<and> schema_call_formed Q e u"
    using system_report_interpretation_formed[OF complete related] by blast
  show "(d,t)\<in>positive_meaning P \<longleftrightarrow> (e,u)\<in>positive_meaning Q"
    using sound claimed by (auto simp: system_report_sound_def)
qed

theorem system_report_empty:
  assumes complete: "system_report_coverage P Q U V M R"
  shows "R={} \<longleftrightarrow> U={} \<and> V={}"
    and "M={} \<longleftrightarrow> U={} \<and> V={}"
  using complete report_coverage_empty[of "system_boundary_calls P U" "system_boundary_calls Q V" R]
    system_boundary_calls_empty[where P=P and U=U] system_boundary_calls_empty[where P=Q and U=V]
    correspondence_complete_empty[of U V M]
  by (auto simp: system_report_coverage_def)

section \<open>Complete preservation and explicit incompatibility are both possible\<close>

definition identity_judgment_reports ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    ('d\<times>factor_term,'d\<times>factor_term) correspondence_reports" where
  "identity_judgment_reports P U p i =
    constant_correspondence_reports ((\<lambda>x. (Some x,Some x)) ` system_boundary_calls P U) p i"

theorem identity_judgment_reports_complete:
  assumes formed: "schema_system_formed P" and inside: "U\<subseteq>system_definitions P"
  shows "system_report_coverage P P U U ((\<lambda>d. (Some d,Some d)) ` U)
    (identity_judgment_reports P U p i)"
  using formed inside diagonal_correspondence_complete[of U]
    constant_reports_coverage[OF diagonal_correspondence_complete[of "system_boundary_calls P U"], of p i]
  by (simp add: system_report_coverage_def identity_judgment_reports_def)

theorem identity_judgment_reports_sound:
  "system_report_sound P P (identity_judgment_reports P U p i)"
  by (auto simp: system_report_sound_def identity_judgment_reports_def constant_correspondence_reports_def
    reported_preservation_def)

definition absent_judgment_reports ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'t,'e,'k) schema_system \<Rightarrow>
    'd set \<Rightarrow> 'e set \<Rightarrow> ('d\<times>factor_term,'e\<times>factor_term) correspondence_reports" where
  "absent_judgment_reports P Q U V =
    constant_correspondence_reports
      (correspondence_completion (system_boundary_calls P U) (system_boundary_calls Q V) {}) False True"

theorem absent_judgment_reports_complete:
  assumes "schema_system_formed P" "schema_system_formed Q"
    "U\<subseteq>system_definitions P" "V\<subseteq>system_definitions Q"
  shows "system_report_coverage P Q U V (correspondence_completion U V {}) (absent_judgment_reports P Q U V)"
  using assms correspondence_completion_complete[of "{}" U V]
    constant_reports_coverage[OF correspondence_completion_complete[of "{}"
      "system_boundary_calls P U" "system_boundary_calls Q V"], of False True]
  by (simp add: system_report_coverage_def absent_judgment_reports_def)

theorem absent_judgment_reports_sound:
  "system_report_sound P Q (absent_judgment_reports P Q U V)"
  by (auto simp: system_report_sound_def absent_judgment_reports_def
    constant_correspondence_reports_def reported_preservation_def)

section \<open>A supplied call-preserving copy gives complete reports\<close>

definition copied_judgment_reports ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'t,'e,'k) schema_system \<Rightarrow>
    'd set \<Rightarrow> 'e set \<Rightarrow> ('d \<Rightarrow> 'e) \<Rightarrow>
    ('d\<times>factor_term,'e\<times>factor_term) correspondence_reports" where
  "copied_judgment_reports P Q U V f =
    {((Some (d,t),Some (f d,t)),(True,False)) |d t. d\<in>U \<and> schema_call_formed P d t} \<union>
    {((None,Some (e,t)),(False,True)) |e t. e\<in>V-f ` U \<and> schema_call_formed Q e t}"

theorem copied_judgment_reports_complete:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
    and inside: "U\<subseteq>system_definitions P" "V\<subseteq>system_definitions Q"
    and mapped: "f ` U\<subseteq>V"
    and calls: "\<And>d t. d\<in>U \<Longrightarrow> schema_call_formed Q (f d) t \<longleftrightarrow> schema_call_formed P d t"
  shows "system_report_coverage P Q U V (correspondence_completion U V ((\<lambda>d. (d,f d)) ` U))
    (copied_judgment_reports P Q U V f)"
proof -
  let ?A="system_boundary_calls P U"
  let ?B="system_boundary_calls Q V"
  let ?J="{((d,t),(f d,t)) |d t. d\<in>U \<and> schema_call_formed P d t}"
  have paired: "?J\<subseteq>?A\<times>?B"
    using mapped calls by (auto simp: system_boundary_calls_def)
  have domain: "rel_dom ?J=?A"
    by (auto simp: rel_dom_def system_boundary_calls_def)
  have range: "rel_ran ?J=system_boundary_calls Q (f ` U)"
    by (auto simp: rel_ran_def system_boundary_calls_def image_iff calls)
  have rows: "rel_dom (copied_judgment_reports P Q U V f)=correspondence_completion ?A ?B ?J"
    by (auto simp: copied_judgment_reports_def rel_dom_def correspondence_completion_def
      domain range system_boundary_calls_def)
  have complete: "correspondence_complete ?A ?B (rel_dom (copied_judgment_reports P Q U V f))"
    using correspondence_completion_complete[OF paired] rows by simp
  have functional: "single_valued (copied_judgment_reports P Q U V f)"
    by (auto simp: copied_judgment_reports_def single_valued_def)
  have structural: "correspondence_complete U V (correspondence_completion U V ((\<lambda>d. (d,f d)) ` U))"
    by (rule correspondence_completion_complete) (use mapped in auto)
  show ?thesis using formed inside complete functional structural
    by (simp add: system_report_coverage_def report_coverage_def)
qed

theorem copied_judgment_reports_sound:
  assumes truth: "\<And>d t. d\<in>U \<Longrightarrow> (f d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  shows "system_report_sound P Q (copied_judgment_reports P Q U V f)"
  using truth by (auto simp: system_report_sound_def copied_judgment_reports_def reported_preservation_def)

lemma copied_judgment_reports_preservation:
  "reported_preservation (copied_judgment_reports P Q U V f) =
    {(Some (d,t),Some (f d,t)) |d t. d\<in>U \<and> schema_call_formed P d t}"
  by (auto simp: copied_judgment_reports_def reported_preservation_def)

lemma copied_judgment_reports_incompatibility:
  "reported_incompatibility (copied_judgment_reports P Q U V f) =
    {(None,Some (e,t)) |e t. e\<in>V-f ` U \<and> schema_call_formed Q e t}"
  by (auto simp: copied_judgment_reports_def reported_incompatibility_def)

text \<open>
  Coverage accounts for every required definition and every argument admitted
  at that definition. Structural rows relate definition sites; judgment rows
  relate complete calls and carry both declaration fields. Neither the
  structural correspondence nor an interpretation alone entails equal truth.

  A preservation declaration must relate two formed calls with equal positive
  truth. A missing counterpart must explicitly declare intentional
  incompatibility. An incompatibility declaration is not a proof of unequal
  truth. A paired interpretation may make no further preservation claim.
  No partition of the four relations is imposed.

  These are specifications of complete comparison reports. The displayed
  identity, absence, and copied-call constructions establish consistency over
  full domains, including infinite call domains. A submitted representation
  and its native checking still need separate adequacy. A set in these
  specifications is not an additional stored infinite certificate or a source
  of semantic authority.
\<close>

end
