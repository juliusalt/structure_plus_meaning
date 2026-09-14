theory Complete_Child_Assignments
  imports Finite_Bijective_Relations
begin

definition child_assignment_relation where
  "child_assignment_relation M P child={(s,H). H\<in>P \<and> (\<exists>d. (s,d)\<in>M \<and> child d H)}"

lemma child_assignment_relation_member:
  "(s,H)\<in>child_assignment_relation M P child \<longleftrightarrow>
    H\<in>P \<and> (\<exists>d. (s,d)\<in>M \<and> child d H)"
  by (simp only: child_assignment_relation_def mem_Collect_eq case_prod_conv)

lemma child_assignment_relation_image:
  assumes related: "\<And>d H. H\<in>P \<Longrightarrow> child d H=other d (f H)"
  shows "map_relation_values f (child_assignment_relation M P child)=
    child_assignment_relation M (f ` P) other"
proof -
  have at: "(s,K)\<in>map_relation_values f (child_assignment_relation M P child) \<longleftrightarrow>
    (s,K)\<in>child_assignment_relation M (f ` P) other" for s K
  proof
    assume "(s,K)\<in>map_relation_values f (child_assignment_relation M P child)"
    then obtain H d where member: "H\<in>P" and row: "(s,d)\<in>M"
      and read: "child d H" and encoded: "K=f H"
      by (auto simp only: map_relation_values_member child_assignment_relation_member)
    have actual: "other d (f H)" using read related[OF member, of d] by blast
    show "(s,K)\<in>child_assignment_relation M (f ` P) other"
      using member row actual encoded by (auto simp: child_assignment_relation_member)
  next
    assume "(s,K)\<in>child_assignment_relation M (f ` P) other"
    then obtain H d where member: "H\<in>P" and row: "(s,d)\<in>M"
      and read: "other d K" and encoded: "K=f H"
      by (auto simp: child_assignment_relation_member)
    have original: "child d H" using read related[OF member, of d] encoded by simp
    show "(s,K)\<in>map_relation_values f (child_assignment_relation M P child)"
      using member row original encoded by (auto simp: map_relation_values_member child_assignment_relation_member)
  qed
  show ?thesis using at by (auto simp: set_eq_iff split_paired_All)
qed

theorem complete_child_assignment_graph:
  assumes rows: "single_valued M"
    and unique: "\<And>d H K. child d H \<Longrightarrow> child d K \<Longrightarrow> H=K"
  shows "(\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
      (\<forall>s d. (s,d)\<in>M \<longrightarrow> child d (g s))) \<longleftrightarrow>
    (\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
      child_assignment_relation M P child=graph_map (rel_dom M) g)"
proof
  assume "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow> child d (g s))"
  then obtain g where injective: "inj_on g (rel_dom M)" and range: "g ` rel_dom M=P"
    and children: "\<forall>s d. (s,d)\<in>M \<longrightarrow> child d (g s)" by blast
  have graph: "child_assignment_relation M P child=graph_map (rel_dom M) g"
    using children range unique
    by (auto simp: child_assignment_relation_def graph_map_def rel_dom_def; blast)
  show "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
    child_assignment_relation M P child=graph_map (rel_dom M) g"
    using injective range graph by blast
next
  assume "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
    child_assignment_relation M P child=graph_map (rel_dom M) g"
  then obtain g where injective: "inj_on g (rel_dom M)" and range: "g ` rel_dom M=P"
    and graph: "child_assignment_relation M P child=graph_map (rel_dom M) g" by blast
  have children: "child d (g s)" if member: "(s,d)\<in>M" for s d
  proof -
    have key: "s\<in>rel_dom M" using member by (simp only: rel_dom_def; blast)
    have related: "(s,g s)\<in>child_assignment_relation M P child"
      by (simp only: graph graph_map_member key simp_thms)
    obtain e where actual: "(s,e)\<in>M" "child e (g s)"
      using related by (simp only: child_assignment_relation_member; blast)
    have "e=d" by (rule single_valued_outputs[OF rows actual(1) member])
    then show ?thesis using actual(2) by simp
  qed
  show "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=P \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow> child d (g s))"
    using injective range children by blast
qed

text \<open>
  The required socket relation and complete child-encoded domain are independent
  inputs. When each endpoint has one possible child encoded, its actual relation
  is the complete injective assignment exactly when that assignment exists.
  Empty families obey the same equation. Uniqueness is an explicit premise.
\<close>

end
