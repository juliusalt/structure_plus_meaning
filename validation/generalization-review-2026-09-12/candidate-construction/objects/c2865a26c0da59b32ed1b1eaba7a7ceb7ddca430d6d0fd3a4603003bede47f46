theory RRA_Collection_Selections
  imports RRA_Collection_References RRA_Selection
begin

section \<open>Recovering selections from the constructed citation families\<close>

lemma target_selection_from_injective_family:
  assumes ef: "environment_formed E" and source: "artifact_at E u R"
    and family: "family_at R r M" and injective: "inj_on h (rel_dom M)"
    and targets: "\<And>s a. (s,a)\<in>M \<Longrightarrow> anchored_at E u a (h s)"
  shows "target_selection_at E u r (image h (rel_dom M))"
proof -
  let ?K="graph_map (rel_dom M) h"
  have anchors: "anchor_family_at E u r ?K"
    using ef source family targets unfolding anchor_family_at_def by blast
  have unique: "inj_on snd ?K"
    using injective by (auto simp: graph_map_def inj_on_def)
  have image: "rel_ran ?K=image h (rel_dom M)"
    by (auto simp: rel_ran_def graph_map_def)
  show ?thesis using anchors unique image unfolding target_selection_at_def by blast
qed

context collection_record_frame
begin

lemma target_selection:
  assumes ef: "environment_formed E" and source: "artifact_at E u (collection_record_syntax xss)"
    and field: "j<length xss" and different: "distinct (xss!j)"
    and targets: "\<And>i. i<length (xss!j) \<Longrightarrow>
      anchored_at E u (collection_field_node j i) (xss!j!i)"
  shows "target_selection_at E u (syntax_branch j []) (set (xss!j))"
proof -
  let ?n="length (xss!j)"
  let ?g="\<lambda>i. xss!j!i"
  let ?M="collection_field_members j ?n"
  have injective: "inj_on ?g {..<?n}" by (rule inj_on_nth[OF different]) simp
  obtain h where assignment: "inj_on h (rel_dom ?M)"
    "\<forall>i<?n. h (collection_field_socket j ?n i)=?g i"
    "image h (rel_dom ?M)=image ?g {..<?n}"
    using collection_field_assignment[OF injective, where j=j] by blast
  have refs: "\<And>s a. (s,a)\<in>?M \<Longrightarrow> anchored_at E u a (h s)"
  proof -
    fix s a assume edge: "(s,a)\<in>?M"
    obtain i where index: "i<?n" and s: "s=collection_field_socket j ?n i"
      and a: "a=collection_field_node j i" using edge by (auto simp: collection_field_member)
    have same: "h s=?g i" using assignment(2) index s by simp
    show "anchored_at E u a (h s)" using targets[OF index] by (simp only: a same)
  qed
  have selected: "target_selection_at E u (syntax_branch j []) (image h (rel_dom ?M))"
    by (rule target_selection_from_injective_family[OF ef source field_family[OF field] assignment(1) refs])
  have contents: "image h (rel_dom ?M)=set (xss!j)" using assignment(3) by (auto simp: set_conv_nth)
  show ?thesis using selected contents by simp
qed

lemma generation_selection:
  assumes ef: "environment_formed E" and source: "artifact_at E u (collection_record_syntax xss)"
    and field: "j<length xss" and different: "distinct gs" and length: "length gs=length (xss!j)"
    and members: "set gs=fset S"
    and refs: "\<And>i. i<length gs \<Longrightarrow>
      located_at E u (collection_field_node j i) (v i) (a i) \<and> generation_at E (v i) (a i) (gs!i)"
  shows "selection_at E u (syntax_branch j []) S"
proof -
  let ?n="length gs"
  let ?g="\<lambda>i. gs!i"
  let ?M="collection_field_members j ?n"
  have injective: "inj_on ?g {..<?n}" by (rule inj_on_nth[OF different]) simp
  obtain h where assignment: "inj_on h (rel_dom ?M)"
    "\<forall>i<?n. h (collection_field_socket j ?n i)=?g i"
    "image h (rel_dom ?M)=image ?g {..<?n}"
    using collection_field_assignment[OF injective, where j=j] by blast
  have family: "family_at (collection_record_syntax xss) (syntax_branch j []) ?M"
    using field_family[OF field] length by simp
  have locations: "\<forall>s d. (s,d)\<in>?M \<longrightarrow>
      (\<exists>w b. located_at E u d w b \<and> generation_at E w b (h s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d)\<in>?M"
    obtain i where index: "i<?n" and s: "s=collection_field_socket j ?n i"
      and d: "d=collection_field_node j i" using edge by (auto simp: collection_field_member)
    have same: "h s=?g i" using assignment(2) index s by simp
    show "\<exists>w b. located_at E u d w b \<and> generation_at E w b (h s)"
      by (rule exI[of _ "v i"], rule exI[of _ "a i"])
         (use refs[OF index] in \<open>simp only: d same\<close>)
  qed
  have contents: "image h (rel_dom ?M)=fset S" using assignment(3) members by (auto simp: set_conv_nth)
  have recovered: "S=Abs_fset (image h (rel_dom ?M))"
    by (rule fset_inject[THEN iffD1]) (simp add: contents Abs_fset_inverse)
  show ?thesis using ef source family assignment(1) locations recovered unfolding selection_at_def by blast
qed

end

text \<open>
  A generation family follows the supplied occurrence citations and recursively
  recovers the existing cores. A target family reads only its exact target
  values. Each selection requires an injective assignment from the complete
  family sockets, so duplicate entries cannot silently disappear into a set.
\<close>

end
