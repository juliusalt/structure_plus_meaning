theory RRA_Generation_Child_Assignments
  imports RRA_Generation_Lists Complete_Child_Assignments
begin

lemma generation_child_value_unique:
  assumes formed: "environment_formed E"
    and first: "\<exists>v a. located_at E u d v a \<and> generation_at E v a G"
    and second: "\<exists>v a. located_at E u d v a \<and> generation_at E v a H"
  shows "G=H"
proof -
  obtain v a where left: "located_at E u d v a" "generation_at E v a G" using first by blast
  obtain w b where right: "located_at E u d w b" "generation_at E w b H" using second by blast
  have same: "v=w \<and> a=b" by (rule located_at_unique[OF formed left(1) right(1)])
  show ?thesis using generation_at_unique[OF left(2)] right(2) same by blast
qed

theorem generation_at_assignment:
  assumes fields: "generation_fields_at E u r l M p c"
  shows "generation_at E u r (Generation l P p c) \<longleftrightarrow>
    (\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=fset P \<and>
      (\<forall>s d. (s,d)\<in>M \<longrightarrow> (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))))"
proof
  assume native: "generation_at E u r (Generation l P p c)"
  obtain l' M' p' c' g where original: "generation_fields_at E u r l' M' p' c'"
    and injective: "inj_on g (rel_dom M')"
    and children: "\<forall>s d. (s,d)\<in>M' \<longrightarrow> (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    and shape: "Generation l P p c=Generation l' (Abs_fset (g ` rel_dom M')) p' c'"
    using native by (cases rule: generation_at.cases) blast
  have same: "l=l' \<and> M=M' \<and> p=p' \<and> c=c'"
    by (rule generation_fields_unique[OF fields original])
  have finite: "finite (g ` rel_dom M')"
    using generation_fields_formed[OF original] by (simp add: rel_dom_image)
  show "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=fset P \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow> (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s)))"
    using injective children shape same finite by (auto simp: Abs_fset_inverse)
next
  assume "\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=fset P \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow> (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s)))"
  then obtain g where injective: "inj_on g (rel_dom M)" and range: "g ` rel_dom M=fset P"
    and children: "\<forall>s d. (s,d)\<in>M \<longrightarrow> (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))" by blast
  have native: "generation_at E u r (Generation l (Abs_fset (g ` rel_dom M)) p c)"
    by (rule generation_at.generation[OF fields injective children])
  show "generation_at E u r (Generation l P p c)"
    using native by (simp only: range fset_inverse)
qed

theorem generation_at_child_relation:
  assumes fields: "generation_fields_at E u r l M p c"
  shows "generation_at E u r (Generation l P p c) \<longleftrightarrow>
    (\<exists>g. inj_on g (rel_dom M) \<and> g ` rel_dom M=fset P \<and>
      child_assignment_relation M (fset P)
        (\<lambda>d H. \<exists>v a. located_at E u d v a \<and> generation_at E v a H)=graph_map (rel_dom M) g)"
proof -
  have formed: "environment_formed E" using generation_fields_formed[OF fields] by blast
  show ?thesis by (simp only: generation_at_assignment[OF fields];
    rule complete_child_assignment_graph[OF generation_fields_keyed[OF fields]];
    rule generation_child_value_unique[OF formed]; assumption)
qed

end
