theory RRA_Generation_References
  imports RRA_Generation
begin

definition generation_predecessor_references where
  "generation_predecessor_references E u r l p c={(v,a). \<exists>M s d.
    generation_fields_at E u r l M p c \<and> (s,d)\<in>M \<and> located_at E u d v a}"

lemma generation_predecessor_references_member:
  "(v,a)\<in>generation_predecessor_references E u r l p c \<longleftrightarrow>
    (\<exists>M s d. generation_fields_at E u r l M p c \<and> (s,d)\<in>M \<and> located_at E u d v a)"
  by (simp only: generation_predecessor_references_def mem_Collect_eq case_prod_conv)

lemma generation_predecessor_references_from_fields:
  assumes fields: "generation_fields_at E u r l M p c"
  shows "(v,a)\<in>generation_predecessor_references E u r l p c \<longleftrightarrow>
    (\<exists>s d. (s,d)\<in>M \<and> located_at E u d v a)"
proof
  assume member: "(v,a)\<in>generation_predecessor_references E u r l p c"
  then obtain N s d where other: "generation_fields_at E u r l N p c"
    and row: "(s,d)\<in>N" and location: "located_at E u d v a"
    by (simp only: generation_predecessor_references_member; blast)
  have same: "M=N" using generation_fields_unique[OF fields other] by blast
  show "\<exists>s d. (s,d)\<in>M \<and> located_at E u d v a" using row location same by blast
next
  assume "\<exists>s d. (s,d)\<in>M \<and> located_at E u d v a"
  then show "(v,a)\<in>generation_predecessor_references E u r l p c"
    using fields by (simp only: generation_predecessor_references_member; blast)
qed

lemma generation_predecessor_references_indexed:
  assumes fields: "generation_fields_at E u r l M p c"
    and rows: "M={(s i,d i) | i. i\<in>I}"
    and locations: "\<And>i. i\<in>I \<Longrightarrow> located_at E u (d i) (v i) (a i)"
  shows "generation_predecessor_references E u r l p c={(v i,a i) | i. i\<in>I}"
proof -
  have formed: "environment_formed E" using generation_fields_formed[OF fields] by blast
  have unique: "located_at E u (d i) w b \<Longrightarrow> i\<in>I \<Longrightarrow> w=v i \<and> b=a i" for i w b
    using located_at_unique[OF formed _ locations] by blast
  show ?thesis
    using locations unique by (auto simp: set_eq_iff generation_predecessor_references_from_fields[OF fields] rows; blast)
qed

end
