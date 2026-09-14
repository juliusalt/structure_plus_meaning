theory Generation_Structures
  imports Bootstrap_Relations "HOL-Library.FSet"
begin

datatype 't generation_structure =
  Generation
    (generation_locus: 't)
    (generation_predecessors: "'t generation_structure fset")
    (generation_payload: 't)
    (generation_cause: 't)

lemma generation_identity:
  "G = H \<longleftrightarrow>
    generation_locus G = generation_locus H \<and>
    generation_predecessors G = generation_predecessors H \<and>
    generation_payload G = generation_payload H \<and>
    generation_cause G = generation_cause H"
  by (cases G; cases H) auto

definition predecessor_edges :: "('t generation_structure \<times> 't generation_structure) set" where
  "predecessor_edges = {(H,G). H \<in> fset (generation_predecessors G)}"

lemma predecessor_size_decreases:
  assumes "(H,G) \<in> predecessor_edges"
  shows "size H < size G"
proof (cases G)
  case (Generation l P p c)
  have member: "H \<in> fset P" using assms Generation by (simp add: predecessor_edges_def)
  have bound: "Suc (size H) \<le> (\<Sum>K\<in>fset P. Suc (size K))"
    by (rule member_le_sum[OF member]) simp_all
  show ?thesis using bound by (simp add: Generation)
qed

lemma predecessor_ancestry_decreases:
  assumes "(H,G) \<in> predecessor_edges\<^sup>+"
  shows "size H < size G"
  using assms
  by (induction rule: trancl_induct)
     (auto dest: predecessor_size_decreases intro: less_trans)

lemma predecessor_acyclic:
  "acyclic_edges predecessor_edges"
  using predecessor_ancestry_decreases
  by (auto simp: acyclic_edges_def)

lemma predecessor_well_founded:
  "wf predecessor_edges"
proof -
  have sub: "predecessor_edges \<subseteq> measure size"
    using predecessor_size_decreases by auto
  show ?thesis by (rule wf_subset[OF wf_measure sub])
qed

text \<open>
  One recursive four-field structure carries generation targets. The original
  exact targets and executable finite targets instantiate this same structure;
  predecessor identity and well-foundedness do not depend on a target encoding.
  Formation, actual artifact recovery, cause validity and historical permission
  remain separate judgments.
\<close>

end
