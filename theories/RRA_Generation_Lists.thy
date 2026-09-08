theory RRA_Generation_Lists
  imports RRA_Generation
begin

section \<open>Complete socket enumerations preserve the recursive reading\<close>

abbreviation generation_child_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> (local_address\<times>local_address) \<Rightarrow>
    generation_core \<Rightarrow> bool" where
  "generation_child_at E u row H \<equiv>
    \<exists>v a. located_at E u (snd row) v a \<and> generation_at E v a H"

lemma generation_fields_keyed:
  assumes "generation_fields_at E u r l M p c"
  shows "single_valued M"
  using assms by (auto simp: generation_fields_at_def family_at_def)

lemma generation_fields_row_addresses:
  assumes fields: "generation_fields_at E u r l M p c" and row: "(s,d)\<in>M"
  shows "octets_formed s \<and> octets_formed d"
proof -
  obtain R pr where source: "environment_formed E" "artifact_at E u R" "family_at R pr M"
    using fields by (auto simp: generation_fields_at_def)
  have exact: "exact_formed R" using source(1,2) by (auto simp: environment_formed_def)
  have positions: "s\<in>rra_carrier (object_structure R)" "d\<in>rra_carrier (object_structure R)"
    using source(3) row by (auto simp: family_at_def headed_incidence_def object_formed_def rra_formed_def)
  show ?thesis using exact positions by (auto simp: exact_formed_def)
qed

theorem generation_at_from_lists:
  assumes fields: "generation_fields_at E u r l M p c"
    and rows: "distinct ms" "set ms=M"
    and children: "list_all2 (generation_child_at E u) ms Hs"
    and separate: "distinct Hs"
  shows "generation_at E u r (Generation l (Abs_fset (set Hs)) p c)"
proof -
  have keys: "distinct (map fst ms)"
    using rows generation_fields_keyed[OF fields] by (simp add: distinct_keys_iff)
  have length: "length (map fst ms)=length Hs"
    using list_all2_lengthD[OF children] by simp
  obtain g where assigned: "inj_on g (set (map fst ms))" "map g (map fst ms)=Hs"
    using distinct_list_rekey[OF length keys separate] by blast
  have domain: "rel_dom M=set (map fst ms)"
    by (simp only: rows(2)[symmetric] rel_dom_image set_map)
  have injective: "inj_on g (rel_dom M)" using assigned(1) by (simp only: domain)
  have range: "image g (rel_dom M)=set Hs"
  proof -
    have "image g (rel_dom M)=set (map g (map fst ms))"
      by (simp only: domain set_map)
    also have "...=set Hs" by (simp only: assigned(2))
    finally show ?thesis .
  qed
  have all: "\<forall>row\<in>set ms. generation_child_at E u row (g (fst row))"
    using children by (simp add: assigned(2)[symmetric] list_all2_map2 list_all2_same)
  have recursion: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
  proof (intro allI impI)
    fix s d assume member: "(s,d)\<in>M"
    have at: "generation_child_at E u (s,d) (g (fst (s,d)))"
      by (rule bspec[OF all]) (use member rows(2) in simp)
    show "\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s)"
      using at by simp
  qed
  have read: "generation_at E u r (Generation l (Abs_fset (image g (rel_dom M))) p c)"
    by (rule generation_at.generation[OF fields injective recursion])
  show ?thesis using read by (simp only: range)
qed

theorem generation_at_to_lists:
  assumes source: "generation_at E u r G"
    and fields: "generation_fields_at E u r l M p c"
    and rows: "distinct ms" "set ms=M"
  shows "l=generation_locus G \<and> p=generation_payload G \<and> c=generation_cause G \<and>
    (\<exists>Hs. distinct Hs \<and> set Hs=fset (generation_predecessors G) \<and>
      list_all2 (generation_child_at E u) ms Hs)"
proof -
  obtain l' M' p' c' g where actual: "generation_fields_at E u r l' M' p' c'"
    and injective: "inj_on g (rel_dom M')"
    and children: "\<forall>s d. (s,d)\<in>M' \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    and core: "G=Generation l' (Abs_fset (image g (rel_dom M'))) p' c'"
    using source by (cases rule: generation_at.cases) blast
  have same: "l=l'" "M=M'" "p=p'" "c=c'"
    using generation_fields_unique[OF fields actual] by blast+
  have keys: "distinct (map fst ms)"
    using rows generation_fields_keyed[OF fields] by (simp add: distinct_keys_iff)
  have domain: "rel_dom M'=set (map fst ms)"
    by (simp only: same(2)[symmetric] rows(2)[symmetric] rel_dom_image set_map)
  let ?Hs="map g (map fst ms)"
  have separate: "distinct ?Hs" using keys injective by (simp only: distinct_map domain; blast)
  have finite: "finite (image g (rel_dom M'))" by (simp add: domain)
  have range: "set ?Hs=fset (generation_predecessors G)"
    using finite by (simp add: core domain Abs_fset_inverse image_image)
  have all: "\<forall>row\<in>set ms. generation_child_at E u row (g (fst row))"
    using children rows(2) same(2) by auto
  have related: "list_all2 (generation_child_at E u) ms ?Hs"
    using all by (simp add: list_all2_map2 list_all2_same)
  show ?thesis using same core separate range related by auto
qed

corollary generation_at_lists:
  assumes fields: "generation_fields_at E u r l M p c"
    and rows: "distinct ms" "set ms=M"
  shows "generation_at E u r (Generation l P p c) \<longleftrightarrow>
    (\<exists>Hs. distinct Hs \<and> set Hs=fset P \<and> list_all2 (generation_child_at E u) ms Hs)"
proof
  assume native: "generation_at E u r (Generation l P p c)"
  show "\<exists>Hs. distinct Hs \<and> set Hs=fset P \<and> list_all2 (generation_child_at E u) ms Hs"
    using generation_at_to_lists[OF native fields rows] by simp
next
  assume "\<exists>Hs. distinct Hs \<and> set Hs=fset P \<and> list_all2 (generation_child_at E u) ms Hs"
  then obtain Hs where children: "distinct Hs" "set Hs=fset P" "list_all2 (generation_child_at E u) ms Hs" by blast
  have read: "generation_at E u r (Generation l (Abs_fset (set Hs)) p c)"
    by (rule generation_at_from_lists[OF fields rows children(3,1)])
  show "generation_at E u r (Generation l P p c)"
    using read by (simp add: children(2) fset_inverse)
qed

text \<open>
  These equations concern the existing generation reading. A list enumerates
  every actual socket row once; the corresponding list contains each exact
  predecessor once. Socket and predecessor distinctness recover precisely
  the injective assignment in the original reading rule. Every complete
  enumeration is available, and the cited use and address remain in each
  recursive reading. No list order becomes part of the generation core.
\<close>

end
