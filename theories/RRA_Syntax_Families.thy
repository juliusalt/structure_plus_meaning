theory RRA_Syntax_Families
  imports RRA_Syntax_Composition RRA_Syntax_Forests
begin

section \<open>A complete family header over disjoint child copies\<close>

locale syntax_family_construction =
  fixes Rs :: "exact_artifact list"
  assumes children_formed: "\<forall>R\<in>set Rs. exact_formed R"
    and children_counts: "\<forall>R\<in>set Rs. bag_count (object_data R) = (\<lambda>_. 0)"
    and children_roots: "\<forall>R\<in>set Rs. [] \<in> rra_carrier (object_structure R)"
begin

abbreviation body where "body \<equiv> syntax_forest Rs"
abbreviation ports where "ports \<equiv> family_ports (length Rs)"
abbreviation nodes where "nodes \<equiv> map (\<lambda>i. syntax_branch i []) [0..<length Rs]"
abbreviation members where "members \<equiv> set (zip ports nodes)"
abbreviation framed where "framed \<equiv> family_wrapper body [] members"

lemma body_formed: "exact_formed body" by (rule syntax_forest_formed[OF children_formed])

lemma member_domain: "rel_dom members = set ports" by (rule zip_domain) simp
lemma member_range: "rel_ran members = set nodes" by (rule zip_range) simp

lemma nodes_inside: "set nodes \<subseteq> rra_carrier (object_structure body)"
proof
  fix a assume member: "a \<in> set nodes"
  obtain i where index: "i < length Rs" "a=syntax_branch i []" using member by auto
  have root: "[] \<in> rra_carrier (object_structure (Rs!i))"
    using children_roots nth_mem[OF index(1)] by blast
  show "a \<in> rra_carrier (object_structure body)"
    using syntax_forest_child_inside[OF index(1) root] index(2) by simp
qed

lemma headers_fresh: "insert [] (rel_dom members) \<inter> rra_carrier (object_structure body) = {}"
  by (simp only: member_domain) (auto dest!: family_ports_shape)

lemma headers_separate: "[] \<notin> rel_dom members"
  by (simp only: member_domain) (auto dest!: family_ports_shape)

lemma member_addresses: "\<forall>a\<in>insert [] (rel_dom members \<union> rel_ran members). octets_formed a"
proof -
  have targets: "\<forall>a\<in>rel_ran members. octets_formed a"
    using nodes_inside body_formed by (auto simp: member_range exact_formed_def)
  show ?thesis using targets family_ports_formed[of "length Rs"]
    by (simp only: member_domain) (auto simp: octets_formed_def)
qed

lemma formed: "exact_formed framed"
  by (rule family_wrapper_formed[OF body_formed _ member_addresses]) simp

lemma family_read: "family_at framed [] members"
  by (rule family_wrapper_fresh_recovers[OF body_formed formed _ _ headers_separate headers_fresh])
     (simp_all add: single_valued_zip)

lemma reads: "object_reads_agree body framed (rra_carrier (object_structure body))"
  by (rule family_wrapper_reads) (use headers_fresh in blast)

lemma child_reads:
  assumes index: "i < length Rs"
  shows "object_reads_agree (push_object (syntax_branch i) (Rs!i)) framed
    (syntax_branch i ` rra_carrier (object_structure (Rs!i)))"
  by (rule object_reads_agree_extend[OF syntax_forest_child_reads[OF children_formed children_counts index] reads])

lemma child_citation:
  assumes index: "i < length Rs" and cite: "citation_at (Rs!i) r c I"
  shows "citation_at framed (syntax_branch i r) (map_citation_positions (syntax_branch i) c)
    (syntax_branch i ` I)"
  by (rule citation_at_copy_into[OF cite formed
      syntax_branch_addressing child_reads[OF index]])
     (use children_formed nth_mem[OF index] in blast)

lemma carrier:
  "rra_carrier (object_structure framed) = insert [] (rel_dom members \<union> rra_carrier (object_structure body))"
  using nodes_inside by (auto simp: family_wrapper_def attach_structure_def family_object_def member_range)

lemma counts: "bag_count (object_data framed) = (\<lambda>_. 0)"
  by (simp add: family_wrapper_def attach_structure_def)

lemma root: "[] \<in> rra_carrier (object_structure framed)"
  by (simp add: carrier)

end

text \<open>
  Each child receives a private structural copy. The family header contains one
  socket per list position and adds no other carrier positions. The list chooses
  a construction layout; the resulting family is read through its complete
  incidence graph, whose sockets distinguish occurrences. The positions of the
  copied children, and their partitions, are the forest's (RRA_Syntax_Forests).
\<close>

end
