theory Factor_Record_Syntax
  imports RRA_Syntax_Records Factor_Reference_Forests
begin

section \<open>Complete records of independently compiled fields\<close>

locale record_syntax_construction =
  fixes Rs :: "exact_artifact list" and Is Ks :: "local_address set list"
    and Ls :: "(local_address \<times> exact_artifact) set list"
    and Cs :: "(local_address \<times> 'u definition_site) set list"
  assumes formed: "\<forall>R\<in>set Rs. exact_formed R"
    and counts: "\<forall>R\<in>set Rs. bag_count (object_data R)=(\<lambda>_. 0)"
    and roots: "\<forall>R\<in>set Rs. []\<in>rra_carrier (object_structure R)"
    and interior_length: "length Is=length Rs"
    and slot_length: "length Ks=length Rs"
    and literal_length: "length Ls=length Rs"
    and callee_length: "length Cs=length Rs"
    and cover: "\<forall>i<length Rs. rra_carrier (object_structure (Rs!i))=Is!i\<union>Ks!i"
    and separate: "\<forall>i<length Rs. Is!i\<inter>Ks!i={}"
    and domains: "\<forall>i<length Rs. Ks!i=rel_dom (Ls!i)\<union>rel_dom (Cs!i)"
    and profiles: "\<forall>i<length Rs. reference_table_formed (Ls!i) (Cs!i)"
begin

sublocale frame: syntax_family_construction Rs
  by (rule syntax_family_construction.intro[OF formed counts roots])

abbreviation framed where "framed \<equiv> frame.record_framed"
abbreviation interior where "interior \<equiv> insert [] (set frame.ports\<union>syntax_forest_positions Is)"
abbreviation slots where "slots \<equiv> syntax_forest_positions Ks"
abbreviation literals where "literals \<equiv> syntax_forest_table Ls"
abbreviation callees where "callees \<equiv> syntax_forest_table Cs"

lemma reference_table: "reference_table_formed literals callees"
  by (rule reference_table_forest)
     (use profiles literal_length callee_length in auto)

lemma reference_domain: "rel_dom literals\<union>rel_dom callees=slots"
  by (simp only: syntax_forest_table_domain)
     (use domains literal_length callee_length slot_length in \<open>auto simp: syntax_forest_positions_def\<close>)

lemma reference_range: "rel_ran callees=(\<Union>C\<in>set Cs. rel_ran C)"
  by (rule syntax_forest_table_range)

lemma body_carrier:
  "rra_carrier (object_structure frame.body)=syntax_forest_positions Is\<union>slots"
  by (rule syntax_forest_carrier_partition[OF interior_length slot_length cover])

lemma carrier: "rra_carrier (object_structure framed)=interior\<union>slots"
  by (simp only: frame.record_carrier body_carrier) blast

lemma reference_bounds: "rel_dom literals\<union>rel_dom callees\<subseteq>rra_carrier (object_structure framed)"
  by (simp only: reference_domain carrier) blast

lemma body_separate: "syntax_forest_positions Is\<inter>slots={}"
  by (rule syntax_forest_positions_disjoint)
     (use interior_length slot_length separate in auto)

lemma header_separate: "insert [] (set frame.ports)\<inter>syntax_forest_positions Is={}"
  using frame.record_headers_fresh by (simp only: body_carrier) blast

lemma boundary: "interior\<inter>slots={}"
  using frame.record_headers_fresh body_separate by (simp only: body_carrier) blast

lemma child_interior_subset:
  assumes index: "i<length Rs"
  shows "image (syntax_branch i) (Is!i)\<subseteq>syntax_forest_positions Is"
  using index interior_length by (auto simp: syntax_forest_positions_def)

lemma child_header_separate:
  assumes index: "i<length Rs"
  shows "insert [] (set frame.ports)\<inter>image (syntax_branch i) (Is!i)={}"
  using header_separate child_interior_subset[OF index] by blast

lemma child_interiors_separate:
  assumes "i\<noteq>j"
  shows "image (syntax_branch i) (Is!i)\<inter>image (syntax_branch j) (Is!j)={}"
  using syntax_branch_disjoint[OF assms] by blast

lemma child_addressing:
  assumes index: "i<length Rs"
  shows "finite_addressing (rra_carrier (object_structure (Rs!i))) (syntax_branch i)"
  by (rule syntax_branch_addressing) (use formed nth_mem[OF index] in blast)

lemma child_references:
  assumes refs: "syntax_references E u literals callees" and index: "i<length Rs"
  shows "syntax_references E u (map_slot_keys (syntax_branch i) (Ls!i))
    (map_slot_keys (syntax_branch i) (Cs!i))"
proof -
  have li: "i<length Ls" and ci: "i<length Cs" using index literal_length callee_length by simp_all
  show ?thesis by (rule syntax_references_mono[
    OF refs syntax_forest_table_child[OF li] syntax_forest_table_child[OF ci]])
qed

end

text \<open>
  Complete field partitions and reference profiles compose into one record.
  Every interior and exposed slot has a source field, and every field keeps
  its exact local reading inside the record. Native semantic readers supply
  the field interpretations separately.
\<close>

end
