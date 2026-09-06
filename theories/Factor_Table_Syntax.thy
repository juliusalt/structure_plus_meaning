theory Factor_Table_Syntax
  imports Factor_Table_Assembly Factor_Reference_Forests
begin

section \<open>Constructing a complete native table from private row syntax\<close>

locale table_syntax_construction =
  fixes qs :: "('k \<times> 'v) list" and code :: "('k \<times> 'v) \<Rightarrow> exact_artifact"
    and interior slots :: "('k \<times> 'v) \<Rightarrow> local_address set"
    and row_literals :: "('k \<times> 'v) \<Rightarrow> (local_address \<times> exact_artifact) set"
    and row_callees :: "('k \<times> 'v) \<Rightarrow> (local_address \<times> 'u definition_site) set"
  assumes keys: "distinct (map fst qs)"
    and formed: "\<forall>q\<in>set qs. exact_formed (code q)"
    and counts: "\<forall>q\<in>set qs. bag_count (object_data (code q)) = (\<lambda>_. 0)"
    and roots: "\<forall>q\<in>set qs. [] \<in> rra_carrier (object_structure (code q))"
    and cover: "\<forall>q\<in>set qs. rra_carrier (object_structure (code q)) = interior q \<union> slots q"
    and separate: "\<forall>q\<in>set qs. interior q \<inter> slots q = {}"
    and profiles: "\<forall>q\<in>set qs. reference_table_formed (row_literals q) (row_callees q)"
    and domains: "\<forall>q\<in>set qs. slots q=rel_dom (row_literals q) \<union> rel_dom (row_callees q)"
begin

abbreviation children where "children \<equiv> map code qs"
abbreviation interiors where "interiors \<equiv> map interior qs"
abbreviation boundaries where "boundaries \<equiv> map slots qs"
abbreviation copied_interiors where "copied_interiors \<equiv>
  map (\<lambda>i. syntax_branch i ` (interior (qs!i))) [0..<length qs]"
abbreviation copied_slots where "copied_slots \<equiv>
  map (\<lambda>i. syntax_branch i ` (slots (qs!i))) [0..<length qs]"

sublocale frame: syntax_family_construction children
  by (rule syntax_family_construction.intro) (use formed counts roots in auto)

abbreviation framed where "framed \<equiv> frame.framed"
abbreviation literals where "literals \<equiv> syntax_forest_table (map row_literals qs)"
abbreviation callees where "callees \<equiv> syntax_forest_table (map row_callees qs)"
abbreviation table_interior where "table_interior \<equiv>
  insert [] (set frame.ports \<union> syntax_forest_positions interiors)"
abbreviation table_slots where "table_slots \<equiv> syntax_forest_positions boundaries"

lemma reference_table: "reference_table_formed literals callees"
  by (rule reference_table_forest) (use profiles in auto)

lemma reference_domain: "rel_dom literals \<union> rel_dom callees=table_slots"
  by (simp only: syntax_forest_table_domain)
     (use domains in \<open>auto simp: syntax_forest_positions_def\<close>)

lemma reference_range: "rel_ran callees = (\<Union>q\<in>set qs. rel_ran (row_callees q))"
  by (simp add: syntax_forest_table_range)

lemma body_carrier: "rra_carrier (object_structure frame.body) =
    syntax_forest_positions interiors \<union> table_slots"
  by (rule syntax_forest_carrier_partition) (use cover in auto)

lemma carrier: "rra_carrier (object_structure framed) = table_interior \<union> table_slots"
  by (simp only: frame.carrier frame.member_domain body_carrier) blast

lemma reference_bounds: "rel_dom literals \<union> rel_dom callees \<subseteq> rra_carrier (object_structure framed)"
  by (simp only: reference_domain carrier) blast

lemma copied_interior_union: "\<Union>(set copied_interiors) = syntax_forest_positions interiors"
  by (auto simp: syntax_forest_positions_def)

lemma copied_slot_union: "\<Union>(set copied_slots) = table_slots"
  by (auto simp: syntax_forest_positions_def)

lemma body_separate: "syntax_forest_positions interiors \<inter> table_slots = {}"
  by (rule syntax_forest_positions_disjoint) (use separate in auto)

lemma header_separate: "insert [] (set frame.ports) \<inter> syntax_forest_positions interiors = {}"
  using frame.headers_fresh by (simp only: frame.member_domain body_carrier) blast

lemma boundary: "table_interior \<inter> table_slots = {}"
  using frame.headers_fresh body_separate by (simp only: frame.member_domain body_carrier) blast

lemma copied_separate:
  "\<forall>i<length qs. \<forall>j<length qs. i\<noteq>j \<longrightarrow> copied_interiors!i \<inter> copied_interiors!j = {}"
proof (intro allI impI)
  fix i j assume i: "i < length qs" and j: "j < length qs" and different: "i\<noteq>j"
  have disjoint: "range (syntax_branch i) \<inter> range (syntax_branch j) = {}"
    by (rule syntax_branch_disjoint[OF different])
  show "copied_interiors!i \<inter> copied_interiors!j = {}" using i j disjoint by auto
qed

theorem recovers:
  assumes ef: "environment_formed E" and art: "artifact_at E u framed"
    and row_reads: "\<forall>i<length qs. read (syntax_branch i []) (qs!i)
      (syntax_branch i ` interior (qs!i)) (syntax_branch i ` slots (qs!i))"
    and unique: "\<And>a q I K z J A. read a q I K \<Longrightarrow> read a z J A \<Longrightarrow> q=z \<and> I=J \<and> K=A"
  shows "native_table_at E u [] read (set qs) table_interior table_slots"
proof -
  interpret indexed: indexed_native_table E u framed "[]" frame.ports frame.nodes qs copied_interiors copied_slots read
  proof (rule indexed_native_table.intro)
    show "environment_formed E" by (rule ef)
    show "artifact_at E u framed" by (rule art)
    show "family_at framed [] (set (zip frame.ports frame.nodes))" by (rule frame.family_read)
    show "length frame.ports=length qs" "length frame.nodes=length qs"
      "length copied_interiors=length qs" "length copied_slots=length qs" by simp_all
    show "distinct frame.ports" by simp
    show "distinct (map fst qs)" by (rule keys)
    show "\<forall>i<length qs. read (frame.nodes!i) (qs!i) (copied_interiors!i) (copied_slots!i)"
      using row_reads by simp
    show "\<And>a q I K z J A. read a q I K \<Longrightarrow> read a z J A \<Longrightarrow> q=z \<and> I=J \<and> K=A"
      by (rule unique; assumption)
    show "\<forall>i<length qs. \<forall>j<length qs. i\<noteq>j \<longrightarrow> copied_interiors!i \<inter> copied_interiors!j = {}"
      by (rule copied_separate)
    show "insert [] (set frame.ports) \<inter> \<Union>(set copied_interiors) = {}"
      by (simp only: copied_interior_union header_separate)
    show "insert [] (set frame.ports \<union> \<Union>(set copied_interiors)) \<inter> \<Union>(set copied_slots) = {}"
      by (simp only: copied_interior_union copied_slot_union boundary)
  qed
  show ?thesis using indexed.recovers by (simp only: copied_interior_union copied_slot_union)
qed

end

text \<open>
  The family constructor determines both reference tables from the complete row
  list. Its slot domain is exactly their union. All other carrier positions
  belong to the recovered table interior. Empty and nonempty tables use the
  same geometry; neither order nor additional payloads are stored to select
  row meanings.
\<close>

end
