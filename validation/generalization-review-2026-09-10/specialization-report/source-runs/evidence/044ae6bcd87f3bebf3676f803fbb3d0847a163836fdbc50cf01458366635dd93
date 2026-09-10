theory Factor_Definition_Frames
  imports Factor_Schema_Forests
begin

section \<open>A fixed definition root enclosing independent interface and clause scopes\<close>

definition definition_wrapper ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address list \<Rightarrow> exact_artifact" where
  "definition_wrapper R r S rs =
    record_wrapper (family_wrapper (syntax_union R S) [1,0]
      (set (zip (family_ports (length rs)) (map (Cons 3) rs))))
      [] [[0,0],[0,1]] [2#r,[1,0]]"

locale definition_frame =
  fixes R S :: exact_artifact and r :: local_address and rs :: "local_address list"
  assumes interface_formed: "exact_formed R" and clauses_formed: "exact_formed S"
    and interface_counts: "bag_count (object_data R) = (\<lambda>_. 0)"
    and clause_counts: "bag_count (object_data S) = (\<lambda>_. 0)"
    and interface_root: "r \<in> rra_carrier (object_structure R)"
    and clause_roots: "set rs \<subseteq> rra_carrier (object_structure S)"
begin

abbreviation body where "body \<equiv> syntax_union R S"
abbreviation ports where "ports \<equiv> family_ports (length rs)"
abbreviation members where "members \<equiv> set (zip ports (map (Cons 3) rs))"
abbreviation family_body where "family_body \<equiv> family_wrapper body [1,0] members"
abbreviation framed where "framed \<equiv> definition_wrapper R r S rs"

lemma body_formed: "exact_formed body" by (rule syntax_union_formed[OF interface_formed clauses_formed])

lemma member_domain: "rel_dom members = set ports" by (rule zip_domain) simp
lemma member_range: "rel_ran members = Cons 3 ` set rs" using zip_range[of ports "map (Cons 3) rs"] by simp
lemma members_finite: "finite members" by simp
lemma members_functional: "single_valued members" by (rule single_valued_zip) simp

lemma endpoints_inside: "rel_ran members \<subseteq> rra_carrier (object_structure body)"
  using clause_roots by (auto simp: member_range syntax_union_def)

lemma interface_inside: "2#r \<in> rra_carrier (object_structure body)"
  using interface_root by (auto simp: syntax_union_def)

lemma family_fresh: "insert [1,0] (rel_dom members) \<inter> rra_carrier (object_structure body) = {}"
  by (simp only: member_domain) (auto simp: syntax_union_def family_ports_def)

lemma family_separate: "[1,0] \<notin> rel_dom members"
  by (simp only: member_domain) (auto simp: family_ports_def)

lemma family_addresses: "\<forall>a\<in>insert [1,0] (rel_dom members \<union> rel_ran members). octets_formed a"
proof -
  have targets: "\<forall>a\<in>rel_ran members. octets_formed a"
    using endpoints_inside body_formed by (auto simp: exact_formed_def)
  show ?thesis using targets family_ports_formed[of "length rs"]
    by (auto simp: member_domain octets_formed_def)
qed

lemma family_formed: "exact_formed family_body"
  by (rule family_wrapper_formed[OF body_formed members_finite family_addresses])

lemma family_carrier:
  "rra_carrier (object_structure family_body) =
    rra_carrier (object_structure body) \<union> {[1,0]} \<union> set ports"
  using endpoints_inside by (auto simp: family_wrapper_def attach_structure_def family_object_def member_domain)

lemma family_read: "family_at family_body [1,0] members"
  by (rule family_wrapper_fresh_recovers[OF body_formed family_formed members_finite members_functional
      family_separate family_fresh])

lemma family_reads: "object_reads_agree body family_body (rra_carrier (object_structure body))"
  by (rule family_wrapper_reads) (use family_fresh in blast)

lemma record_fresh:
  "insert [] (set [[0,0],[0,1]]) \<inter> rra_carrier (object_structure family_body) = {}"
  by (simp only: family_carrier) (auto simp: syntax_union_def family_ports_def)

lemma formed: "exact_formed framed"
proof -
  have roots: "set [2#r,[1,0]] \<subseteq> rra_carrier (object_structure family_body)"
    by (simp only: family_carrier) (use interface_inside in auto)
  have headers: "\<forall>a\<in>insert [] (set [[0,0],[0,1]]). octets_formed a"
    by (auto simp: octets_formed_def)
  show ?thesis unfolding definition_wrapper_def
    by (rule record_wrapper_formed[OF family_formed roots headers])
qed

lemma object_formed: "object_formed framed" using formed by (simp add: exact_formed_def)

lemma record_read: "record_at framed [] [[0,0],[0,1]] [2#r,[1,0]]"
  unfolding definition_wrapper_def
  by (rule record_wrapper_recovers[OF family_formed _ _ _ record_fresh])
     (use formed in \<open>auto simp: definition_wrapper_def\<close>)

lemma record_reads: "object_reads_agree family_body framed (rra_carrier (object_structure family_body))"
  unfolding definition_wrapper_def by (rule record_wrapper_reads[OF record_fresh])

lemma body_reads: "object_reads_agree body framed (rra_carrier (object_structure body))"
  by (rule object_reads_agree_extend[OF family_reads record_reads])

lemma interface_reads:
  "object_reads_agree (push_object (Cons 2) R) framed (Cons 2 ` rra_carrier (object_structure R))"
  by (rule object_reads_agree_extend[OF syntax_union_reads_left[OF interface_counts] body_reads])

lemma clause_reads:
  "object_reads_agree (push_object (Cons 3) S) framed (Cons 3 ` rra_carrier (object_structure S))"
  by (rule object_reads_agree_extend[OF syntax_union_reads_right[OF clause_counts] body_reads])

lemma clauses_read: "family_at framed [1,0] members"
  by (rule family_at_read_transport[OF family_read object_formed record_reads])
     (simp only: member_domain family_carrier, auto)

lemma carrier:
  "rra_carrier (object_structure framed) =
    Cons 2 ` rra_carrier (object_structure R) \<union> Cons 3 ` rra_carrier (object_structure S) \<union>
    {[],[0,0],[0,1],[1,0]} \<union> set ports"
  by (simp only: definition_wrapper_def record_wrapper_def attach_structure_def
      structured_object.select_convs rra_structure.select_convs family_carrier)
     (use interface_root in \<open>auto simp: record_structure_def syntax_union_def\<close>)

lemma no_counts: "bag_count (object_data framed) = (\<lambda>_. 0)"
  by (simp add: definition_wrapper_def record_wrapper_def family_wrapper_def attach_structure_def)

lemma root_inside: "[] \<in> rra_carrier (object_structure framed)" by (simp add: carrier)

end

section \<open>Recovering a complete identified clause family\<close>

lemma native_schema_family_from_list:
  assumes ef: "environment_formed E" and source: "artifact_at E u R"
    and raw: "family_at R m (set (zip ss rs))"
    and lengths: "length ss = length rs" "length ss = length As"
    and distinct: "distinct ss"
    and bodies: "\<forall>i<length As. native_schema_at E u (rs!i) (As!i)"
  shows "native_schema_family_at E u m (set (zip ss As))"
proof -
  have finite: "finite (set (zip ss As))" by simp
  have functional: "single_valued (set (zip ss As))" by (rule single_valued_zip[OF distinct])
  have domain: "rel_dom (set (zip ss As)) = rel_dom (set (zip ss rs))"
    by (simp only: zip_domain[OF lengths(1)] zip_domain[OF lengths(2)])
  have readings: "\<forall>s a. (s,a) \<in> set (zip ss rs) \<longrightarrow>
    (\<exists>A. (s,A) \<in> set (zip ss As) \<and> native_schema_at E u a A)"
  proof (intro allI impI)
    fix s a assume entry: "(s,a) \<in> set (zip ss rs)"
    obtain i where index: "i < length ss" "i < length rs" "s=ss!i" "a=rs!i"
      using entry by (auto simp: in_set_zip)
    have small: "i < length As" using index(1) lengths(2) by simp
    have projected: "(s,As!i) \<in> set (zip ss As)"
      using index(1,3) small by (auto simp: in_set_zip)
    have read: "native_schema_at E u a (As!i)" using bodies small index(4) by blast
    show "\<exists>A. (s,A) \<in> set (zip ss As) \<and> native_schema_at E u a A"
      using projected read by blast
  qed
  show ?thesis using ef source raw finite functional domain readings
    unfolding native_schema_family_at_def by blast
qed

text \<open>
  The enclosing root is fixed before any callee environment is constructed.
  Interface syntax occupies one disjoint copy and complete clause syntax
  another. The only added occurrences are the definition record, the clause
  family root, and its complete identified sockets. Their coordinates are
  construction choices; the native readers recognize their incidence geometry.
\<close>

end
