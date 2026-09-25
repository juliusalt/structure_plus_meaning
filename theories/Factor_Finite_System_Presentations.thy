theory Factor_Finite_System_Presentations
  imports Factor_Finite_System_Unions Factor_Finite_View_Installation Factor_System_Restriction
    Bootstrap_Finite_Closure
begin

section \<open>A program's finite presentation is derived from its parts'\<close>

text \<open>
  A system whose interfaces and clauses lie within those of a formed system is presented exactly by its
  finite presentation, formed or not: a union's parts and a view extension's predecessor are such parts.
  So the presentation of a formed union is the finite union of its parts' presentations, that of a formed
  view extension the finite view extension of its predecessor's, and that of a restriction the finite
  restriction of the restricted program's. A rooted program is the restriction to the closure its finite
  presentation computes, and a formed system agreeing with a formed program on its whole domain is the
  restriction of that program to its domain, so it is presented by the finite restriction of the
  program's presentation: a sub-lineage of a presented program is never presented again.
\<close>

lemma decode_finite_system_of_part:
  assumes formed: "schema_system_formed R"
    and interfaces: "system_interfaces P\<subseteq>system_interfaces R" and clauses: "system_clauses P\<subseteq>system_clauses R"
  shows "decode_finite_system (finite_system_of P)=P"
proof -
  have finite: "finite (system_interfaces P)" "finite (system_clauses P)"
    using formed interfaces clauses by (auto simp: schema_system_formed_def intro: finite_subset)
  have interface: "decode_finite_pattern (finite_pattern_of p)=p" if "(d,p)\<in>system_interfaces P" for d p
  proof -
    have "(d,p)\<in>system_interfaces R" using that interfaces by blast
    then show ?thesis using formed by (auto simp: schema_system_formed_def intro: decode_finite_pattern_of)
  qed
  have clause: "decode_finite_schema (finite_schema_of S)=S" if "(k,S)\<in>system_clauses P" for k S
  proof -
    have "(k,S)\<in>system_clauses R" using that clauses by blast
    then show ?thesis using formed by (cases k) (auto simp: schema_system_formed_def intro: decode_finite_schema_of)
  qed
  have i: "map_relation_values decode_finite_pattern
      (map_relation_values finite_pattern_of (system_interfaces P))=system_interfaces P"
    by (rule map_relation_values_inverse) (erule interface)
  have c: "map_relation_values decode_finite_schema
      (map_relation_values finite_schema_of (system_clauses P))=system_clauses P"
    by (rule map_relation_values_inverse) (erule clause)
  have ifs: "fset (Abs_fset (map_relation_values finite_pattern_of (system_interfaces P)))=
      map_relation_values finite_pattern_of (system_interfaces P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  have cfs: "fset (Abs_fset (map_relation_values finite_schema_of (system_clauses P)))=
      map_relation_values finite_schema_of (system_clauses P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  show ?thesis
    by (rule schema_system.equality)
      (simp_all add: decode_finite_system_def finite_system_of_def ifs cfs i c)
qed

theorem finite_system_of_union:
  assumes formed: "schema_system_formed (system_union P Q)"
  shows "finite_system_of (system_union P Q)=finite_system_union (finite_system_of P) (finite_system_of Q)"
proof -
  have left: "decode_finite_system (finite_system_of P)=P"
    by (rule decode_finite_system_of_part[OF formed]) (simp_all add: system_union_def)
  have right: "decode_finite_system (finite_system_of Q)=Q"
    by (rule decode_finite_system_of_part[OF formed]) (simp_all add: system_union_def)
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: finite_system_union_correct decode_finite_system_of[OF formed] left right)
qed

theorem finite_system_of_view:
  assumes formed: "schema_system_formed (add_view_definition P d p C)"
  shows "finite_system_of (add_view_definition P d p C)=finite_add_view_definition (finite_system_of P) d
    (finite_pattern_of p) (Abs_fset (map_relation_values finite_schema_of C))"
proof -
  have base: "decode_finite_system (finite_system_of P)=P"
    by (rule decode_finite_system_of_part[OF formed]) (auto simp: add_view_definition_def)
  have interface: "(d,p)\<in>system_interfaces (add_view_definition P d p C)"
    by (simp add: add_view_definition_def)
  have pattern: "decode_finite_pattern (finite_pattern_of p)=p"
    using formed interface by (auto simp: schema_system_formed_def intro: decode_finite_pattern_of)
  have image: "(\<lambda>(c,S). ((d,c),S)) ` C\<subseteq>system_clauses (add_view_definition P d p C)"
    by (auto simp: add_view_definition_def)
  have finite: "finite C"
  proof -
    have "finite ((\<lambda>(c,S). ((d,c),S)) ` C)"
      using formed image finite_subset by (auto simp: schema_system_formed_def)
    moreover have "inj_on (\<lambda>(c,S). ((d,c),S)) C" by (auto simp: inj_on_def)
    ultimately show ?thesis by (rule finite_imageD)
  qed
  have schemas: "decode_finite_schema (finite_schema_of S)=S" if "(c,S)\<in>C" for c S
  proof -
    have "((d,c),S)\<in>system_clauses (add_view_definition P d p C)" using that image by blast
    then show ?thesis using formed by (auto simp: schema_system_formed_def intro: decode_finite_schema_of)
  qed
  have abs: "fset (Abs_fset (map_relation_values finite_schema_of C))=map_relation_values finite_schema_of C"
    by (rule Abs_fset_inverse) (simp add: finite)
  have clauses: "map_relation_values decode_finite_schema (fset (Abs_fset (map_relation_values finite_schema_of C)))=C"
    unfolding abs by (rule map_relation_values_inverse) (erule schemas)
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: finite_add_view_definition_correct decode_finite_system_of[OF formed] base pattern clauses)
qed

definition finite_system_restriction ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd fset \<Rightarrow> ('a,'s,'d,'c) finite_schema_system" where
  "finite_system_restriction P U=\<lparr>
    finite_system_interfaces=ffilter (\<lambda>(d,p). d|\<in>|U) (finite_system_interfaces P),
    finite_system_clauses=ffilter (\<lambda>((d,c),S). d|\<in>|U) (finite_system_clauses P)\<rparr>"

lemma finite_system_restriction_correct:
  "decode_finite_system (finite_system_restriction P U)=system_restriction (decode_finite_system P) (fset U)"
  by (rule schema_system.equality)
    (auto simp: set_eq_iff finite_system_restriction_def ffilter.rep_eq)

theorem finite_system_of_restriction:
  assumes formed: "schema_system_formed P"
  shows "finite_system_of (system_restriction P (fset U))=finite_system_restriction (finite_system_of P) U"
proof -
  have part: "decode_finite_system (finite_system_of (system_restriction P (fset U)))=system_restriction P (fset U)"
    by (rule decode_finite_system_of_part[OF formed]) auto
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: part finite_system_restriction_correct decode_finite_system_of[OF formed])
qed

theorem finite_system_of_whole_agreement:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
    and agreement: "systems_agree_on Q P (system_definitions Q)"
    and domain: "fset U=system_definitions Q"
  shows "finite_system_of Q=finite_system_restriction (finite_system_of P) U"
proof -
  have "system_restriction P (fset U)=Q"
    by (simp only: domain system_restriction_whole_agreement[OF formed(2) agreement])
  then show ?thesis using finite_system_of_restriction[OF formed(1), of U] by simp
qed

definition finite_dependency_edges :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>'d) fset" where
  "finite_dependency_edges P=ffUnion (fimage (\<lambda>z. fimage (Pair (fst (fst z))) (finite_schema_dependencies (snd z)))
    (finite_system_clauses P))"

lemma finite_dependency_edges_correct:
  "fset (finite_dependency_edges P)=system_dependency_edges (decode_finite_system P)"
proof (rule set_eqI)
  fix x :: "'a\<times>'a"
  obtain d e where x: "x=(d,e)" by (cases x)
  have "x\<in>fset (finite_dependency_edges P) \<longleftrightarrow>
      (\<exists>z\<in>fset (finite_system_clauses P). d=fst (fst z) \<and> e\<in>fset (finite_schema_dependencies (snd z)))"
    by (auto simp: x finite_dependency_edges_def ffUnion.rep_eq fimage.rep_eq)
  also have "\<dots> \<longleftrightarrow> x\<in>system_dependency_edges (decode_finite_system P)"
    by (auto simp: x system_dependency_edges_def finite_schema_dependencies_correct; force)
  finally show "x\<in>fset (finite_dependency_edges P) \<longleftrightarrow> x\<in>system_dependency_edges (decode_finite_system P)" .
qed

definition finite_definition_closure :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd fset \<Rightarrow> 'd fset" where
  "finite_definition_closure P R=R|\<union>|fimage snd (ffilter (\<lambda>z. fst z|\<in>|R)
    (finite_edge_closure (finite_dependency_edges P)))"

lemma finite_definition_closure_correct:
  "fset (finite_definition_closure P R)=system_definition_closure (decode_finite_system P) (fset R)"
proof (rule set_eqI)
  fix d
  show "d\<in>fset (finite_definition_closure P R) \<longleftrightarrow> d\<in>system_definition_closure (decode_finite_system P) (fset R)"
    by (auto simp: finite_definition_closure_def system_definition_closure_def finite_edge_closure_correct
      finite_dependency_edges_correct rtrancl_eq_or_trancl ffilter.rep_eq fimage.rep_eq image_iff; force)
qed

theorem finite_system_of_rooted:
  assumes formed: "schema_system_formed P"
  shows "finite_system_of (rooted_system P (fset R))=
    finite_system_restriction (finite_system_of P) (finite_definition_closure (finite_system_of P) R)"
  by (simp only: rooted_system_def finite_system_of_restriction[OF formed, symmetric]
    finite_definition_closure_correct decode_finite_system_of[OF formed])

end
