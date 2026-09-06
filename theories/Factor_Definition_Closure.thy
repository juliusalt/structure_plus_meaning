theory Factor_Definition_Closure
  imports Factor_Positive_Locality Factor_Native_Meaning
begin

section \<open>Definition closure follows the actual prospective callees\<close>

definition system_definition_closure ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "system_definition_closure P roots =
    {d. \<exists>r\<in>roots. (r,d)\<in>(system_dependency_edges P)\<^sup>*}"

lemma system_definition_closure_roots:
  "roots\<subseteq>system_definition_closure P roots"
  by (auto simp: system_definition_closure_def)

lemma system_definition_closure_step:
  assumes member: "d\<in>system_definition_closure P roots" and edge: "(d,e)\<in>system_dependency_edges P"
  shows "e\<in>system_definition_closure P roots"
proof -
  obtain r where root: "r\<in>roots" and path: "(r,d)\<in>(system_dependency_edges P)\<^sup>*"
    using member by (auto simp: system_definition_closure_def)
  have extended: "(r,e)\<in>(system_dependency_edges P)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF path edge])
  show ?thesis using root extended by (auto simp: system_definition_closure_def)
qed

lemma system_definition_closure_closed:
  "system_dependency_closed P (system_definition_closure P roots)"
  using system_definition_closure_step by (auto simp: system_dependency_closed_def)

lemma system_definition_closure_least:
  assumes roots: "roots\<subseteq>U" and closed: "system_dependency_closed P U"
  shows "system_definition_closure P roots\<subseteq>U"
proof
  fix d assume member: "d\<in>system_definition_closure P roots"
  obtain r where root: "r\<in>roots" and path: "(r,d)\<in>(system_dependency_edges P)\<^sup>*"
    using member by (auto simp: system_definition_closure_def)
  have base: "r\<in>U" using root roots by blast
  show "d\<in>U" using path
    by (induction rule: rtrancl_induct) (use base closed in \<open>auto simp: system_dependency_closed_def\<close>)
qed

lemma system_definition_closure_boundary:
  assumes formed: "schema_system_formed P" and roots: "roots\<subseteq>system_definitions P"
  shows "system_definition_closure P roots\<subseteq>system_definitions P"
    and "finite (system_definition_closure P roots)"
proof -
  have closed: "system_dependency_closed P (system_definitions P)"
    using system_dependency_boundary(1)[OF formed] by (auto simp: system_dependency_closed_def)
  show inside: "system_definition_closure P roots\<subseteq>system_definitions P"
    by (rule system_definition_closure_least[OF roots closed])
  show "finite (system_definition_closure P roots)"
    by (rule finite_subset[OF inside system_definitions_finite[OF formed]])
qed

lemma system_definition_closure_idempotent:
  "system_definition_closure P (system_definition_closure P roots)=system_definition_closure P roots"
proof -
  have left: "system_definition_closure P (system_definition_closure P roots)\<subseteq>system_definition_closure P roots"
    by (rule system_definition_closure_least[OF subset_refl system_definition_closure_closed])
  have right: "system_definition_closure P roots\<subseteq>system_definition_closure P (system_definition_closure P roots)"
    by (rule system_definition_closure_roots)
  show ?thesis using left right by blast
qed

theorem system_definition_closure_locality:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definition_closure P roots)"
    and root: "d\<in>roots"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed Q d t"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,t)\<in>positive_meaning Q"
proof -
  have member: "d\<in>system_definition_closure P roots"
    by (rule subsetD[OF system_definition_closure_roots root])
  show "schema_call_formed P d t\<longleftrightarrow>schema_call_formed Q d t"
    by (rule schema_call_agreement[OF formed agree member])
  show "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,t)\<in>positive_meaning Q"
    by (rule positive_meaning_dependency_locality[OF formed agree system_definition_closure_closed member])
qed

theorem system_definition_closure_instance:
  assumes member: "d\<in>system_definition_closure P roots"
    and inst: "admitted_schema_instance P d c V t Q"
  shows "\<forall>s e x. (s,e,x)\<in>Q \<longrightarrow> e\<in>system_definition_closure P roots"
  by (rule admitted_instance_inside[OF system_definition_closure_closed member inst])

section \<open>The native and recovered dependency graphs give the same closure\<close>

theorem native_program_definition_closure:
  assumes roots: "U\<subseteq>native_definition_sites E roots"
  shows "system_definition_closure (native_program E roots) U=native_definition_sites E U"
proof -
  let ?P="native_program E roots"
  let ?D="native_definition_sites E roots"
  have whole: "system_dependency_closed ?P ?D"
    using native_definition_step by (auto simp: system_dependency_closed_def native_program_dependency_edges)
  have included: "system_definition_closure ?P U\<subseteq>?D"
    by (rule system_definition_closure_least[OF roots whole])
  have closed: "system_dependency_closed ?P (native_definition_sites E U)"
    using native_definition_step by (auto simp: system_dependency_closed_def native_program_dependency_edges)
  have forward: "system_definition_closure ?P U\<subseteq>native_definition_sites E U"
    by (rule system_definition_closure_least[OF native_definition_roots closed])
  have reverse: "native_definition_sites E U\<subseteq>system_definition_closure ?P U"
  proof (rule native_definition_sites_least[OF system_definition_closure_roots])
    fix d e assume member: "d\<in>system_definition_closure ?P U" and edge: "(d,e)\<in>native_definition_edges E"
    have inside: "d\<in>?D" using included member by blast
    have recovered: "(d,e)\<in>system_dependency_edges ?P"
      using edge inside by (simp add: native_program_dependency_edges)
    show "e\<in>system_definition_closure ?P U"
      by (rule system_definition_closure_step[OF member recovered])
  qed
  show ?thesis using forward reverse by blast
qed

text \<open>
  Closure is derived from complete clause families and their prospective
  callees. It is finite inside a formed program, contains its supplied roots,
  and is the least set closed under those edges. Every admitted instance at a
  member calls only members, for every substitution and ordinary argument.

  For native programs this is exactly the existing grammar-derived definition
  reachability, restricted to roots in the package. Complete program formation
  still checks the whole package. Closure bounds all possible recursive truth
  calls from its roots; it is not a claim that every such call occurs in each
  particular derivation. Material observations and quoted candidate programs
  remain operands and introduce no semantic invocation edge.
\<close>

end
