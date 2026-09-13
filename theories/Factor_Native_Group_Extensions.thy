theory Factor_Native_Group_Extensions
  imports Factor_Recursive_Groups Factor_Package_Extensions Factor_Program_Scopes Factor_Rooted_Code_Families
begin

section \<open>Recursive definition families extend the actual existing source\<close>

theorem native_group_extension_total:
  fixes E :: "local_address option artifact_environment"
    and P Q :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes source: "native_package_at E pu pr N"
    and source_variant: "system_alpha_variant P N"
    and group: "schema_system_formed_over (system_definitions P) Q"
    and roots: "\<forall>d\<in>system_definitions Q. snd d=[]"
    and fresh: "fst ` system_definitions Q\<inter>environment_uses E={}"
  shows "\<exists>F u T K. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr N \<and> native_package_at F u [] T \<and>
    system_definitions T=system_definitions P\<union>system_definitions Q \<and>
    system_alpha_variant (system_union P Q) T \<and>
    positive_meaning T=positive_meaning (system_union P Q) \<and>
    (\<forall>d t. schema_call_formed T d t \<longleftrightarrow> schema_call_formed (system_union P Q) d t) \<and>
    (\<forall>d\<in>system_definitions Q.
      definition_code_for (system_interface (system_union P Q) d) (system_clause_family (system_union P Q) d) (K d) \<and>
      native_definition_at F (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T d t \<longleftrightarrow> schema_call_formed N d t) \<and>
      ((d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning N)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>k v. binds_slot F w k v \<longleftrightarrow> binds_slot E w k v)"
proof -
  let ?D="system_definitions Q"
  let ?V="system_union P Q"
  let ?B="system_definitions P\<union>?D"
  have ef: "environment_formed E"
    using native_package_projection(1)[OF source] by (simp add: native_package_formed_def)
  have pf: "schema_system_formed P" and source_definitions: "system_definitions P=system_definitions N"
    using source_variant unfolding system_alpha_variant_def by blast+
  have source_site: "d\<in>system_definitions N" if "d\<in>system_definitions P" for d
    using source_definitions that by simp
  have source_position: "d\<in>environment_positions E" if "d\<in>system_definitions P" for d
    by (rule native_package_entry_position[OF source source_site[OF that]])
  have separate: "system_definitions P\<inter>?D={}"
  proof (rule ccontr)
    assume "system_definitions P\<inter>?D\<noteq>{}"
    then obtain d where old: "d\<in>system_definitions P" and new: "d\<in>?D" by auto
    have position: "d\<in>environment_positions E" by (rule source_position[OF old])
    have used: "fst d\<in>environment_uses E"
      using position by (auto simp: environment_positions_def environment_uses_def artifact_at_def rel_dom_def)
    show False using fresh new used by blast
  qed
  interpret algebra: positive_definition_group P Q
    by (rule positive_definition_group.intro[OF pf group separate])
  have inside: "?D\<subseteq>system_definitions ?V" by simp
  have addresses: "\<forall>d\<in>?D. \<forall>S\<in>rel_ran (system_clause_family ?V d).
    \<forall>e\<in>schema_dependencies S. octets_formed (snd e)"
  proof (intro ballI)
    fix d S e assume member: "d\<in>?D" and schema: "S\<in>rel_ran (system_clause_family ?V d)"
      and callee: "e\<in>schema_dependencies S"
    have target: "e\<in>?B"
      using system_clause_family_dependencies[OF algebra.formed, of d] schema callee by auto
    show "octets_formed (snd e)"
    proof (cases "e\<in>system_definitions P")
      case True
      show ?thesis by (rule environment_position_address[OF ef source_position[OF True]])
    next
      case False
      have new: "e\<in>?D" using target False by blast
      show ?thesis using roots new by (simp add: octets_formed_def)
    qed
  qed
  obtain K where codes: "\<forall>d\<in>?D.
    definition_code_for (system_interface ?V d) (system_clause_family ?V d) (K d)"
    using definition_codes_on[OF algebra.formed inside addresses] by blast
  interpret family: rooted_code_family ?V ?D K
    by (rule rooted_code_family.intro[OF algebra.formed inside roots codes])
  have targets: "\<forall>u\<in>family.uses. \<forall>d\<in>rel_ran (family.callees u).
    d\<in>environment_positions E \<or>
      (fst d\<in>family.uses \<and> snd d\<in>rra_carrier (object_structure (family.artifacts (fst d))))"
  proof (intro ballI)
    fix u d assume member: "u\<in>family.uses" and callee: "d\<in>rel_ran (family.callees u)"
    have boundary: "d\<in>?B" using family.callee_source[OF member callee] by simp
    show "d\<in>environment_positions E \<or>
      (fst d\<in>family.uses \<and> snd d\<in>rra_carrier (object_structure (family.artifacts (fst d))))"
    proof (cases "d\<in>system_definitions P")
      case True
      then show ?thesis using source_position[OF True] by blast
    next
      case False
      have new: "d\<in>?D" using boundary False by blast
      show ?thesis using family.internal_anchor[OF new] by blast
    qed
  qed
  obtain H where built: "environment_formed H" "environment_included E H"
    "\<forall>u\<in>family.uses. artifact_at H u (family.artifacts u) \<and>
      syntax_references H u (family.literals u) (family.callees u)"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at H w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>k v. binds_slot H w k v \<longleftrightarrow> binds_slot E w k v"
    using fresh_reference_environment[OF ef family.finite_uses fresh family.artifact_formation
      family.profiles family.bounds targets] by blast
  have copied: "native_package_at H pu pr N" by (rule native_package_included[OF source built(2,1)])
  have compiled: "native_definition_at H (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
    if "d\<in>?D" for d
    using family.installed[OF built(1,3)] that by blast
  have reads: "\<exists>p C. native_definition_at H (fst d) (snd d) p C" if "d\<in>?B" for d
  proof (cases "d\<in>?D")
    case True
    show ?thesis using compiled[OF True] by blast
  next
    case False
    have old: "d\<in>system_definitions P" using that False by blast
    show ?thesis by (rule native_package_definition_exists[OF copied source_site[OF old]])
  qed
  have closed: "e\<in>?B" if member: "d\<in>?B" and edge: "(d,e)\<in>native_definition_edges H" for d e
  proof (cases "d\<in>?D")
    case True
    have dependency: "e\<in>(\<Union>S\<in>rel_ran (code_clauses (K d)). schema_dependencies S)"
      using native_definition_edges_at[OF compiled[OF True], of e] edge
      by (auto simp: rel_ran_def)
    show ?thesis using family.compiled_dependencies[OF True] dependency by auto
  next
    case False
    have old: "d\<in>system_definitions P" using member False by blast
    show ?thesis using native_package_edge_closed[OF copied source_site[OF old] edge] source_definitions by simp
  qed
  have selectable: "\<exists>F u T. environment_formed F \<and> environment_included H F \<and>
    native_package_at F u [] T \<and> system_definitions T=?B \<and>
    (\<forall>w\<in>environment_uses H. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at H w A) \<and>
    (\<forall>w\<in>environment_uses H. \<forall>k v. binds_slot F w k v \<longleftrightarrow> binds_slot H w k v)"
  proof (rule native_definition_family_selection[OF built(1)])
    fix d assume member: "d\<in>?B"
    show "\<exists>p C. native_definition_at H (fst d) (snd d) p C" by (rule reads[OF member])
  next
    fix d e assume member: "d\<in>?B" and edge: "(d,e)\<in>native_definition_edges H"
    show "e\<in>?B" by (rule closed[OF member edge])
  qed
  obtain F u T where selected: "environment_formed F" "environment_included H F"
    "native_package_at F u [] T" "system_definitions T=?B"
    "\<forall>w\<in>environment_uses H. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at H w A"
    "\<forall>w\<in>environment_uses H. \<forall>k v. binds_slot F w k v \<longleftrightarrow> binds_slot H w k v"
    using selectable by blast
  have included: "environment_included E F" by (rule environment_included_trans[OF built(2) selected(2)])
  have original: "native_package_at F pu pr N" by (rule native_package_included[OF source included selected(1)])
  have new_reads: "\<forall>d\<in>?D.
    definition_code_for (system_interface ?V d) (system_clause_family ?V d) (K d) \<and>
    native_definition_at F (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
  proof (intro ballI conjI)
    fix d assume member: "d\<in>?D"
    show "definition_code_for (system_interface ?V d) (system_clause_family ?V d) (K d)"
      using codes member by blast
    show "native_definition_at F (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
      by (rule native_definition_included[OF compiled[OF member] selected(2,1)])
  qed
  have meanings: "\<forall>d\<in>system_definitions P. \<forall>t.
    (schema_call_formed T d t \<longleftrightarrow> schema_call_formed N d t) \<and>
    ((d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning N)"
  proof (intro ballI allI)
    fix d t assume member: "d\<in>system_definitions P"
    have target: "d\<in>system_definitions T" using selected(4) member by simp
    show "(schema_call_formed T d t \<longleftrightarrow> schema_call_formed N d t) \<and>
      ((d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning N)"
      using native_packages_shared_call[OF selected(3) original target source_site[OF member], of t]
        native_packages_shared_meaning[OF selected(3) original target source_site[OF member], of t] by blast
  qed
  have variants: "\<exists>p C f h. native_definition_at F (fst d) (snd d) p C \<and>
    inj_on f (pattern_variables (system_interface ?V d)) \<and>
    p=rename_pattern f (system_interface ?V d) \<and>
    schema_family_variant h (system_clause_family ?V d) C"
    if member: "d\<in>system_definitions ?V" for d
  proof (cases "d\<in>?D")
    case True
    have code: "definition_code_for (system_interface ?V d) (system_clause_family ?V d) (K d)"
      and read: "native_definition_at F (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
      using new_reads True by blast+
    show ?thesis using definition_code_properties(4)[OF code] read by blast
  next
    case False
    have old: "d\<in>system_definitions P" using member False by simp
    obtain p C where read: "native_definition_at F (fst d) (snd d) p C"
      using native_package_definition_exists[OF original source_site[OF old]] by blast
    obtain f h where renaming: "inj_on f (pattern_variables (system_interface P d))"
      "system_interface N d=rename_pattern f (system_interface P d)"
      "schema_family_variant h (system_clause_family P d) (system_clause_family N d)"
      using source_variant old unfolding system_alpha_variant_def by blast
    have fields: "system_interface N d=p" "system_clause_family N d=C"
      by (rule native_package_fields_at[OF original source_site[OF old] read])+
    have agreement: "system_interface ?V d=system_interface P d"
      "system_clause_family ?V d=system_clause_family P d"
      by (rule systems_agree_on_fields[OF pf algebra.formed algebra.old_agreement old old])+
    show ?thesis by (rule exI[of _ p], rule exI[of _ C], rule exI[of _ f], rule exI[of _ h])
      (use read renaming fields agreement in simp)
  qed
  have variant: "system_alpha_variant ?V T"
  proof (rule native_package_variant_from_readings[OF algebra.formed selected(3)])
    show "system_definitions ?V=system_definitions T" using selected(4) by simp
  next
    fix d assume member: "d\<in>system_definitions ?V"
    show "\<exists>p C f h. native_definition_at F (fst d) (snd d) p C \<and>
      inj_on f (pattern_variables (system_interface ?V d)) \<and>
      p=rename_pattern f (system_interface ?V d) \<and>
      schema_family_variant h (system_clause_family ?V d) C" by (rule variants[OF member])
  qed
  have complete_meaning: "positive_meaning T=positive_meaning ?V"
    using system_alpha_positive_meaning[OF variant] by simp
  have complete_calls: "\<forall>d t. schema_call_formed T d t \<longleftrightarrow> schema_call_formed ?V d t"
    using system_alpha_calls[OF variant] by blast
  have uses: "environment_uses E\<subseteq>environment_uses H" by (rule included_uses[OF built(2)])
  have artifacts: "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    using uses selected(5) built(4) by blast
  have bindings: "\<forall>w\<in>environment_uses E. \<forall>k v. binds_slot F w k v \<longleftrightarrow> binds_slot E w k v"
    using uses selected(6) built(5) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ T], rule exI[of _ K])
    (use selected(1,3,4) included original variant complete_meaning complete_calls
      new_reads meanings artifacts bindings in blast)
qed

text \<open>
  New definitions have distinct fresh uses and may call one another recursively
  as well as the actual original source package. Their code comes from the
  complete source-and-group union. The existing fresh-reference constructor
  installs every artifact before resolving those cycles. Exact root selection
  retains the whole old and new definition family. Every original artifact,
  outgoing binding, call boundary and meaning is preserved. Complete readings
  establish the whole program variant, so every call boundary and the entire
  positive meaning agree with the original source-and-group union, including
  mutually recursive new definitions.

  The ordinary source may use different private variable, socket and clause
  coordinates. Its complete program variant must be established against the
  actual retained native source before extension. The constructor compiles
  only new definitions; the old source readings and references remain actual
  material. Taking the ordinary source to be that native program itself uses
  the identity variant.
\<close>

end
