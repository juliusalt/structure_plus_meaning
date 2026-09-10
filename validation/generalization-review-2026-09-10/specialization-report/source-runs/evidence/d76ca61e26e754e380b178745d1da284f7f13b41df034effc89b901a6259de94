theory Factor_Reference_Packages
  imports Factor_Reference_Environments
begin

section \<open>Simultaneous reference requirements over preallocated source artifacts\<close>

theorem finite_reference_environment_total:
  fixes E :: "local_address option artifact_environment"
  assumes fin: "finite U" and ef: "environment_formed E"
    and sources: "\<forall>u\<in>U. artifact_at E u (R u)"
    and profiles: "\<forall>u\<in>U. reference_table_formed (L u) (C u)"
    and bounds: "\<forall>u\<in>U. rel_dom (L u) \<union> rel_dom (C u) \<subseteq> rra_carrier (object_structure (R u))"
    and callees: "\<forall>u\<in>U. \<forall>d\<in>rel_ran (C u). \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    and unbound: "\<forall>u\<in>U. \<forall>k\<in>rel_dom (L u) \<union> rel_dom (C u). \<forall>v. \<not> binds_slot E u k v"
  shows "\<exists>F. environment_formed F \<and> environment_included E F \<and>
    (\<forall>u\<in>U. syntax_references F u (L u) (C u)) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. (v \<notin> U \<or> k \<notin> rel_dom (L v) \<union> rel_dom (C v)) \<longrightarrow>
      (binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
  using fin sources profiles bounds callees unbound
proof (induction U rule: finite_induct)
  case empty
  show ?case by (rule exI[of _ E]) (use ef in simp)
next
  case (insert u U)
  have sources: "\<forall>v\<in>U. artifact_at E v (R v)"
    and profiles: "\<forall>v\<in>U. reference_table_formed (L v) (C v)"
    and bounds: "\<forall>v\<in>U. rel_dom (L v) \<union> rel_dom (C v) \<subseteq> rra_carrier (object_structure (R v))"
    and callees: "\<forall>v\<in>U. \<forall>d\<in>rel_ran (C v). \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    and unbound: "\<forall>v\<in>U. \<forall>k\<in>rel_dom (L v) \<union> rel_dom (C v). \<forall>w. \<not> binds_slot E v k w"
    using insert.prems by simp_all
  obtain G where old: "environment_formed G" "environment_included E G"
    "\<forall>v\<in>U. syntax_references G v (L v) (C v)"
    "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at G v T \<longleftrightarrow> artifact_at E v T"
    "\<forall>v\<in>environment_uses E. \<forall>k w. (v \<notin> U \<or> k \<notin> rel_dom (L v) \<union> rel_dom (C v)) \<longrightarrow>
      (binds_slot G v k w \<longleftrightarrow> binds_slot E v k w)"
    using insert.IH[OF sources profiles bounds callees unbound] by metis
  have original: "artifact_at E u (R u)" and profile: "reference_table_formed (L u) (C u)"
    and bound: "rel_dom (L u) \<union> rel_dom (C u) \<subseteq> rra_carrier (object_structure (R u))"
    using insert.prems by simp_all
  have inside: "u \<in> environment_uses E" using original by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have source: "artifact_at G u (R u)" by (rule included_artifact[OF old(2) original])
  have targets: "\<forall>k d. (k,d) \<in> C u \<longrightarrow> (\<exists>T. artifact_at G (fst d) T \<and> anchor_formed (T,snd d))"
  proof (intro allI impI)
    fix k d assume entry: "(k,d) \<in> C u"
    have member: "d \<in> rel_ran (C u)" by (rule rel_ranI[OF entry])
    obtain T where original: "artifact_at E (fst d) T" "anchor_formed (T,snd d)"
      using insert.prems(4) member by auto
    show "\<exists>T. artifact_at G (fst d) T \<and> anchor_formed (T,snd d)"
      using included_artifact[OF old(2) original(1)] original(2) by blast
  qed
  have available: "\<And>k v. k \<in> rel_dom (L u) \<union> rel_dom (C u) \<Longrightarrow> \<not> binds_slot G u k v"
  proof -
    fix k v assume key: "k \<in> rel_dom (L u) \<union> rel_dom (C u)"
    have free: "\<not> binds_slot E u k v" using insert.prems(5) key by simp
    have same: "binds_slot G u k v \<longleftrightarrow> binds_slot E u k v" using old(5) inside insert.hyps(2) by blast
    show "\<not> binds_slot G u k v" using free same by blast
  qed
  interpret extension: reference_extension G u "R u" "L u" "C u"
    by (rule reference_extension.intro[OF old(1) source profile bound targets available])
  let ?F = "install_reference_tables G u (R u) (L u) (C u)"
  have included: "environment_included E ?F" by (rule environment_included_trans[OF old(2) extension.included])
  have refs: "\<forall>v\<in>insert u U. syntax_references ?F v (L v) (C v)"
  proof (intro ballI)
    fix v assume member: "v \<in> insert u U"
    show "syntax_references ?F v (L v) (C v)"
    proof (cases "v=u")
      case True
      show ?thesis using extension.references True by simp
    next
      case False
      have old_refs: "syntax_references G v (L v) (C v)" using old(3) member False by blast
      show ?thesis by (rule syntax_references_included[OF extension.formed extension.included old_refs])
    qed
  qed
  have artifacts: "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
  proof (intro ballI allI)
    fix v T assume member: "v \<in> environment_uses E"
    have in_old: "v \<in> environment_uses G" by (rule subsetD[OF included_uses[OF old(2)] member])
    show "artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
      using extension.old_artifacts[OF in_old] old(4) member by blast
  qed
  have bindings: "\<forall>v\<in>environment_uses E. \<forall>k w.
    (v \<notin> insert u U \<or> k \<notin> rel_dom (L v) \<union> rel_dom (C v)) \<longrightarrow>
      (binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w)"
  proof (intro ballI allI impI)
    fix v k w assume member: "v \<in> environment_uses E"
      and outside: "v \<notin> insert u U \<or> k \<notin> rel_dom (L v) \<union> rel_dom (C v)"
    have separate: "v \<noteq> u \<or> k \<notin> rel_dom (L u) \<union> rel_dom (C u)" using outside by auto
    have previous: "v \<notin> U \<or> k \<notin> rel_dom (L v) \<union> rel_dom (C v)" using outside by auto
    show "binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w"
      using extension.other_bindings[OF separate] old(5) member previous by blast
  qed
  show ?case by (rule exI[of _ ?F]) (use extension.formed included refs artifacts bindings in blast)
qed

theorem preallocated_reference_environment:
  fixes U :: "local_address option set"
  assumes fin: "finite U" and formed: "\<forall>u\<in>U. exact_formed (R u)"
    and profiles: "\<forall>u\<in>U. reference_table_formed (L u) (C u)"
    and bounds: "\<forall>u\<in>U. rel_dom (L u) \<union> rel_dom (C u) \<subseteq> rra_carrier (object_structure (R u))"
    and callees: "\<forall>u\<in>U. \<forall>d\<in>rel_ran (C u).
      fst d \<in> U \<and> snd d \<in> rra_carrier (object_structure (R (fst d)))"
  shows "\<exists>E. environment_formed E \<and>
    (\<forall>u\<in>U. artifact_at E u (R u) \<and> syntax_references E u (L u) (C u)) \<and>
    (\<forall>u\<in>U. \<forall>T. artifact_at E u T \<longleftrightarrow> T=R u)"
proof -
  let ?E = "artifact_family_environment U R"
  have ef: "environment_formed ?E" by (rule artifact_family_formed[OF fin formed])
  have sources: "\<forall>u\<in>U. artifact_at ?E u (R u)" by simp
  have targets: "\<forall>u\<in>U. \<forall>d\<in>rel_ran (C u).
    \<exists>T. artifact_at ?E (fst d) T \<and> anchor_formed (T,snd d)"
  proof (intro ballI)
    fix u d assume member: "u \<in> U" and dependency: "d \<in> rel_ran (C u)"
    have target: "fst d \<in> U" "snd d \<in> rra_carrier (object_structure (R (fst d)))"
      using callees member dependency by blast+
    have rf: "exact_formed (R (fst d))" using formed target(1) by blast
    show "\<exists>T. artifact_at ?E (fst d) T \<and> anchor_formed (T,snd d)"
      by (rule exI[of _ "R (fst d)"]) (use target rf in \<open>simp add: anchor_formed_def\<close>)
  qed
  have unbound: "\<forall>u\<in>U. \<forall>k\<in>rel_dom (L u) \<union> rel_dom (C u). \<forall>v. \<not> binds_slot ?E u k v"
    by simp
  obtain F where final: "environment_formed F" "environment_included ?E F"
    "\<forall>u\<in>U. syntax_references F u (L u) (C u)"
    "\<forall>u\<in>environment_uses ?E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at ?E u T"
    using finite_reference_environment_total[OF fin ef sources profiles bounds targets unbound] by metis
  have actual: "\<forall>u\<in>U. artifact_at F u (R u)"
    using final(4) by simp
  show ?thesis by (rule exI[of _ F]) (use final actual in auto)
qed

text \<open>
  Every finite set of preallocated source artifacts can receive all of its
  compatible literal and callee references. Callees may target the same source
  or any other preallocated source, including cycles. Reference installation
  preserves earlier references, all original artifact values, and every binding
  outside the specified new source slots.
\<close>

section \<open>Fresh reference packages preserve the entire existing environment\<close>

theorem fresh_reference_environment:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and fin: "finite U" and fresh: "U\<inter>environment_uses E={}"
    and formed: "\<forall>u\<in>U. exact_formed (R u)"
    and profiles: "\<forall>u\<in>U. reference_table_formed (L u) (C u)"
    and bounds: "\<forall>u\<in>U. rel_dom (L u)\<union>rel_dom (C u)\<subseteq>rra_carrier (object_structure (R u))"
    and targets: "\<forall>u\<in>U. \<forall>d\<in>rel_ran (C u).
      d\<in>environment_positions E \<or>
      (fst d\<in>U \<and> snd d\<in>rra_carrier (object_structure (R (fst d))))"
  shows "\<exists>F. environment_formed F \<and> environment_included E F \<and>
    (\<forall>u\<in>U. artifact_at F u (R u) \<and> syntax_references F u (L u) (C u)) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v)"
proof -
  interpret allocation: fresh_artifact_family E U R
    by (rule fresh_artifact_family.intro[OF ef fin fresh formed])
  let ?G = "allocation.extended"
  have sources: "\<forall>u\<in>U. artifact_at ?G u (R u)"
    using allocation.new_artifacts by blast
  have anchored: "\<forall>u\<in>U. \<forall>d\<in>rel_ran (C u).
    \<exists>T. artifact_at ?G (fst d) T \<and> anchor_formed (T,snd d)"
  proof (intro ballI)
    fix u d assume member: "u\<in>U" and dependency: "d\<in>rel_ran (C u)"
    have alternatives: "d\<in>environment_positions E \<or>
      (fst d\<in>U \<and> snd d\<in>rra_carrier (object_structure (R (fst d))))"
      using targets member dependency by blast
    show "\<exists>T. artifact_at ?G (fst d) T \<and> anchor_formed (T,snd d)"
    proof (cases "d\<in>environment_positions E")
      case True
      obtain T where old: "artifact_at E (fst d) T" "anchor_formed (T,snd d)"
        using environment_position_anchor[OF ef True] by blast
      have art: "artifact_at ?G (fst d) T" by (rule included_artifact[OF allocation.included old(1)])
      show ?thesis using art old(2) by blast
    next
      case False
      have new: "fst d\<in>U" "snd d\<in>rra_carrier (object_structure (R (fst d)))"
        using alternatives False by auto
      have rf: "exact_formed (R (fst d))" using formed new(1) by blast
      show ?thesis using allocation.new_artifacts[OF new(1)] rf new(2)
        by (auto simp: anchor_formed_def)
    qed
  qed
  have unbound: "\<forall>u\<in>U. \<forall>k\<in>rel_dom (L u)\<union>rel_dom (C u). \<forall>v. \<not>binds_slot ?G u k v"
    using allocation.new_unbound by blast
  obtain F where installed: "environment_formed F" "environment_included ?G F"
    "\<forall>u\<in>U. syntax_references F u (L u) (C u)"
    "\<forall>u\<in>environment_uses ?G. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at ?G u T"
    "\<forall>u\<in>environment_uses ?G. \<forall>k v.
      (u\<notin>U \<or> k\<notin>rel_dom (L u)\<union>rel_dom (C u)) \<longrightarrow>
      (binds_slot F u k v \<longleftrightarrow> binds_slot ?G u k v)"
    using finite_reference_environment_total[OF fin allocation.extended_formed sources profiles bounds anchored unbound] by metis
  have included: "environment_included E F"
    by (rule environment_included_trans[OF allocation.included installed(2)])
  have complete: "\<forall>u\<in>U. artifact_at F u (R u) \<and> syntax_references F u (L u) (C u)"
  proof (intro ballI conjI)
    fix u assume member: "u\<in>U"
    have source: "artifact_at ?G u (R u)" using sources member by blast
    show "artifact_at F u (R u)" by (rule included_artifact[OF installed(2) source])
    show "syntax_references F u (L u) (C u)" using installed(3) member by blast
  qed
  have artifacts: "\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T"
  proof (intro ballI allI)
    fix u T assume member: "u\<in>environment_uses E"
    have inside: "u\<in>environment_uses ?G" by (rule subsetD[OF included_uses[OF allocation.included] member])
    show "artifact_at F u T \<longleftrightarrow> artifact_at E u T"
      using installed(4) inside allocation.old_artifacts[OF member] by blast
  qed
  have bindings: "\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
  proof (intro ballI allI)
    fix u k v assume member: "u\<in>environment_uses E"
    have inside: "u\<in>environment_uses ?G" by (rule subsetD[OF included_uses[OF allocation.included] member])
    have outside: "u\<notin>U" using member fresh by blast
    show "binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
      using installed(5) inside outside allocation.bindings by blast
  qed
  show ?thesis by (rule exI[of _ F]) (use installed(1) included complete artifacts bindings in blast)
qed

end
