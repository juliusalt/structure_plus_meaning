theory RRA_Fresh_Uses
  imports RRA_Environment
begin

section \<open>Fresh use occurrences in one fixed unbounded carrier\<close>

fun use_word_length :: "local_address option \<Rightarrow> nat" where
  "use_word_length None = 0"
| "use_word_length (Some a) = length a"

definition fresh_use_prefix :: "local_address option set \<Rightarrow> local_address option \<Rightarrow> local_address" where
  "fresh_use_prefix U u = replicate (Suc (Max (use_word_length ` insert u U))) 0"

fun fresh_use_map ::
  "local_address option set \<Rightarrow> local_address option \<Rightarrow>
    local_address option \<Rightarrow> local_address option" where
  "fresh_use_map U u None = u"
| "fresh_use_map U u (Some a) = Some (fresh_use_prefix U u @ a)"

lemma fresh_use_prefix_formed [simp]: "octets_formed (fresh_use_prefix U u)"
  by (simp add: fresh_use_prefix_def octets_formed_def)

lemma fresh_use_map_outside:
  assumes finite: "finite U"
  shows "fresh_use_map U u (Some a) \<notin> insert u U"
proof
  assume member: "fresh_use_map U u (Some a) \<in> insert u U"
  have image: "use_word_length (fresh_use_map U u (Some a)) \<in> use_word_length ` insert u U"
    by (rule imageI[OF member])
  have fin: "finite (use_word_length ` insert u U)" using finite by simp
  have bound: "use_word_length (fresh_use_map U u (Some a)) \<le> Max (use_word_length ` insert u U)"
    by (rule Max_ge[OF fin image])
  have "Suc (Max (use_word_length ` insert u U)) + length a \<le> Max (use_word_length ` insert u U)"
    using bound by (simp add: fresh_use_prefix_def)
  then show False by arith
qed

lemma fresh_use_map_injective:
  assumes finite: "finite U"
  shows "inj (fresh_use_map U u)"
proof -
  show ?thesis
  proof (rule injI)
    fix x y assume eq: "fresh_use_map U u x = fresh_use_map U u y"
    show "x=y"
    proof (cases x)
      case None
      have xp: "x=None" by (rule None)
      show ?thesis
      proof (cases y)
        case None
        show ?thesis using xp None by simp
      next
        case (Some b)
        have equal: "fresh_use_map U u (Some b)=u" using eq xp Some by simp
        have outside: "fresh_use_map U u (Some b) \<notin> insert u U"
          by (rule fresh_use_map_outside[OF finite])
        show ?thesis using outside equal by simp
      qed
    next
      case (Some a)
      have xp: "x=Some a" by (rule Some)
      show ?thesis
      proof (cases y)
        case None
        have equal: "fresh_use_map U u (Some a)=u" using eq xp None by simp
        have outside: "fresh_use_map U u (Some a) \<notin> insert u U"
          by (rule fresh_use_map_outside[OF finite])
        show ?thesis using outside equal by simp
      next
        case (Some b)
        show ?thesis using eq xp Some by simp
      qed
    qed
  qed
qed

lemma fresh_use_existing_origin:
  assumes finite: "finite U" and member: "v \<in> U" and same: "fresh_use_map U u x = v"
  shows "x=None \<and> v=u"
  using member same fresh_use_map_outside[OF finite, of u]
  by (cases x) auto

section \<open>Composition at an explicitly shared passive boundary\<close>

definition graft_environment ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option artifact_environment" where
  "graft_environment E u F =
    merge_environment E (rename_environment (fresh_use_map (environment_uses E) u) F)"

lemma graft_imported_artifact:
  assumes ef: "environment_formed E" and ff: "environment_formed F" and boundary: "artifact_at F None R"
    and member: "v \<in> environment_uses E"
    and imported: "artifact_at (rename_environment (fresh_use_map (environment_uses E) u) F) v S"
  shows "v=u \<and> S=R"
proof -
  have finite: "finite (environment_uses E)" by (rule environment_uses_finite[OF ef])
  obtain x where mapped: "fresh_use_map (environment_uses E) u x=v" and source: "artifact_at F x S"
    using imported by (auto simp: artifact_at_renaming)
  have origin: "x=None \<and> v=u" by (rule fresh_use_existing_origin[OF finite member mapped])
  have art: "artifact_at F None S" using source origin by simp
  have same: "S=R" by (rule environment_artifact_unique[OF ff art boundary])
  show ?thesis using origin same by blast
qed

lemma graft_imported_binding_no_old:
  assumes ef: "environment_formed E" and boundary_empty: "\<And>k v. \<not> binds_slot F None k v"
    and member: "v \<in> environment_uses E"
    and imported: "binds_slot (rename_environment (fresh_use_map (environment_uses E) u) F) v k w"
  shows False
proof -
  have finite: "finite (environment_uses E)" by (rule environment_uses_finite[OF ef])
  obtain x y where mapped: "fresh_use_map (environment_uses E) u x=v" and binding: "binds_slot F x k y"
    using imported by (auto simp: binds_slot_renaming)
  have origin: "x=None \<and> v=u" by (rule fresh_use_existing_origin[OF finite member mapped])
  have old: "binds_slot F None k y" using binding origin by simp
  show False using boundary_empty[of k y] old by blast
qed

lemma graft_environments_compatible:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and source: "artifact_at E u R" and boundary: "artifact_at F None R"
    and boundary_empty: "\<And>k v. \<not> binds_slot F None k v"
  shows "environments_compatible E (rename_environment (fresh_use_map (environment_uses E) u) F)"
proof -
  let ?G = "rename_environment (fresh_use_map (environment_uses E) u) F"
  have artifacts: "\<forall>v S T. artifact_at E v S \<longrightarrow> artifact_at ?G v T \<longrightarrow> S=T"
  proof (intro allI impI)
    fix v S T assume old: "artifact_at E v S" and new: "artifact_at ?G v T"
    have member: "v \<in> environment_uses E" using old by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
    have imported: "v=u \<and> T=R" by (rule graft_imported_artifact[OF ef ff boundary member new])
    have at_source: "artifact_at E u S" using old imported by simp
    have same: "S=R" by (rule environment_artifact_unique[OF ef at_source source])
    show "S=T" using same imported by blast
  qed
  have bindings: "\<forall>v k x y. binds_slot E v k x \<longrightarrow> binds_slot ?G v k y \<longrightarrow> x=y"
  proof (intro allI impI)
    fix v k x y assume old: "binds_slot E v k x" and new: "binds_slot ?G v k y"
    obtain S where art: "artifact_at E v S" using ef old unfolding environment_formed_def by blast
    have member: "v \<in> environment_uses E" using art by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
    have False by (rule graft_imported_binding_no_old[OF ef boundary_empty member new])
    then show "x=y" by blast
  qed
  show ?thesis using artifacts bindings by (simp add: environments_compatible_def)
qed

theorem graft_environment_formed:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and source: "artifact_at E u R" and boundary: "artifact_at F None R"
    and boundary_empty: "\<And>k v. \<not> binds_slot F None k v"
  shows "environment_formed (graft_environment E u F)"
proof -
  have finite: "finite (environment_uses E)" by (rule environment_uses_finite[OF ef])
  have injective: "inj (fresh_use_map (environment_uses E) u)" by (rule fresh_use_map_injective[OF finite])
  have formed: "environment_formed (rename_environment (fresh_use_map (environment_uses E) u) F)"
    by (rule environment_renaming_formed[OF ff injective])
  have compatible: "environments_compatible E (rename_environment (fresh_use_map (environment_uses E) u) F)"
    by (rule graft_environments_compatible[OF assms])
  show ?thesis unfolding graft_environment_def
    using environment_merge_formed_iff[OF ef formed] compatible by blast
qed

lemma graft_includes_existing:
  "environment_included E (graft_environment E u F)"
  unfolding graft_environment_def by (rule environment_included_merge_left)

lemma graft_includes_imported:
  "environment_included (rename_environment (fresh_use_map (environment_uses E) u) F) (graft_environment E u F)"
  unfolding graft_environment_def by (rule environment_included_merge_right)

theorem graft_existing_artifacts_unchanged:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and source: "artifact_at E u R" and boundary: "artifact_at F None R"
    and member: "v \<in> environment_uses E"
  shows "artifact_at (graft_environment E u F) v S \<longleftrightarrow> artifact_at E v S"
proof
  assume art: "artifact_at (graft_environment E u F) v S"
  have alternatives: "artifact_at E v S \<or>
    artifact_at (rename_environment (fresh_use_map (environment_uses E) u) F) v S"
    using art by (simp add: graft_environment_def)
  then show "artifact_at E v S"
  proof
    assume "artifact_at E v S"
    then show ?thesis .
  next
    assume imported: "artifact_at (rename_environment (fresh_use_map (environment_uses E) u) F) v S"
    have same: "v=u \<and> S=R" by (rule graft_imported_artifact[OF ef ff boundary member imported])
    show ?thesis using source same by simp
  qed
next
  assume art: "artifact_at E v S"
  show "artifact_at (graft_environment E u F) v S" by (rule included_artifact[OF graft_includes_existing art])
qed

theorem graft_existing_bindings_unchanged:
  assumes ef: "environment_formed E" and boundary_empty: "\<And>k w. \<not> binds_slot F None k w"
    and member: "v \<in> environment_uses E"
  shows "binds_slot (graft_environment E u F) v k w \<longleftrightarrow> binds_slot E v k w"
proof -
  have none: "\<not> binds_slot (rename_environment (fresh_use_map (environment_uses E) u) F) v k w"
    by (intro notI) (rule graft_imported_binding_no_old[OF ef boundary_empty member])
  show ?thesis using none by (simp add: graft_environment_def)
qed

text \<open>
  The optional address carrier is fixed and unbounded. A finite set of existing
  uses is reserved; the distinguished boundary use of a separate finite package
  is mapped to an explicitly selected existing use, and every other use is
  fresh. The prefix is a construction choice, not a stored role or an operation
  selector. Neither artifact addresses nor their payloads are changed by this
  map of external use occurrences.

  A graft shares only the explicitly identified boundary use. The imported
  package has no outgoing binding at that boundary; the existing package may
  have any formed outgoing bindings there. They are all preserved. Every other
  imported use is fresh, even when an artifact value is equal to an existing
  value. No global registry or mutation chooses these occurrences.
\<close>

section \<open>Combining separate finite environments without sharing uses\<close>

theorem disjoint_environment_extension:
  fixes E F :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and ff: "environment_formed F"
  shows "\<exists>H h. environment_formed H \<and> inj h \<and>
    environment_included E H \<and> environment_included (rename_environment h F) H \<and>
    range h \<inter> environment_uses E = {}"
proof -
  let ?U = "environment_uses E"
  let ?u = "fresh_use_map ?U None (Some [])"
  let ?h = "fresh_use_map ?U ?u"
  let ?F = "rename_environment ?h F"
  let ?H = "merge_environment E ?F"
  have fin: "finite ?U" by (rule environment_uses_finite[OF ef])
  have fresh: "?u \<notin> ?U" using fresh_use_map_outside[OF fin, of None "[]"] by blast
  have injective: "inj ?h" by (rule fresh_use_map_injective[OF fin])
  have outside: "\<And>v. ?h v \<notin> ?U"
    using fresh fresh_use_map_outside[OF fin, of ?u] by (case_tac v) auto
  have separate: "range ?h \<inter> ?U = {}" using outside by blast
  have imported: "environment_formed ?F" by (rule environment_renaming_formed[OF ff injective])
  have no_artifact: "\<And>v R S. artifact_at E v R \<Longrightarrow> artifact_at ?F v S \<Longrightarrow> False"
  proof -
    fix v R S assume old: "artifact_at E v R" and new: "artifact_at ?F v S"
    have member: "v \<in> ?U" using old by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
    obtain w where origin: "v = ?h w" using new by (auto simp only: artifact_at_renaming)
    show False using outside[of w] member origin by blast
  qed
  have no_binding: "\<And>v k x y. binds_slot E v k x \<Longrightarrow> binds_slot ?F v k y \<Longrightarrow> False"
  proof -
    fix v k x y assume old: "binds_slot E v k x" and new: "binds_slot ?F v k y"
    obtain R where old_source: "artifact_at E v R"
      using ef old unfolding environment_formed_def by blast
    obtain S where new_source: "artifact_at ?F v S"
      using imported new unfolding environment_formed_def by blast
    show False by (rule no_artifact[OF old_source new_source])
  qed
  have compatible: "environments_compatible E ?F"
    using no_artifact no_binding unfolding environments_compatible_def by blast
  have formed: "environment_formed ?H"
    using environment_merge_formed_iff[OF ef imported] compatible by blast
  show ?thesis using formed injective environment_included_merge_left[of E ?F]
      environment_included_merge_right[of ?F E] separate by blast
qed

text \<open>
  This construction reserves every existing use and places the complete
  imported environment at fresh uses. Equal artifact values remain separately
  placed, and every imported binding is carried with its source and target.
  The construction requires no common boundary and no empty outgoing scope.
\<close>

end
