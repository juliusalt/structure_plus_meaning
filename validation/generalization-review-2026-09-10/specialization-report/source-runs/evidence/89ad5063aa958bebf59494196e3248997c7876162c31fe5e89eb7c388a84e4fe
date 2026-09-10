theory Factor_Scoped_Transport
  imports Factor_Presentation
begin

section \<open>Copying a complete private binder scope\<close>

theorem scoped_pattern_transport:
  assumes scoped: "scoped_pattern_at E u r p I K" and source: "artifact_at E u R"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (f ` I)"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    and injective: "inj f" and ff: "environment_formed F" and target: "artifact_at F w S"
  shows "scoped_pattern_at F w (f r) (rename_pattern f p) (f ` I) (f ` K)"
proof -
  have ef: "environment_formed E" using scoped by (simp add: scoped_pattern_at_def)
  obtain T ports b q V J where parts: "artifact_at E u T" "record_at T r ports [b,q]"
    "binder_scope_at T b V" "pattern_quoted_at E u V q p J K" "V=pattern_variables p"
    "insert r (set ports) \<inter> (insert b V \<union> J) = {}" "insert b V \<inter> J = {}"
    "I=insert r (set ports \<union> insert b V \<union> J)" "I \<inter> K = {}"
    using scoped by (auto simp: scoped_pattern_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF ef parts(1) source])
  have rec: "record_at R r ports [b,q]" and scope: "binder_scope_at R b V" using parts(2,3) same by simp_all
  have local_inj: "inj_on f (rra_carrier (object_structure R))" using injective by (auto simp: inj_on_def)
  have sf: "object_formed S" using ff target by (auto simp: environment_formed_def exact_formed_def)
  have copied_rec: "record_at (push_object f R) (f r) (map f ports) [f b,f q]"
    using record_at_push[OF rec local_inj] by simp
  have new_rec: "record_at S (f r) (map f ports) [f b,f q]"
    by (rule record_at_read_transport[OF copied_rec sf reads]) (use parts(8) in auto)
  have copied_scope: "binder_scope_at (push_object f R) (f b) (f ` V)"
    by (rule binder_scope_push[OF scope local_inj])
  have copied_family: "family_at (push_object f R) (f b) ((\<lambda>a. (a,a)) ` (f ` V))"
    using copied_scope by (simp add: binder_scope_at_def)
  have new_family: "family_at S (f b) ((\<lambda>a. (a,a)) ` (f ` V))"
    by (rule family_at_read_transport[OF copied_family sf reads])
       (use parts(8) in \<open>auto simp: rel_dom_def\<close>)
  have new_scope: "binder_scope_at S (f b) (f ` V)" using new_family by (simp add: binder_scope_at_def)
  have body_reads: "object_reads_agree (push_object f R) S (f ` J)"
    by (rule object_reads_agree_mono[OF reads]) (use parts(8) in blast)
  have body: "pattern_quoted_at F w (f ` V) (f q) (rename_pattern f p) (f ` J) (f ` K)"
    by (rule pattern_quotation_transport[OF parts(4) source addressing body_reads slots injective ff target])
  have variables: "f ` V = pattern_variables (rename_pattern f p)"
    by (simp add: parts(5) rename_pattern_variables)
  have top_separate: "insert (f r) (set (map f ports)) \<inter> (insert (f b) (f ` V) \<union> f ` J) = {}"
    using image_Int[OF injective, of "insert r (set ports)" "insert b V \<union> J"] parts(6)
    by (simp add: image_Un)
  have scope_separate: "insert (f b) (f ` V) \<inter> f ` J = {}"
    using image_Int[OF injective, of "insert b V" J] parts(7) by simp
  have key_separate: "f ` I \<inter> f ` K = {}"
    using image_Int[OF injective, of I K] parts(9) by simp
  show ?thesis unfolding scoped_pattern_at_def
    apply (rule conjI[OF ff])
    apply (rule exI[of _ S], rule exI[of _ "map f ports"], rule exI[of _ "f b"],
        rule exI[of _ "f q"], rule exI[of _ "f ` V"], rule exI[of _ "f ` J"])
    using target new_rec new_scope body variables top_separate scope_separate key_separate parts(8)
    by (simp add: image_Un)
qed

text \<open>
  A complete scope can be copied with all its binder positions renamed along
  with its body and declaration. Thus separate scoped blocks need not share
  binders when they are composed. Literal values stay fixed, while complete
  syntax, the exact declared variable set, and the external slots are transported.
\<close>

end
