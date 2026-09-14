theory RRA_Environment_Update_References
  imports RRA_Indexed_Environment_Views Finite_Relation_Reader_Assessments RRA_Finite_Syntax_Construction
begin

datatype environment_update = Install_Artifact "local_address option" finite_exact_artifact
  | Install_Binding "local_address option" local_address "local_address option"

type_synonym environment_update_subject =
  "(local_address option\<times>finite_exact_artifact) list\<times>
    ((local_address option\<times>local_address)\<times>local_address option) list\<times>environment_update"

fun original_environment_update_ready where
  "original_environment_update_ready E (Install_Artifact u R)=(exact_formed (decode_finite_object R) \<and>
    u\<notin>environment_uses E)"
| "original_environment_update_ready E (Install_Binding u k v)=
    ((\<exists>R. artifact_at E u R \<and> k\<in>rra_carrier (object_structure R)) \<and>
      v\<in>environment_uses E \<and> (\<forall>w. \<not>binds_slot E u k w))"

fun original_environment_update_body where
  "original_environment_update_body E (Install_Artifact u R)=add_artifact_use E u (decode_finite_object R)"
| "original_environment_update_body E (Install_Binding u k v)=add_source_bindings E u {(k,v)}"

fun finite_environment_update_ready where
  "finite_environment_update_ready E (Install_Artifact u R)=(finite_exact_formed R \<and>
    \<not>fBex (finite_environment_artifacts E) (\<lambda>(v,C). v=u))"
| "finite_environment_update_ready E (Install_Binding u k v)=(
    fBex (finite_environment_artifacts E) (\<lambda>(w,R). w=u \<and> k |\<in>| finite_carrier (finite_structure R)) \<and>
    fBex (finite_environment_artifacts E) (\<lambda>(w,R). w=v) \<and>
    \<not>fBex (finite_environment_bindings E) (\<lambda>((w,j),z). w=u \<and> j=k))"

fun finite_environment_update_body where
  "finite_environment_update_body E (Install_Artifact u R)=finite_add_artifact_use E u R"
| "finite_environment_update_body E (Install_Binding u k v)=finite_add_source_bindings E u {|(k,v)|}"

lemma finite_environment_update_ready_exact:
  "finite_environment_update_ready E op=original_environment_update_ready (decode_finite_environment E) op"
  apply (cases op)
   apply (simp_all only: finite_environment_update_ready.simps original_environment_update_ready.simps
     finite_exact_formed_correct decode_finite_environment_slot finite_environment_uses_correct[symmetric])
  by (auto simp: finite_environment_uses_def fimage.rep_eq binds_slot_def Bex_def split_paired_Ex intro: rev_image_eqI)

lemma finite_environment_update_body_exact:
  "decode_finite_environment (finite_environment_update_body E op)=
    original_environment_update_body (decode_finite_environment E) op"
  by (cases op) simp_all

definition environment_update_relation where
  "environment_update_relation X F=(case X of (A,B,op) \<Rightarrow>
    let E=decode_finite_environment (finite_enumerated_environment A B) in
      environment_formed E \<and> original_environment_update_ready E op \<and>
        decode_finite_environment F=original_environment_update_body E op)"

definition environment_update_reference where
  "environment_update_reference X=(case X of (A,B,op) \<Rightarrow>
    let E=finite_enumerated_environment A B in
      if finite_environment_formed E \<and> finite_environment_update_ready E op
        then {|finite_environment_update_body E op|} else {||})"

lemma environment_update_reference_exact:
  "F |\<in>| environment_update_reference X \<longleftrightarrow> environment_update_relation X F"
proof -
  obtain A B op where shape: "X=(A,B,op)" by (cases X) auto
  show ?thesis
    by (simp only: shape environment_update_reference_def environment_update_relation_def
      case_prod_conv Let_def finite_environment_formed_correct finite_environment_update_ready_exact
      finite_environment_update_body_exact[symmetric]; auto)
qed

end
