theory Factor_Finite_Artifact_Enumeration
  imports RRA_Finite_Artifacts Factor_Material_Observation
begin

definition finite_enumerated_artifact ::
  "local_address list \<Rightarrow> (local_address \<times> local_address \<times> local_address) list \<Rightarrow>
    (local_address \<times> octets) list \<Rightarrow> (local_address \<times> octets) list \<Rightarrow> finite_exact_artifact" where
  "finite_enumerated_artifact A E B F =
    \<lparr>finite_structure = \<lparr>finite_carrier = fset_of_list A, finite_incidence = fset_of_list E\<rparr>,
     finite_data = \<lparr>finite_bag = mset B, finite_bindings = fset_of_list F\<rparr>\<rparr>"

lemma decode_finite_enumerated_artifact [simp]:
  "decode_finite_object (finite_enumerated_artifact A E B F) = enumerated_artifact A E B F"
  by (simp add: finite_enumerated_artifact_def enumerated_artifact_def decode_finite_object_def
      decode_finite_structure_def decode_finite_basis_def fset_of_list.rep_eq fun_eq_iff count_mset)

definition finite_artifact_enumeration ::
  "finite_exact_artifact \<Rightarrow> local_address list \<Rightarrow>
    (local_address \<times> local_address \<times> local_address) list \<Rightarrow>
    (local_address \<times> octets) list \<Rightarrow> (local_address \<times> octets) list \<Rightarrow> bool" where
  "finite_artifact_enumeration C A E B F \<longleftrightarrow>
    finite_exact_formed C \<and> distinct A \<and> distinct E \<and> distinct F \<and>
    C = finite_enumerated_artifact A E B F"

lemma finite_artifact_enumeration_correct:
  "finite_artifact_enumeration C A E B F \<longleftrightarrow>
    artifact_enumeration (decode_finite_object C) A E B F"
proof -
  have equal: "C = finite_enumerated_artifact A E B F \<longleftrightarrow>
    decode_finite_object C = enumerated_artifact A E B F"
    using decode_finite_object_injective[of C "finite_enumerated_artifact A E B F"] by simp
  show ?thesis by (simp add: finite_artifact_enumeration_def artifact_enumeration_def
      finite_exact_formed_correct equal)
qed

end
