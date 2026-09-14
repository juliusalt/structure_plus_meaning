theory RRA_Finite_Environment_Construction
  imports RRA_Executable_Retention RRA_Literal_Extension
begin

section \<open>Complete finite environment operations decode to their original constructors\<close>

definition finite_add_artifact_use :: "'u finite_artifact_environment\<Rightarrow>'u\<Rightarrow>
    finite_exact_artifact\<Rightarrow>'u finite_artifact_environment" where
  "finite_add_artifact_use E u R=E\<lparr>finite_environment_artifacts:=finsert (u,R) (finite_environment_artifacts E)\<rparr>"

lemma decode_finite_add_artifact_use [simp]:
  "decode_finite_environment (finite_add_artifact_use E u R)=
    add_artifact_use (decode_finite_environment E) u (decode_finite_object R)"
  by (simp add: finite_add_artifact_use_def add_artifact_use_def decode_finite_environment_def
    map_relation_values_def)

definition finite_merge_environment :: "'u finite_artifact_environment\<Rightarrow>'u finite_artifact_environment\<Rightarrow>'u finite_artifact_environment" where
  "finite_merge_environment E F=\<lparr>
    finite_environment_artifacts=finite_environment_artifacts E |\<union>| finite_environment_artifacts F,
    finite_environment_bindings=finite_environment_bindings E |\<union>| finite_environment_bindings F\<rparr>"

lemma decode_finite_merge_environment [simp]:
  "decode_finite_environment (finite_merge_environment E F)=merge_environment (decode_finite_environment E) (decode_finite_environment F)"
  by (simp add: finite_merge_environment_def merge_environment_def decode_finite_environment_def
    map_relation_values_def image_Un)

definition finite_rename_environment :: "('u\<Rightarrow>'v)\<Rightarrow>'u finite_artifact_environment\<Rightarrow>'v finite_artifact_environment" where
  "finite_rename_environment h E=\<lparr>
    finite_environment_artifacts=fimage (\<lambda>(u,R). (h u,R)) (finite_environment_artifacts E),
    finite_environment_bindings=fimage (\<lambda>((u,k),v). ((h u,k),h v)) (finite_environment_bindings E)\<rparr>"

lemma decode_finite_rename_environment [simp]:
  "decode_finite_environment (finite_rename_environment h E)=rename_environment h (decode_finite_environment E)"
  by (simp add: finite_rename_environment_def rename_environment_def decode_finite_environment_def
    map_relation_values_def fimage.rep_eq image_image split_def)

fun finite_fresh_use_map :: "local_address option fset\<Rightarrow>local_address option\<Rightarrow>
    local_address option\<Rightarrow>local_address option" where
  "finite_fresh_use_map U u None=u"
| "finite_fresh_use_map U u (Some a)=Some (replicate (Suc (fMax (fimage use_word_length (finsert u U)))) 0 @ a)"

lemma finite_fresh_use_map_exact:
  "finite_fresh_use_map U u=fresh_use_map (fset U) u"
proof (rule ext)
  fix v
  show "finite_fresh_use_map U u v=fresh_use_map (fset U) u v"
    by (cases v) (simp_all add: fresh_use_prefix_def fMax.F.rep_eq fimage.rep_eq)
qed

definition finite_graft_environment :: "local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>local_address option finite_artifact_environment" where
  "finite_graft_environment E u F=finite_merge_environment E
    (finite_rename_environment (finite_fresh_use_map (finite_environment_uses E) u) F)"

lemma decode_finite_graft_environment [simp]:
  "decode_finite_environment (finite_graft_environment E u F)=
    graft_environment (decode_finite_environment E) u (decode_finite_environment F)"
  by (simp add: finite_graft_environment_def graft_environment_def finite_fresh_use_map_exact finite_environment_uses_correct)

definition finite_add_source_bindings :: "'u finite_artifact_environment\<Rightarrow>'u\<Rightarrow>
    (local_address\<times>'u) fset\<Rightarrow>'u finite_artifact_environment" where
  "finite_add_source_bindings E u D=E\<lparr>finite_environment_bindings:=finite_environment_bindings E |\<union>|
    fimage (\<lambda>(k,v). ((u,k),v)) D\<rparr>"

lemma decode_finite_add_source_bindings [simp]:
  "decode_finite_environment (finite_add_source_bindings E u D)=add_source_bindings (decode_finite_environment E) u (fset D)"
  by (simp add: finite_add_source_bindings_def add_source_bindings_def decode_finite_environment_def fimage.rep_eq)

definition finite_literal_environment :: "finite_exact_artifact\<Rightarrow>(local_address\<times>finite_exact_artifact) fset\<Rightarrow>
    local_address option finite_artifact_environment" where
  "finite_literal_environment R L=\<lparr>
    finite_environment_artifacts=finsert (None,R) (fimage (\<lambda>(k,S). (Some k,S)) L),
    finite_environment_bindings=fimage (\<lambda>k. ((None,k),Some k)) (fimage fst L)\<rparr>"

lemma decode_finite_literal_environment [simp]:
  "decode_finite_environment (finite_literal_environment R L)=
    literal_environment (decode_finite_object R) (map_relation_values decode_finite_object (fset L))"
  by (simp add: finite_literal_environment_def literal_environment_def decode_finite_environment_def
    map_relation_values_def fimage.rep_eq image_image split_def rel_dom_image)

definition finite_artifact_family_environment :: "'u fset\<Rightarrow>('u\<Rightarrow>finite_exact_artifact)\<Rightarrow>'u finite_artifact_environment" where
  "finite_artifact_family_environment U R=\<lparr>
    finite_environment_artifacts=fimage (\<lambda>u. (u,R u)) U,finite_environment_bindings={||}\<rparr>"

lemma decode_finite_artifact_family_environment [simp]:
  "decode_finite_environment (finite_artifact_family_environment U R)=
    artifact_family_environment (fset U) (\<lambda>u. decode_finite_object (R u))"
  by (simp add: finite_artifact_family_environment_def artifact_family_environment_def
    decode_finite_environment_def map_relation_values_def fimage.rep_eq image_image split_def)

export_code finite_add_artifact_use finite_merge_environment finite_rename_environment finite_fresh_use_map finite_graft_environment
  finite_add_source_bindings finite_literal_environment finite_artifact_family_environment checking SML

text \<open>
  The operations retain complete artifact and binding tables. Their decoding
  equations are exact environment equality. Fresh uses come from the original
  environment's finite use boundary, and grafting preserves its designated
  shared source. Formation and compatibility remain the prerequisites of the
  original environment-construction contracts.
\<close>

end
