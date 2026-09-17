theory Factor_Native_Derivation_Cases
  imports Factor_Finite_Native_Proof_Construction Factor_Finite_Proof_Checking Factor_Native_History_Cases
begin

type_synonym native_derivation_tree = "(local_address,local_address,local_address) finite_schema_proof"
type_synonym native_derivation_family = "(native_history_call\<times>native_derivation_tree) fset"
type_synonym native_derivation_result =
  "(local_address option finite_native_system\<times>native_history_call fset\<times>native_derivation_family) option"

fun native_derivation_alter_root :: "nat\<Rightarrow>native_derivation_tree\<Rightarrow>native_derivation_tree" where
  "native_derivation_alter_root m (Schema_Proof c V B)=
    Schema_Proof (if m=4 then [] else c)
      (if m=3 then {||} else if m=13 then fimage (map_prod id (\<lambda>_. Finite_Payload [255])) V else V)
      (if m=2 then {||} else B)"

lemma native_derivation_alter_root_original:
  "native_derivation_alter_root 0 p=p"
  by (cases p) simp

fun native_derivation_alter_children :: "nat\<Rightarrow>native_derivation_tree\<Rightarrow>native_derivation_tree" where
  "native_derivation_alter_children m (Schema_Proof c V B)=Schema_Proof c V
    (if m=11 then fimage (map_prod id (native_derivation_alter_root 4)) B
      else if m=12 then B |\<union>| fimage (map_prod id (native_derivation_alter_root 4)) B else B)"

lemma native_derivation_child_fields:
  assumes "native_derivation_alter_children m (Schema_Proof c V B)=Schema_Proof c' V' C"
  shows "c'=c" "V'=V" "fimage fst C=fimage fst B"
proof -
  let ?C="if m=11 then fimage (map_prod id (native_derivation_alter_root 4)) B
    else if m=12 then B |\<union>| fimage (map_prod id (native_derivation_alter_root 4)) B else B"
  have fields: "c'=c \<and> V'=V \<and> C=?C" using assms by simp
  have domain: "fimage fst ?C=fimage fst B"
    by (simp add: fimage_funion finite_value_image_domain split: if_splits)
  show "c'=c" "V'=V" "fimage fst C=fimage fst B" using fields domain by blast+
qed

lemma native_derivation_changed_binding_fields:
  assumes "native_derivation_alter_root 13 (Schema_Proof c V B)=Schema_Proof c' V' C"
  shows "c'=c" "C=B" "fimage fst V'=fimage fst V"
    "fBall V' (\<lambda>(a,t). finite_term_formed t)"
proof -
  have fields: "c'=c \<and> C=B \<and> V'=fimage (map_prod id (\<lambda>_. Finite_Payload [255])) V"
    using assms by simp
  show "c'=c" "C=B" using fields by blast+
  show "fimage fst V'=fimage fst V" using fields by (simp only: finite_value_image_domain; blast)
  show "fBall V' (\<lambda>(a,t). finite_term_formed t)"
    using fields by (auto simp: octets_formed_def map_prod_def)
qed

definition native_derivation_variant :: "nat\<Rightarrow>native_history_call fset\<Rightarrow>
    (local_address option finite_native_system\<times>native_history_call fset\<times>native_derivation_family)\<Rightarrow>
    (local_address option finite_native_system\<times>native_history_call fset\<times>native_derivation_family)" where
  "native_derivation_variant m D v=(case v of (P,A,T) \<Rightarrow>
    let U=(if m=1 then {||} else if m=8 then ffilter (\<lambda>((d,t),p). t=Finite_Payload [1]) T
      else if m=11 \<or> m=12 then fimage (map_prod id (native_derivation_alter_children m)) T
      else fimage (map_prod id (native_derivation_alter_root m)) T)
    in (if m=7 then native_history_empty_program else P,if m=5 then D else if m=8 then fimage fst U else A,U))"

definition native_derivation_base :: "native_history_problem\<Rightarrow>native_derivation_result" where
  "native_derivation_base X=(case X of (E,u,r,D) \<Rightarrow> finite_native_program_proofs E u r D)"

definition native_derivation_expansion :: "native_history_problem\<Rightarrow>native_derivation_result" where
  "native_derivation_expansion X=(case X of (E,u,r,D) \<Rightarrow>
    finite_native_program_proofs E u r (native_history_expanded_demand D))"

definition native_derivation_apply_values ::
    "nat\<Rightarrow>native_history_problem\<Rightarrow>native_derivation_result\<Rightarrow>native_derivation_result\<Rightarrow>native_derivation_result" where
  "native_derivation_apply_values m X base expanded=(case X of (E,u,r,D) \<Rightarrow>
    if m=6 then None else case base of None \<Rightarrow>
      (if m=10 then Some (native_history_empty_program,D,{||}) else None)
    | Some v \<Rightarrow> if m=9 \<or> m=14 then
        (case expanded of None \<Rightarrow> Some v
          | Some wider \<Rightarrow> Some (if m=14 then (fst v,fst (snd v),snd (snd wider)) else wider))
      else Some (native_derivation_variant m D v))"

definition native_derivation_apply ::
    "nat\<Rightarrow>native_history_problem\<Rightarrow>native_derivation_result\<Rightarrow>native_derivation_result" where
  "native_derivation_apply m X base=native_derivation_apply_values m X base
    (if (m=9 \<or> m=14) \<and> base\<noteq>None then native_derivation_expansion X else None)"

lemma native_derivation_apply_values_actual:
  "native_derivation_apply_values m X base (native_derivation_expansion X)=native_derivation_apply m X base"
  by (cases X; cases base)
    (auto simp: native_derivation_apply_values_def native_derivation_apply_def split: if_splits)

definition native_derivation_method :: "nat\<Rightarrow>native_history_problem\<Rightarrow>native_derivation_result" where
  "native_derivation_method m X=native_derivation_apply m X (native_derivation_base X)"

lemma native_derivation_variant_original:
  "native_derivation_variant 0 D v=v"
  by (cases v) (simp add: native_derivation_variant_def native_derivation_alter_root_original
    Let_def split_def map_prod_def)

lemma native_derivation_method_original:
  "native_derivation_method 0 (E,u,r,D)=finite_native_program_proofs E u r D"
  by (simp add: native_derivation_method_def native_derivation_base_def native_derivation_apply_def native_derivation_apply_values_def
    native_derivation_variant_original split: option.splits)

definition native_derivation_methods :: "nat list" where
  "native_derivation_methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]"
definition native_derivation_indices :: "nat list" where
  "native_derivation_indices=native_history_indices"

text \<open>
  The existing twenty-six native history problems supply complete original
  environments and requests. Candidates construct actual certificates, erase
  proof families or root metadata, change claimed answers or source identity,
  return an actual supported subfamily, or evaluate an expanded request.
  A separate control fabricates answers on unavailable original inputs.
  Every mutation remains an actual finite structural value; the independent
  proof checker must assess each complete certificate against the original
  source. These values still require native graph construction and placement.

  Further controls preserve root metadata while corrupting children or adding
  conflicting children, preserve binding keys while substituting formed wrong
  values, and retain original answers while returning actual extra certificates.
  The shared expansion is an actual source computation and supplies no
  satisfaction table. Every candidate is still inspected independently.
\<close>

end
