theory Factor_Required_History_Methods
  imports Factor_Required_History_References Factor_Finite_Derivations
begin

type_synonym required_history_certificate =
  "(local_address option definition_site\<times>finite_factor_term)\<times>
    (local_address,local_address,local_address) finite_schema_proof"
type_synonym required_history_result_row =
  "required_history_certificate option\<times>finite_required_history_state option option"

definition required_history_inspect ::
  "(required_history_result_row fset\<times>required_history_result_row fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "required_history_inspect=finite_reader_inspect"

definition required_history_variant where
  "required_history_variant (m::nat) q l rows E pu pr au ar root R=(
    if m=5 then None else if m=6 then Some q else
    if m\<noteq>2 \<and> \<not>list_all (\<lambda>row. row\<in>set (required_history_members q)) rows then None else
    let generated=(if m=4 then
      case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> map_option (\<lambda>(A,u,G). (A,u,G,J,C))
        (finite_construct_generation_record (required_history_material q) l (Finite_Whole R) (Finite_Whole C) rows)
      else finite_record_native_replay (required_history_material q) l rows E pu pr au ar root R)
    in case generated of None \<Rightarrow> None | Some (A,u,G,J,C) \<Rightarrow>
      if m=3 \<or> m=4 \<or> finite_certified_policy_cause (required_history_policy q)
          (required_history_policy_use q) [] (required_history_entry q) A u [] G E root R
      then Some (q\<lparr>required_history_material:=A,
        required_history_members:=(if m=7 then [] else ((u,[]),G)#required_history_members q),
        required_history_goals:=(if m=8 then [] else required_history_goals q)\<rparr>) else None)"

fun required_history_method where
  "required_history_method (m::nat) (q,History_Step l rows E pu pr au ar root R)=(
    if m=0 then map_option raw_required_history (required_history_step q l rows E pu pr au ar root R)
    else if m=1 then finite_required_history_step (raw_required_history q) l rows E pu pr au ar root R
    else required_history_variant m (raw_required_history q) l rows E pu pr au ar root R)"

theorem required_history_correct_methods:
  assumes method: "m\<in>{0,1}"
  shows "required_history_method m X=required_history_reference_option X"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  show ?thesis using method by (cases input) (auto simp: shape required_history_step_raw)
qed

definition required_history_family_reference where
  "required_history_family_reference subjects=fimage (\<lambda>(key,input).
    (key,map_option required_history_reference_option input)) subjects"

definition required_history_family_base where
  "required_history_family_base m subjects=fimage (\<lambda>(key,input).
    (key,map_option (required_history_method m) input)) subjects"

definition required_history_family_method where
  "required_history_family_method (m::nat) subjects=(
    if m=9 then {||}
    else if m=10 then finsert (None,None) (required_history_family_reference subjects)
    else if m=11 then fimage (\<lambda>(key,result).
      (key,Some (case result of None \<Rightarrow> None | Some following \<Rightarrow> following)))
      (required_history_family_reference subjects)
    else required_history_family_base m subjects)"

lemma required_history_family_previous:
  "m<9 \<Longrightarrow> required_history_family_method m subjects=required_history_family_base m subjects"
  by (auto simp: required_history_family_method_def)

definition required_history_family_condition where
  "required_history_family_condition f method subjects=relation_reader_condition
    (\<lambda>row. row |\<in>| required_history_family_reference subjects) f (method subjects)"

definition required_history_context where
  "required_history_context subjects=(subjects,required_history_family_reference subjects)"

definition required_history_assessment where
  "required_history_assessment m context=(case context of (subjects,reference) \<Rightarrow>
    (required_history_family_method m subjects,reference))"

lemma required_history_assessment_exact:
  "required_history_inspect (required_history_assessment m (required_history_context subjects)) f=
    required_history_family_condition f (required_history_family_method m) subjects"
  by (simp only: required_history_inspect_def required_history_assessment_def required_history_context_def case_prod_conv
      required_history_family_condition_def finite_reader_inspect_exact[OF refl])

text \<open>
  The original methods retain each key, absent input and optional output. Candidates
  include the typed API, its raw operation, omission of predecessor membership
  or policy, quotation without replay and policy, refusal, a no-op, deletion of
  the ledger, and alteration of the original goals. Three family controls remove
  every row, add an actual absent-key row, or conflate unavailable input with
  rejected output. Complete state and family comparison
  observes these differences even when a weaker invariant still holds.
\<close>

end
