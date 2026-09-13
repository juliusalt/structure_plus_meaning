theory Factor_Native_History_Cases
  imports Factor_Finite_Native_Histories Factor_Native_Evaluation_Cases
begin

type_synonym native_history_call = "local_address option definition_site\<times>finite_factor_term"
type_synonym native_history_application =
  "local_address option definition_site\<times>local_address\<times>finite_factor_term\<times>
    (local_address\<times>finite_factor_term) fset\<times>(local_address\<times>native_history_call) fset"
type_synonym native_history_steps = "(native_history_call fset\<times>native_history_application fset) list"
type_synonym native_history_result =
  "(local_address option finite_native_system\<times>native_history_call fset\<times>native_history_steps) option"
type_synonym native_history_problem =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    native_history_call fset"

definition native_history_empty_program :: "local_address option finite_native_system" where
  "native_history_empty_program=\<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr>"

definition native_history_compiled_problem :: "nat\<Rightarrow>native_history_problem option" where
  "native_history_compiled_problem i=(let E=finite_guard_source False;
    P=finite_nat_guard_source_model False; Q=fst (program_evaluation_subject i); D=snd (program_evaluation_subject i);
    h=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) native_guard_source_coordinate
    in map_option (\<lambda>(F,u). (F,u,[],fimage (\<lambda>(d,t). (h d,t)) D))
      (finite_extend_mapped_native E P Q native_guard_source_coordinate))"

definition native_history_closed_negative_problem :: "native_history_problem option" where
  "native_history_closed_negative_problem=map_option (\<lambda>(E,u,r,D).
    (E,u,r,{|(native_guard_source_coordinate 0,Finite_Payload [])|})) (native_history_compiled_problem 13)"

definition native_history_problem :: "nat\<Rightarrow>native_history_problem option" where
  "native_history_problem i=(if i<21 then map_option (\<lambda>(E,u,r,focus,source,D). (E,u,r,D))
    (native_evaluation_input i) else if i<25 then native_history_compiled_problem ([9,12,13,14]!(i-21))
    else if i=25 then native_history_closed_negative_problem else None)"

definition native_history_expanded_demand :: "native_history_call fset\<Rightarrow>native_history_call fset" where
  "native_history_expanded_demand D=D |\<union>| fimage (\<lambda>(d,t). (d,Finite_Pair t t)) D"

definition native_history_expanded_answer where
  "native_history_expanded_answer P D A=(case finite_program_evaluation P (native_history_expanded_demand D) of
    None \<Rightarrow> A | Some B \<Rightarrow> B)"

lemma native_history_expanded_answer_properties:
  assumes original: "finite_program_evaluation P D=Some A"
  shows "A |\<subseteq>| native_history_expanded_answer P D A"
    "\<forall>q\<in>fset (native_history_expanded_answer P D A).
      decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  have demand: "D |\<subseteq>| native_history_expanded_demand D"
    by (simp add: native_history_expanded_demand_def)
  show "A |\<subseteq>| native_history_expanded_answer P D A"
    using finite_program_evaluation_demand_included[OF original _ demand]
    by (cases "finite_program_evaluation P (native_history_expanded_demand D)")
      (auto simp: native_history_expanded_answer_def)
  show "\<forall>q\<in>fset (native_history_expanded_answer P D A).
      decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    using finite_program_evaluation_exact(2)[OF original]
      finite_program_evaluation_exact(2)[of P "native_history_expanded_demand D"]
    by (cases "finite_program_evaluation P (native_history_expanded_demand D)")
      (auto simp: native_history_expanded_answer_def)
qed

definition native_history_global_head_covered where
  "native_history_global_head_covered P=finite_program_head_covered P
    (fimage (\<lambda>d. (d,Finite_Payload [])) (finite_system_definitions P))"

definition native_history_variant ::
    "nat\<Rightarrow>native_history_call fset\<Rightarrow>
      (local_address option finite_native_system\<times>native_history_call fset\<times>native_history_steps)\<Rightarrow>
      (local_address option finite_native_system\<times>native_history_call fset\<times>native_history_steps)" where
  "native_history_variant m D result=(case result of (P,A,Hs) \<Rightarrow>
    (if m=7 then native_history_empty_program else P,
      if m=5 then D else if m=9 then native_history_expanded_answer P D A else A,
      if m=1 then [] else if m=2 then rev Hs else
      map (\<lambda>(X,W). (X,fimage (\<lambda>(d,c,t,V,H).
        (d,c,t,if m=4 then {||} else V,if m=3 then {||} else H)) W)) Hs))"

definition native_history_apply :: "nat\<Rightarrow>native_history_call fset\<Rightarrow>native_history_result\<Rightarrow>native_history_result" where
  "native_history_apply m D history=(if m=6 then None else case history of
      None \<Rightarrow> (if m=8 then Some (native_history_empty_program,D,[]) else None)
    | Some result \<Rightarrow> if m=10 \<and> \<not>native_history_global_head_covered (fst result) then None
      else Some (native_history_variant m D result))"

definition native_history_method :: "nat\<Rightarrow>native_history_problem\<Rightarrow>native_history_result" where
  "native_history_method m X=(case X of (E,u,r,D) \<Rightarrow>
    native_history_apply m D (finite_native_program_history E u r D))"

lemma native_history_variant_original:
  "native_history_variant 0 D result=result"
  by (cases result) (simp add: native_history_variant_def case_prod_eta split_def)

lemma native_history_method_original:
  "native_history_method 0 (E,u,r,D)=finite_native_program_history E u r D"
  by (simp add: native_history_method_def native_history_apply_def native_history_variant_original split: option.splits)

definition native_history_methods :: "nat list" where
  "native_history_methods=[0,1,2,3,4,5,6,7,8,9,10]"
definition native_history_indices :: "nat list" where
  "native_history_indices=[0..<26]"

definition native_history_source_report where
  "native_history_source_report X=(case X of (E,u,r,D) \<Rightarrow>
    let source=finite_native_source E u r in (source,
      map_option (\<lambda>P. (finite_system_formed P,finite_program_head_covered P D,
        finite_program_demand_closed P D,finite_program_applications P D)) source,
      finite_native_program_evaluation E u r D,
      (native_history_expanded_demand D,map_option native_history_global_head_covered source,
        finite_native_program_evaluation E u r (native_history_expanded_demand D))))"

definition native_history_report where
  "native_history_report i=map_option (\<lambda>X. (X,native_history_source_report X,
    map (\<lambda>m. (m,native_history_method m X)) native_history_methods)) (native_history_problem i)"

export_code native_history_report native_history_indices native_history_methods checking SML

text \<open>
  The actual source environment and requested calls are the complete inputs.
  The original evaluator cases supply those values without candidate answers.
  Each candidate computes an actual history or changes its returned fields.
  The changes erase or reverse steps, erase premise or binding families, claim
  every requested answer, return no evidence, replace the claimed program,
  or fabricate evidence when the source or evaluation prerequisites fail.
  Missing problem construction remains distinct from an existing invalid source.

  Four further inputs compile the original hidden-variable and growing-premise
  programs. Their requested calls distinguish missing head coverage, an open
  demand, a closed demand with two positive calls, and an unrequested clause
  whose head is not covered. A further closed demand requests only the original
  equality guard at an empty payload and retains its computed negative answer. Every demand uses the actual constructed source
  coordinates. Two further methods return the evaluator's answer on an
  expanded demand or reject a source because of an unrequested uncovered head.
  The expanded-answer theorem establishes the original positive meaning of
  every added call. Requested membership remains a separate requirement.
\<close>

end
