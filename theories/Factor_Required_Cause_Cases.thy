theory Factor_Required_Cause_Cases
  imports Factor_Finite_Required_Causes Factor_Certified_Cause_Variants Factor_Requirement_Source_Examples_Base
begin

type_synonym required_cause_request = "local_address option finite_artifact_environment\<times>
  local_address option\<times>local_address\<times>local_address option definition_site admission_goal list"
type_synonym required_cause_subject = "required_cause_request\<times>certified_cause_subject"

definition required_cause_true_request :: required_cause_request where
  "required_cause_true_request=(finite_guard_source True,None,[0],[Existing_Admission (None,[1])])"

definition required_cause_request :: "nat\<Rightarrow>required_cause_request" where
  "required_cause_request w=(case required_cause_true_request of (S,su,sr,gs) \<Rightarrow>
    if w=1 then (finite_guard_source False,su,sr,gs)
    else if w=5 then (finite_add_artifact_use S (Some [255]) (finite_payload_syntax [256]),su,sr,gs)
    else if w=8 then (S,su,sr,[])
    else if w=9 then (S,su,sr,[Existing_Admission (Some [255],[])])
    else (S,su,sr,gs))"

definition required_cause_record_family where
  "required_cause_record_family w=(case required_cause_true_request of (S,su,sr,gs) \<Rightarrow>
    case finite_construct_source_requirements S su sr gs of None \<Rightarrow> {|(None,None)|}
    | Some (d,K,pu) \<Rightarrow> let R=finite_payload_syntax [61]; t=Finite_Target (Finite_Whole R);
      A=(if w=3 then certified_cause_changed_replay K pu else K);
      called=(if w=2 then (None,[1]) else d) in
      case finite_native_source A pu [] of None \<Rightarrow> {|(None,None)|}
      | Some Q \<Rightarrow> case finite_native_program_proofs A pu [] (finite_program_term_demand Q {|t|}) of
        None \<Rightarrow> {|(None,None)|}
      | Some (P,B,T) \<Rightarrow> let selected=ffilter (\<lambda>((e,v),p). e=called \<and> v=t) T;
          replays=finite_certificate_replays A pu [] selected in
          if selected={||} then {|(None,None)|} else
          fimage (\<lambda>(key,result). (Some key,case result of None \<Rightarrow> None
            | Some (N,M,root,graph,au,I,J,H) \<Rightarrow>
              let X=(H,pu,[],au,[],root,R) in
              case certified_cause_seed_record X of None \<Rightarrow> None
                | Some built \<Rightarrow> certified_cause_variant
                  (if w=4 then 2 else if w=6 then 7 else if w=7 then 6 else 0) X built)) replays)"

definition required_cause_family where
  "required_cause_family w=fimage (\<lambda>(key,result). (key,map_option (Pair (required_cause_request w)) result))
    (required_cause_record_family w)"

definition required_cause_holds :: "required_cause_subject\<Rightarrow>bool" where
  "required_cause_holds X=(case X of ((S,su,sr,gs),(E,gu,gr,G,H,root,R)) \<Rightarrow>
    case finite_construct_source_requirements S su sr gs of None \<Rightarrow> False
    | Some (d,K,pu) \<Rightarrow> certified_policy_cause_at (decode_finite_environment K) pu [] d
      (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R))"

definition required_cause_direct :: "required_cause_subject\<Rightarrow>bool" where
  "required_cause_direct X=(case X of ((S,su,sr,gs),(E,gu,gr,G,H,root,R)) \<Rightarrow>
    finite_required_cause S su sr gs E gu gr G H root R)"

lemma required_cause_direct_exact:
  "required_cause_direct X=required_cause_holds X"
  by (cases X) (simp add: required_cause_direct_def required_cause_holds_def finite_required_cause_def
    finite_certified_policy_cause_exact split: prod.splits option.splits)

definition required_cause_covered where
  "required_cause_covered=fBex (required_cause_family 0)
    (\<lambda>(key,result). case result of None \<Rightarrow> False | Some X \<Rightarrow> required_cause_direct X)"

lemma required_cause_covered_exact:
  "required_cause_covered \<longleftrightarrow>
    (\<exists>key X. (key,Some X) |\<in>| required_cause_family 0 \<and> required_cause_holds X)"
  by (simp only: required_cause_covered_def required_cause_direct_exact finite_optional_relation_exists)

text \<open>
  The fixture's original policy has a nonempty requirement family over an
  actual native source clause. Native evaluation derives every selected
  certificate; actual replay and record constructors produce the subject.
  Failure before a certificate exists is an explicit absent-key position.

  Cases replace the expected original policy, change the called entry, alter
  the whole policy artifact while keeping its local program, remove proof,
  shift or reorder the cause quotation, or make the original request unavailable.
  The checker supplies every outcome. The test policy is not claimed to cover
  the full development workflow.
\<close>

end
