theory Factor_Required_History_Cases
  imports Factor_Required_History_Methods Factor_Finite_Requirement_Decision_Replay
    Factor_Required_Cause_Cases
begin

lift_definition required_history_empty_ledger :: "required_history\<Rightarrow>required_history"
  is "\<lambda>q. q\<lparr>required_history_members:=[]\<rparr>"
  by (auto intro: finite_required_history_member_subset)

lemma required_history_empty_ledger_raw:
  "raw_required_history (required_history_empty_ledger q)=
    (raw_required_history q)\<lparr>required_history_members:=[]\<rparr>"
  by transfer simp

definition required_history_seed_replays where
  "required_history_seed_replays=(case required_cause_true_request of (S,su,sr,gs) \<Rightarrow>
    let R=finite_payload_syntax [61] in finite_requirement_decision_replay S su sr gs {|Finite_Target (Finite_Whole R)|})"

definition required_history_case_input where
  "required_history_case_input (w::nat) v replay=(case required_cause_request
      (if w=7 then 1 else if w=8 then 8 else if w=9 then 9 else if w=10 then 5 else 0)
      of (S,su,sr,gs) \<Rightarrow>
    case prepare_required_history S su sr gs of None \<Rightarrow> None | Some q0 \<Rightarrow>
    case replay of None \<Rightarrow> None | Some (A,M,root,graph,au,I,K,E) \<Rightarrow>
    let R=finite_payload_syntax [61];l=Finite_Whole (finite_payload_syntax [60]);
      prepared=(if w=1 \<or> w=2 \<or> w=3 \<or> w=4 then
        case required_history_step q0 l [] E v [] au [] root R of None \<Rightarrow> None | Some q1 \<Rightarrow>
          if w=2 then required_history_step q1 l (required_history_members (raw_required_history q1)) E v [] au [] root R
          else Some q1
        else Some q0)
    in case prepared of None \<Rightarrow> None | Some q \<Rightarrow>
      let rows=(if w=1 \<or> w=2 \<or> w=3 then required_history_members (raw_required_history q)
        else if w=4 then required_history_members (raw_required_history q) @ required_history_members (raw_required_history q) else []);
        state=(if w=3 then required_history_empty_ledger q else q);
        payload=(if w=5 then finite_payload_syntax [62] else R);
        target=(if w=6 then (Some [255],[]) else root);
        ambient=(if w=11 then finite_enumerated_environment [] [] else E)
      in Some (state,History_Step l rows ambient v [] au [] target payload))"

definition required_history_case where
  "required_history_case w=(case required_history_seed_replays of None \<Rightarrow> {|(None,None)|}
    | Some ((d,F,v,Q,D,A,T,Ys),replays) \<Rightarrow>
      if replays={||} then {|(None,None)|} else
      fimage (\<lambda>(key,replay). (Some key,required_history_case_input w v replay)) replays)"

definition required_history_subject_coverage ::
  "(required_history_certificate option\<times>required_history_subject option) fset\<Rightarrow>nat\<times>nat" where
  "required_history_subject_coverage subjects=(let positions=fimage
    (\<lambda>(key,input). (key,case input of None \<Rightarrow> False | Some X \<Rightarrow> True)) subjects
    in (fcard positions,fcard (ffilter snd positions)))"

text \<open>
  Actual original requirement evaluation supplies the full certificate and
  replay family. The history API supplies zero, one or two preceding steps.
  A proved invariant-preserving fixture removes ledger entries while retaining
  their actual material; it tests membership separately from generation reading
  and is not claimed reachable through the production API. Other cases use
  duplicate predecessors, a changed payload or root, a different original
  policy, unavailable preparation and an absent replay environment. No supplied
  validity flag or expected satisfaction table enters these constructions.
\<close>

end
