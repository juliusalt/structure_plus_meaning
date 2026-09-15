theory Factor_Quoted_Policy_Attempts
  imports Factor_Known_Replay_Policy
begin

definition quoted_policy_attempt where
  "quoted_policy_attempt construct K ku entry H l rows E pu pr au ar R=(
    case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
    | Some (J,C) \<Rightarrow> if replay_policy_condition K ku [] entry R J pu pr au ar then
        construct H l (Finite_Whole R) (Finite_Whole C) rows else None)"

declare policy_record_replay_from_source_def[code del]

lemma policy_record_replay_from_source_factored [code]:
  "policy_record_replay_from_source construct K ku entry H l rows E pu pr au ar root R=(
    if finite_literal_replay_ready E pu pr au ar root R then
      quoted_policy_attempt construct K ku entry H l rows E pu pr au ar R else None)"
  by (simp only: policy_record_replay_from_source_def quoted_policy_attempt_def)

text \<open>
  The actual quotation and package-policy alignment operation is factored from
  its original literal replay guard. The complete proved operation retains
  that guard. A control may call the quotation attempt alone so that the native
  comparison can expose the missing replay premise without also removing policy.
\<close>

end
