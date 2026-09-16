theory Factor_Steered_Execution_Sharing
  imports Factor_Steered_Development Factor_Development_Execution_Sharing
begin

declare steered_development_result_def[code del]

lemma steered_development_result_prepared_code [code]:
  "steered_development_result m Q=(let original=construct_native_development Q;
    admit=prepared_computed_function (native_development_admission Q) [original];
    actual=development_producer_from m Q original (admit original);
    admission=admit (fst actual)
    in (m,Q,fst actual,snd actual,if snd actual=admission then admission else None))"
  by (simp only: prepared_computed_function_exact steered_development_result_def
    development_producer_def Let_def)

text \<open>The producer and the subsequent request check share the actual
  original admission through the existing exact computed-function contract.
  An equal complete report reads that result; a changed report executes the
  original admission under this request. No producer identifier, claimed
  decision, prior policy scope or omitted condition justifies a cache hit.\<close>

end
