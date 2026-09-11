theory Factor_Encoding_Order_Audit
  imports Factor_Finite_Terms Factor_Resource_Sensitivity
begin

section \<open>Exact finite-set recovery does not hide the chosen enumeration\<close>

lemma same_finite_entries_can_have_observable_order:
  assumes xf: "term_formed x" and yf: "term_formed y" and different: "x\<noteq>y"
  shows "set [x,y]=set [y,x]"
    "native_positive_holds
      (equality_query_environment (Pair_Term (enumeration_term [x,y]) (enumeration_term [x,y])))
      None [0] (Some []) []"
    "native_application_formed
      (equality_query_environment (Pair_Term (enumeration_term [y,x]) (enumeration_term [x,y])))
      None [0] (Some []) []"
    "\<not> native_positive_holds
      (equality_query_environment (Pair_Term (enumeration_term [y,x]) (enumeration_term [x,y])))
      None [0] (Some []) []"
proof -
  have left: "term_formed (enumeration_term [x,y])" and right: "term_formed (enumeration_term [y,x])"
    using xf yf by (simp_all add: enumeration_term_formed)
  have changed: "enumeration_term [x,y] \<noteq> enumeration_term [y,x]" using different by simp
  show "set [x,y]=set [y,x]" by auto
  show "native_positive_holds
      (equality_query_environment (Pair_Term (enumeration_term [x,y]) (enumeration_term [x,y])))
      None [0] (Some []) []"
    using native_context_equality(2)[OF left left] by simp
  show "native_application_formed
      (equality_query_environment (Pair_Term (enumeration_term [y,x]) (enumeration_term [x,y])))
      None [0] (Some []) []"
    by (rule native_context_equality(1)[OF right left])
  show "\<not> native_positive_holds
      (equality_query_environment (Pair_Term (enumeration_term [y,x]) (enumeration_term [x,y])))
      None [0] (Some []) []"
    using native_context_equality(2)[OF right left] changed by auto
qed

definition boolean_entry :: "bool \<Rightarrow> factor_term" where
  "boolean_entry b = (if b then Payload_Term [0] else Payload_Term [])"

lemma boolean_entry_formed [simp]: "term_formed (boolean_entry b)"
  by (simp add: boolean_entry_def octets_formed_def)

lemma canonical_boolean_set_term:
  "finite_set_term boolean_entry {False,True} = enumeration_term [boolean_entry False,boolean_entry True]"
  by (simp add: finite_set_term_def)

theorem canonical_set_order_changes_native_truth:
  "native_positive_holds
    (equality_query_environment
      (Pair_Term (finite_set_term boolean_entry {False,True})
        (enumeration_term [boolean_entry False,boolean_entry True])))
    None [0] (Some []) []"
  "\<not> native_positive_holds
    (equality_query_environment
      (Pair_Term (enumeration_term [boolean_entry True,boolean_entry False])
        (enumeration_term [boolean_entry False,boolean_entry True])))
    None [0] (Some []) []"
  using same_finite_entries_can_have_observable_order(2,4)
    [OF boolean_entry_formed[of False] boolean_entry_formed[of True]]
  by (simp_all add: canonical_boolean_set_term boolean_entry_def)

text \<open>
  The program is the existing closed native equality program in both calls.
  Reversing the enumeration preserves its finite set of entries and changes
  native truth. Canonical sorting selects one observable representation; an
  injective decoder alone cannot make that selection semantically neutral.
\<close>

end
