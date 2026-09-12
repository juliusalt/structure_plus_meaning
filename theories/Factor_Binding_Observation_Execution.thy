theory Factor_Binding_Observation_Execution
  imports Factor_Binding_Observation_Contracts Factor_Executable_Data_Values Option_List_Maps
begin

section \<open>The native row operation constructs its selected value\<close>

definition finite_binding_observation_row ::
  "bool\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term option" where
  "finite_binding_observation_row first u r=(case r of Finite_Pair k v \<Rightarrow>
    (case k of Finite_Pair owner a \<Rightarrow>
      (case v of Finite_Pair x y \<Rightarrow>
        (if owner=u \<and> finite_term_formed u \<and> finite_term_formed a \<and>
            finite_term_formed x \<and> finite_term_formed y
         then Some (Finite_Pair a (if first then x else y)) else None)
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
   | _ \<Rightarrow> None)"

theorem finite_binding_observation_row_correct:
  "finite_binding_observation_row first u r=Some v \<longleftrightarrow>
    binding_observation_row first (decode_finite_term u) (decode_finite_term r) (decode_finite_term v)"
  by (cases first; cases v)
    (auto simp: finite_binding_observation_row_def binding_observation_row_def
      finite_term_formed_correct split: finite_factor_term.splits)

definition finite_binding_observation_view ::
  "bool\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term list\<Rightarrow>finite_factor_term list option" where
  "finite_binding_observation_view first u rs=
    guarded_option_map (finite_term_formed u) (finite_binding_observation_row first u) rs"

theorem finite_binding_observation_view_correct:
  "finite_binding_observation_view first u bs=Some xs \<longleftrightarrow>
    term_formed (decode_finite_term u) \<and>
    list_all2 (binding_observation_row first (decode_finite_term u))
      (map decode_finite_term bs) (map decode_finite_term xs)"
  by (simp only: finite_binding_observation_view_def guarded_option_map_result
    finite_term_formed_correct finite_binding_observation_row_correct list_all2_map1 list_all2_map2)

theorem finite_binding_observation_view_native:
  "finite_binding_observation_view first u bs=Some xs \<longleftrightarrow>
    ((if first then 345 else 346),context_relation_argument (decode_finite_term u)
      (data_list_term (map decode_finite_term bs)) (data_list_term (map decode_finite_term xs)))
      \<in>positive_meaning binding_observation_program"
  by (cases first)
    (simp_all only: if_True if_False finite_binding_observation_view_correct
      binding_observation_first_list.lists binding_observation_second_list.lists
      binding_observation_first.at_arguments binding_observation_second.at_arguments)

definition finite_binding_observation_outputs where
  "finite_binding_observation_outputs u bs=paired_option_outputs
    (finite_binding_observation_view True u) (finite_binding_observation_view False u) bs"

lemma finite_binding_observation_outputs_parts:
  "finite_binding_observation_outputs u bs=Some (xs,ys) \<longleftrightarrow>
    finite_binding_observation_view True u bs=Some xs \<and>
    finite_binding_observation_view False u bs=Some ys"
  by (simp only: finite_binding_observation_outputs_def paired_option_outputs_result)

theorem finite_binding_observation_outputs_native:
  "finite_binding_observation_outputs u bs=Some (xs,ys) \<longleftrightarrow>
    (347,binding_observation_argument (decode_finite_term u) (data_list_term (map decode_finite_term bs))
      (data_list_term (map decode_finite_term xs)) (data_list_term (map decode_finite_term ys)))
      \<in>positive_meaning binding_observation_program"
  by (simp only: finite_binding_observation_outputs_parts binding_observation_pair_arguments
    finite_binding_observation_view_native if_True if_False)

section \<open>Constructed observations supply semantically established premises\<close>

abbreviation finite_binding_sequence where
  "finite_binding_sequence xs \<equiv> finite_data_sequence xs"

lemma decode_finite_binding_sequence [simp]:
  "decode_finite_term (finite_binding_sequence xs)=data_list_term (map decode_finite_term xs)"
  by (rule decode_finite_data_sequence)

definition finite_binding_observation_frontier ::
  "finite_factor_term\<Rightarrow>finite_factor_term list\<Rightarrow>(nat\<times>finite_factor_term) list" where
  "finite_binding_observation_frontier u bs=
    (case finite_binding_observation_view True u bs of None \<Rightarrow> []
      | Some xs \<Rightarrow> [(345,Finite_Pair u (Finite_Pair (finite_binding_sequence bs) (finite_binding_sequence xs)))]) @
    (case finite_binding_observation_view False u bs of None \<Rightarrow> []
      | Some ys \<Rightarrow> [(346,Finite_Pair u (Finite_Pair (finite_binding_sequence bs) (finite_binding_sequence ys)))])"

theorem finite_binding_observation_frontier_sound:
  assumes member: "(d,t)\<in>set (finite_binding_observation_frontier u bs)"
  shows "(d,decode_finite_term t)\<in>positive_meaning binding_observation_program"
proof -
  have first: "(345,decode_finite_term (Finite_Pair u
      (Finite_Pair (finite_binding_sequence bs) (finite_binding_sequence xs))))
      \<in>positive_meaning binding_observation_program"
    if "finite_binding_observation_view True u bs=Some xs" for xs
    using that by (simp only: decode_finite_term.simps decode_finite_binding_sequence
      finite_binding_observation_view_native if_True)
  have second: "(346,decode_finite_term (Finite_Pair u
      (Finite_Pair (finite_binding_sequence bs) (finite_binding_sequence ys))))
      \<in>positive_meaning binding_observation_program"
    if "finite_binding_observation_view False u bs=Some ys" for ys
    using that by (simp only: decode_finite_term.simps decode_finite_binding_sequence
      finite_binding_observation_view_native if_False)
  show ?thesis using member first second
    by (auto simp: finite_binding_observation_frontier_def split: option.splits)
qed

export_code finite_binding_observation_outputs finite_binding_observation_frontier checking SML

text \<open>
  Every returned pair of lists is exactly a true call of the native operation.
  The original input determines both outputs. A different owner, a missing
  paired value, or a malformed component prevents a result. All original rows
  are visited, and the empty case still checks the supplied context.

  The frontier consists only of the native traversal calls established by
  these computations. It can supply known premises to the general inference
  engine without treating arbitrary possible calls as already established.
\<close>

end
