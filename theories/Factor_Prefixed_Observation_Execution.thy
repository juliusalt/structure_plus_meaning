theory Factor_Prefixed_Observation_Execution
  imports Factor_Prefixed_Observation_Contracts Factor_Executable_Data_Values Option_List_Maps
begin

section \<open>The finite row operation keeps the prefix around either selected value\<close>

definition finite_prefixed_observation_row ::
  "bool\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term option" where
  "finite_prefixed_observation_row first u r=(case r of Finite_Pair k v \<Rightarrow>
    (case k of Finite_Pair owner a \<Rightarrow>
      (case v of Finite_Pair d xy \<Rightarrow>
        (case xy of Finite_Pair x y \<Rightarrow>
          (if owner=u \<and> finite_term_formed u \<and> finite_term_formed a \<and>
              finite_term_formed d \<and> finite_term_formed x \<and> finite_term_formed y
           then Some (Finite_Pair a (Finite_Pair d (if first then x else y))) else None)
         | _ \<Rightarrow> None)
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
   | _ \<Rightarrow> None)"

theorem finite_prefixed_observation_row_correct:
  "finite_prefixed_observation_row first u r=Some v \<longleftrightarrow>
    prefixed_observation_row first (decode_finite_term u) (decode_finite_term r) (decode_finite_term v)"
  apply (cases first; cases v)
  apply (auto simp: finite_prefixed_observation_row_def prefixed_observation_row_def
    finite_term_formed_correct split: finite_factor_term.splits)
  apply (metis decode_finite_term.simps(3) decode_finite_term_injective)+
  done

definition finite_prefixed_observation_view ::
  "bool\<Rightarrow>finite_factor_term\<Rightarrow>finite_factor_term list\<Rightarrow>finite_factor_term list option" where
  "finite_prefixed_observation_view first u rs=
    guarded_option_map (finite_term_formed u) (finite_prefixed_observation_row first u) rs"

theorem finite_prefixed_observation_view_correct:
  "finite_prefixed_observation_view first u rs=Some xs \<longleftrightarrow>
    term_formed (decode_finite_term u) \<and>
    list_all2 (prefixed_observation_row first (decode_finite_term u))
      (map decode_finite_term rs) (map decode_finite_term xs)"
  by (simp only: finite_prefixed_observation_view_def guarded_option_map_result
    finite_term_formed_correct finite_prefixed_observation_row_correct list_all2_map1 list_all2_map2)

theorem finite_prefixed_observation_view_native:
  "finite_prefixed_observation_view first u rs=Some xs \<longleftrightarrow>
    ((if first then 356 else 357),context_relation_argument (decode_finite_term u)
      (data_list_term (map decode_finite_term rs)) (data_list_term (map decode_finite_term xs)))
      \<in>positive_meaning prefixed_observation_program"
  by (cases first)
    (simp_all only: if_True if_False finite_prefixed_observation_view_correct
      prefixed_observation_first_list.lists prefixed_observation_second_list.lists
      prefixed_observation_first.at_arguments prefixed_observation_second.at_arguments)

definition finite_prefixed_observation_outputs where
  "finite_prefixed_observation_outputs u rs=paired_option_outputs
    (finite_prefixed_observation_view True u) (finite_prefixed_observation_view False u) rs"

lemma finite_prefixed_observation_outputs_parts:
  "finite_prefixed_observation_outputs u rs=Some (xs,ys) \<longleftrightarrow>
    finite_prefixed_observation_view True u rs=Some xs \<and>
    finite_prefixed_observation_view False u rs=Some ys"
  by (simp only: finite_prefixed_observation_outputs_def paired_option_outputs_result)

theorem finite_prefixed_observation_outputs_native:
  "finite_prefixed_observation_outputs u rs=Some (xs,ys) \<longleftrightarrow>
    (358,paired_context_results_argument (decode_finite_term u) (data_list_term (map decode_finite_term rs))
      (data_list_term (map decode_finite_term xs)) (data_list_term (map decode_finite_term ys)))
      \<in>positive_meaning prefixed_observation_program"
  by (simp only: finite_prefixed_observation_outputs_parts prefixed_observation_pair.at_arguments
    finite_prefixed_observation_view_native if_True if_False)

export_code finite_prefixed_observation_outputs checking SML

text \<open>
  The output equation concerns the complete decoded input and both complete
  returned lists. It may supply a native paired-view fact after the actual
  computation succeeds. The generic guarded sequence map and paired partial
  result operation are shared with the existing binding-observation reader.
\<close>

end
