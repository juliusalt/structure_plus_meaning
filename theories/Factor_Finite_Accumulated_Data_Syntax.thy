theory Factor_Finite_Accumulated_Data_Syntax
  imports Factor_Finite_Data_Syntax Factor_Finite_Syntax_Accumulation
begin

section \<open>The rows of the complete data quotation are accumulated once\<close>

fun finite_data_syntax_rows :: "nat \<Rightarrow> factor_term \<Rightarrow> finite_syntax_rows \<Rightarrow> (nat\<times>finite_syntax_rows) option" where
  "finite_data_syntax_rows n (Target_Term t) A=None"
| "finite_data_syntax_rows n (Payload_Term v) A=
    Some (Suc n,finite_syntax_rows_payload (compact_syntax_address n) v A)"
| "finite_data_syntax_rows n (Pair_Term x y) A=(case finite_data_syntax_rows (n+3) x A of None \<Rightarrow> None
    | Some (m,B) \<Rightarrow> (case finite_data_syntax_rows m y B of None \<Rightarrow> None
      | Some (k,D) \<Rightarrow> Some (k,finite_syntax_rows_pair (compact_syntax_address n) (compact_syntax_address (Suc n))
          (compact_syntax_address (Suc (Suc n))) (compact_syntax_address (n+3)) (compact_syntax_address m) D)))"

lemma finite_data_syntax_payload_rows:
  "finite_syntax_rows_object (finite_syntax_rows_payload (compact_syntax_address n) v X)=
    finite_syntax_accumulate [] (finite_compact_payload n v) (finite_syntax_rows_object X)"
  by (cases X) (simp add: finite_syntax_rows_object_def finite_syntax_rows_payload_def
      finite_syntax_accumulate_def finite_syntax_join_def finite_compact_payload_def finite_payload_basis_def
      finite_enumerated_artifact_def id_def)

lemma finite_data_syntax_pair_rows:
  assumes "finite_syntax_rows_object D=finite_syntax_accumulate [] S (finite_syntax_accumulate [] R X)"
  shows "finite_syntax_rows_object (finite_syntax_rows_pair (compact_syntax_address n)
      (compact_syntax_address (Suc n)) (compact_syntax_address (Suc (Suc n))) (compact_syntax_address (n+3))
      (compact_syntax_address m) D)=
    finite_syntax_accumulate [] (finite_compact_pair n m R S) X"
proof -
  obtain U I B where D: "D=(U,I,B)" by (cases D)
  show ?thesis
    using assms
    by (simp add: D finite_syntax_rows_pair_def finite_syntax_rows_object_def finite_enumerated_artifact_def
        finite_syntax_accumulate_def finite_syntax_join_def finite_compact_pair_def
        fimage_funion fimage_fimage id_def case_prod_unfold
        funion_commute funion_left_commute funion_assoc)
qed

theorem finite_data_syntax_rows_exact:
  "map_option (\<lambda>(k,X). (k,finite_syntax_rows_object X)) (finite_data_syntax_rows n t A)=
    map_option (\<lambda>(k,C). (k,finite_syntax_accumulate [] C (finite_syntax_rows_object A))) (finite_data_syntax_at n t)"
proof (induction t arbitrary: n A)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  show ?case by (simp add: finite_data_syntax_payload_rows)
next
  case (Pair_Term x y)
  show ?case
  proof (cases "finite_data_syntax_at (n+3) x")
    case None
    have rows: "finite_data_syntax_rows (n+3) x A=None" using Pair_Term.IH(1)[of "n+3" A] None by simp
    show ?thesis by (simp add: rows None)
  next
    case (Some p)
    obtain m R where p: "p=(m,R)" by (cases p)
    obtain B where rows_left: "finite_data_syntax_rows (n+3) x A=Some (m,B)"
      and object_left: "finite_syntax_rows_object B=finite_syntax_accumulate [] R (finite_syntax_rows_object A)"
      using Pair_Term.IH(1)[of "n+3" A] Some p by (auto split: option.splits)
    show ?thesis
    proof (cases "finite_data_syntax_at m y")
      case None
      have rows: "finite_data_syntax_rows m y B=None" using Pair_Term.IH(2)[of m B] None by simp
      show ?thesis by (simp add: rows_left rows Some p None)
    next
      case (Some q)
      obtain l S where q: "q=(l,S)" by (cases q)
      obtain D where rows_right: "finite_data_syntax_rows m y B=Some (l,D)"
        and object_right: "finite_syntax_rows_object D=finite_syntax_accumulate [] S (finite_syntax_rows_object B)"
        using Pair_Term.IH(2)[of m B] Some q by (auto split: option.splits)
      have joined: "finite_syntax_rows_object (finite_syntax_rows_pair (compact_syntax_address n)
          (compact_syntax_address (Suc n)) (compact_syntax_address (Suc (Suc n))) (compact_syntax_address (n+3))
          (compact_syntax_address m) D)=
          finite_syntax_accumulate [] (finite_compact_pair n m R S) (finite_syntax_rows_object A)"
        by (rule finite_data_syntax_pair_rows) (simp only: object_right object_left)
      show ?thesis
        using \<open>finite_data_syntax_at (n+3) x=Some p\<close> Some
        by (simp add: rows_left rows_right p q joined)
    qed
  qed
qed

lemma finite_data_syntax_at_empty_bag:
  "finite_data_syntax_at n t=Some (k,C) \<Longrightarrow> finite_bag (finite_data C)={#}"
  by (induction t arbitrary: n k C)
    (auto simp: finite_compact_payload_def finite_payload_basis_def finite_compact_pair_def finite_syntax_join_def
      split: option.splits)

declare finite_data_syntax_def[code del]

theorem finite_data_syntax_accumulated:
  "finite_data_syntax t=
    map_option (\<lambda>(k,X). finite_syntax_rows_object X) (finite_data_syntax_rows 0 t ([],[],[]))"
proof (cases "finite_data_syntax_at 0 t")
  case None
  then show ?thesis using finite_data_syntax_rows_exact[of 0 t "([],[],[])"]
    by (simp add: finite_data_syntax_def split: option.splits)
next
  case (Some p)
  obtain k C where p: "p=(k,C)" by (cases p)
  have bag: "finite_bag (finite_data C)={#}" using finite_data_syntax_at_empty_bag Some p by simp
  show ?thesis using finite_data_syntax_rows_exact[of 0 t "([],[],[])"] Some p
    finite_syntax_accumulate_empty[OF bag]
    by (auto simp: finite_data_syntax_def split: option.splits)
qed

theorem finite_data_syntax_accumulated_code [code]:
  "finite_data_syntax t=map_option (\<lambda>(k,X). finite_syntax_rows_object (case X of (U,I,B) \<Rightarrow>
      (sorted_list_of_set (set U),sorted_list_of_set (set I),sorted_list_of_set (set B))))
    (finite_data_syntax_rows 0 t ([],[],[]))"
  by (simp only: finite_data_syntax_accumulated finite_syntax_rows_object_listed)

text \<open>The executable refinement constructs each carrier, incidence and binding row
  at its final compact address, threading the node counter, accumulates the rows once and lists
  each row family once in its canonical order. It retains the original optional result for every
  term, including target rejection and malformed payload values, so the exact syntax and quotation
  theorems apply to the returned artifact without another semantic premise.\<close>

end
