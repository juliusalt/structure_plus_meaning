theory Factor_Finite_Accumulated_Data_Syntax
  imports Factor_Finite_Data_Syntax Factor_Finite_Syntax_Accumulation
begin

fun finite_data_syntax_rows ::
  "local_address \<Rightarrow> factor_term \<Rightarrow> finite_syntax_rows \<Rightarrow> finite_syntax_rows option" where
  "finite_data_syntax_rows p (Target_Term t) A=None"
| "finite_data_syntax_rows p (Payload_Term v) A=Some (finite_syntax_rows_payload p v A)"
| "finite_data_syntax_rows p (Pair_Term x y) A=
    (case finite_data_syntax_rows (p@[3]) y A of None \<Rightarrow> None
      | Some B \<Rightarrow> map_option (finite_syntax_rows_pair p) (finite_data_syntax_rows (p@[2]) x B))"

theorem finite_data_syntax_rows_exact:
  "map_option finite_syntax_rows_object (finite_data_syntax_rows p t A)=
    map_option (\<lambda>C. finite_syntax_accumulate p C (finite_syntax_rows_object A)) (finite_data_syntax t)"
proof (induction t arbitrary: p A)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  then show ?case by (simp add: finite_syntax_rows_payload_object)
next
  case (Pair_Term x y)
  show ?case
  proof (cases "finite_data_syntax y")
    case None
    have empty: "finite_data_syntax_rows (p@[3]) y A=None"
      using Pair_Term.IH(2)[of "p@[3]" A] None
      by (cases "finite_data_syntax_rows (p@[3]) y A") auto
    show ?thesis by (simp add: empty None split: option.splits)
  next
    case (Some S)
    obtain B where built_y: "finite_data_syntax_rows (p@[3]) y A=Some B"
      and rows_y: "finite_syntax_rows_object B=
        finite_syntax_accumulate (p@[3]) S (finite_syntax_rows_object A)"
      using Pair_Term.IH(2)[of "p@[3]" A] Some
      by (cases "finite_data_syntax_rows (p@[3]) y A") auto
    show ?thesis
    proof (cases "finite_data_syntax x")
      case None
      have empty: "finite_data_syntax_rows (p@[2]) x B=None"
        using Pair_Term.IH(1)[of "p@[2]" B] None
        by (cases "finite_data_syntax_rows (p@[2]) x B") auto
      show ?thesis by (simp add: built_y empty None)
    next
      case (Some R)
      obtain D where built_x: "finite_data_syntax_rows (p@[2]) x B=Some D"
        and rows_x: "finite_syntax_rows_object D=
          finite_syntax_accumulate (p@[2]) R (finite_syntax_rows_object B)"
        using Pair_Term.IH(1)[of "p@[2]" B] Some
        by (cases "finite_data_syntax_rows (p@[2]) x B") auto
      show ?thesis
        by (simp only: finite_data_syntax_rows.simps finite_data_syntax.simps
            built_y built_x \<open>finite_data_syntax y=Some S\<close> Some option.case option.map
            finite_syntax_rows_pair_object rows_x rows_y finite_syntax_accumulate_pair)
    qed
  qed
qed

lemma finite_data_syntax_empty_bag:
  "finite_data_syntax t=Some C \<Longrightarrow> finite_bag (finite_data C)={#}"
  by (induction t arbitrary: C)
    (auto simp: finite_payload_syntax_def finite_payload_basis_def
      finite_pair_syntax_def finite_syntax_join_def split: option.splits)

declare finite_data_syntax.simps[code del]

theorem finite_data_syntax_accumulated_code [code]:
  "finite_data_syntax t=map_option finite_syntax_rows_object (finite_data_syntax_rows [] t ([],[],[]))"
proof (cases "finite_data_syntax t")
  case None
  then show ?thesis using finite_data_syntax_rows_exact[of "[]" t "([],[],[])"] by simp
next
  case (Some C)
  have bag: "finite_bag (finite_data C)={#}" by (rule finite_data_syntax_empty_bag[OF Some])
  show ?thesis using finite_data_syntax_rows_exact[of "[]" t "([],[],[])"]
    by (simp only: Some option.map finite_syntax_accumulate_empty[OF bag])
qed

text \<open>The executable refinement constructs each complete carrier, incidence
  and binding row at its final address and accumulates the rows once. It retains
  the original optional result for every term, including target rejection and
  malformed payload values. The existing exact syntax and quotation theorems
  therefore apply to the returned artifact without another semantic premise.\<close>

end
