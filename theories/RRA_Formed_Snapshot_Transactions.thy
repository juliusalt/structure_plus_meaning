theory RRA_Formed_Snapshot_Transactions
  imports RRA_Finite_Transactions
begin

section \<open>A formed snapshot stays formed through its transactions\<close>

text \<open>
  A transaction checks that the snapshot it is executed on is formed: formed generations, at most one
  at each locus. The snapshot a successful transaction returns is formed again, so a transaction
  executed on it needs to check only itself, whose formation is local to the generations it compares
  and writes. Checking the whole snapshot at every step made each publication pay for every
  generation published before it.
\<close>

definition finite_transact_formed :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> finite_transaction_result option" where
  "finite_transact_formed S T=(if finite_transaction_formed T then
    Some (if finite_comparison_passes S T then Finite_Applied (finite_transaction_update S T)
      else Finite_Conflict (finite_observed_comparison S T)) else None)"

lemma finite_transact_formed_exact:
  assumes "finite_snapshot_formed S"
  shows "finite_transact S T=finite_transact_formed S T"
  using assms by (simp add: finite_transact_def finite_transact_formed_def)

lemma finite_transact_applied_formed:
  assumes applied: "finite_transact S T=Some (Finite_Applied U)"
  shows "finite_snapshot_formed U"
proof -
  have "transact (decode_finite_snapshot S) (decode_finite_transaction T)
      (decode_finite_transaction_result (Finite_Applied U))"
    using applied by (auto simp: finite_transact_exact)
  then have "snapshot_formed (decode_finite_snapshot U)"
    by (simp add: successful_transaction_formed)
  then show ?thesis by (simp only: finite_snapshot_formed_correct)
qed

lemma finite_transact_after_applied:
  assumes "finite_transact S T=Some (Finite_Applied U)"
  shows "finite_transact U T'=finite_transact_formed U T'"
  by (rule finite_transact_formed_exact[OF finite_transact_applied_formed[OF assms]])

section \<open>Publishing several generations in turn\<close>

text \<open>
  Generations are published one after another, each by the transaction that expects what its
  publisher read at its locus, and each against the snapshot the previous transaction left: a
  successful transaction continues from its successor, and a conflict or a refusal leaves the
  snapshot as it was. A generation that is absent publishes nothing. The snapshot's formation is
  checked once, where the sequence starts; a snapshot that is not formed refuses every transaction.
\<close>

fun finite_locus_publications ::
    "finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow>
      finite_transaction_result option list" where
  "finite_locus_publications S []=[]"
| "finite_locus_publications S ((I,A)#ps)=(case A of
     None \<Rightarrow> None#finite_locus_publications S ps
   | Some G \<Rightarrow> (let result=finite_transact S (finite_locus_transaction I G) in
       result#(case result of Some (Finite_Applied U) \<Rightarrow> finite_locus_publications U ps
         | _ \<Rightarrow> finite_locus_publications S ps)))"

fun finite_locus_publications_formed ::
    "finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow>
      finite_transaction_result option list" where
  "finite_locus_publications_formed S []=[]"
| "finite_locus_publications_formed S ((I,A)#ps)=(case A of
     None \<Rightarrow> None#finite_locus_publications_formed S ps
   | Some G \<Rightarrow> (let result=finite_transact_formed S (finite_locus_transaction I G) in
       result#(case result of Some (Finite_Applied U) \<Rightarrow> finite_locus_publications_formed U ps
         | _ \<Rightarrow> finite_locus_publications_formed S ps)))"

lemma finite_locus_publications_formed_exact:
  assumes "finite_snapshot_formed S"
  shows "finite_locus_publications S ps=finite_locus_publications_formed S ps"
  using assms
proof (induction ps arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons q ps)
  obtain I A where q: "q=(I,A)" by (cases q) auto
  show ?case
  proof (cases A)
    case None
    then show ?thesis using Cons.IH[OF Cons.prems] by (simp add: q)
  next
    case (Some G)
    have same: "finite_transact_formed S (finite_locus_transaction I G)=finite_transact S (finite_locus_transaction I G)"
      by (rule finite_transact_formed_exact[OF Cons.prems, symmetric])
    show ?thesis
    proof (cases "finite_transact S (finite_locus_transaction I G)")
      case None
      then show ?thesis using Cons.IH[OF Cons.prems] same by (simp add: q \<open>A=Some G\<close>)
    next
      case (Some result)
      note found=this
      have formed_found: "finite_transact_formed S (finite_locus_transaction I G)=Some result"
        using same found by simp
      show ?thesis
      proof (cases result)
        case (Finite_Applied U)
        have formed: "finite_snapshot_formed U"
          by (rule finite_transact_applied_formed[OF found[unfolded Finite_Applied]])
        show ?thesis using Cons.IH[OF formed] found formed_found
          by (simp add: q \<open>A=Some G\<close> Finite_Applied)
      next
        case (Finite_Conflict C)
        show ?thesis using Cons.IH[OF Cons.prems] found formed_found
          by (simp add: q \<open>A=Some G\<close> Finite_Conflict)
      qed
    qed
  qed
qed

lemma finite_locus_publications_unformed:
  assumes "\<not>finite_snapshot_formed S"
  shows "finite_locus_publications S ps=map (\<lambda>q. None) ps"
  using assms
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons q ps)
  obtain I A where q: "q=(I,A)" by (cases q) auto
  have refused: "finite_transact S T=None" for T using Cons.prems by (simp add: finite_transact_def)
  show ?case using Cons.IH[OF Cons.prems] refused by (cases A) (simp_all add: q)
qed

declare finite_locus_publications.simps [code del]

text \<open>
  The equation is stated for the snapshot alone, so a publisher made once for a snapshot checks its
  formation once, however many lists it then publishes.
\<close>

lemma finite_locus_publications_code [code]:
  "finite_locus_publications S=(if finite_snapshot_formed S then finite_locus_publications_formed S
    else map (\<lambda>q. None))"
proof (rule ext)
  fix ps
  show "finite_locus_publications S ps=(if finite_snapshot_formed S then finite_locus_publications_formed S
    else map (\<lambda>q. None)) ps"
    by (cases "finite_snapshot_formed S")
      (simp_all add: finite_locus_publications_formed_exact finite_locus_publications_unformed)
qed

end
