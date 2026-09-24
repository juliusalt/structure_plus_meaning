theory RRA_Formed_Snapshot_Transactions
  imports RRA_Finite_Transactions Established_Premises
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

text \<open>
  The snapshot's formation is the first notion of @{text Established_Premises} checked at the entry:
  the premise is the snapshot's formation, its body the publications over a formed snapshot and its
  refusal the publications' own value outside it.
\<close>

lemma finite_locus_publications_checked:
  "checked_premise finite_locus_publications finite_snapshot_formed finite_locus_publications_formed
    (\<lambda>S. map (\<lambda>q. None))"
  by unfold_locales
    (simp_all add: fun_eq_iff finite_locus_publications_formed_exact finite_locus_publications_unformed)

lemma finite_locus_publications_code [code]:
  "finite_locus_publications S=(if finite_snapshot_formed S then finite_locus_publications_formed S
    else map (\<lambda>q. None))"
  by (rule checked_premise.checked_at_entry[OF finite_locus_publications_checked])

section \<open>A transaction over formed generations checks only itself\<close>

text \<open>
  A transaction's formation is the formation of the generations it compares and writes, and the
  conditions on its loci and absent targets. Where every generation it compares and writes is formed
  already, as where each was made by a constructor whose contract states it formed, the transaction
  checks only the rest: the first notion of @{text Established_Premises} at its third place, the
  premise established by the constructor and nothing checked at the entry. The premise is on the
  transaction, the argument after the snapshot, so its instance is stated for the transaction on
  every snapshot; the publications' premise holds of every pair of the list they publish.
\<close>

definition finite_transaction_generations :: "finite_transaction \<Rightarrow> finite_generation fset" where
  "finite_transaction_generations T=finite_expected_selected T |\<union>| finite_proposed_selected T"

definition finite_transaction_body_formed :: "finite_transaction \<Rightarrow> bool" where
  "finite_transaction_body_formed T \<longleftrightarrow>
    fcard (finite_snapshot_loci (finite_expected_selected T))=fcard (finite_expected_selected T) \<and>
    fcard (finite_snapshot_loci (finite_proposed_selected T))=fcard (finite_proposed_selected T) \<and>
    fBall (finite_expected_absent T) finite_target_formed \<and> fBall (finite_proposed_absent T) finite_target_formed \<and>
    fBall (finite_snapshot_loci (finite_expected_selected T)) (\<lambda>l. l |\<notin>| finite_expected_absent T) \<and>
    fBall (finite_snapshot_loci (finite_proposed_selected T)) (\<lambda>l. l |\<notin>| finite_proposed_absent T) \<and>
    fBall (finite_changed_loci T) (\<lambda>l. l |\<in>| finite_comparison_loci T)"

lemma finite_transaction_formed_generations:
  "finite_transaction_formed T \<longleftrightarrow>
    fBall (finite_transaction_generations T) finite_generation_formed \<and> finite_transaction_body_formed T"
  by (auto simp: finite_transaction_formed_def finite_transaction_body_formed_def
    finite_transaction_generations_def finite_snapshot_formed_def fBall_funion)

lemma finite_locus_transaction_generations:
  "fBall (finite_transaction_generations (finite_locus_transaction I G)) finite_generation_formed \<longleftrightarrow>
    pred_option finite_generation_formed I \<and> finite_generation_formed G"
  by (cases I) (simp_all add: finite_locus_transaction_def finite_admission_transaction_def
    finite_replacement_transaction_def finite_transaction_generations_def conj_commute)

definition finite_transact_body :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> finite_transaction_result option" where
  "finite_transact_body S T=(if finite_transaction_body_formed T then
    Some (if finite_comparison_passes S T then Finite_Applied (finite_transaction_update S T)
      else Finite_Conflict (finite_observed_comparison S T)) else None)"

lemma finite_transact_body_established:
  "established_premise (finite_transact_formed S)
    (\<lambda>T. fBall (finite_transaction_generations T) finite_generation_formed) (finite_transact_body S)"
  by unfold_locales
    (simp add: finite_transact_formed_def finite_transact_body_def finite_transaction_formed_generations)

definition finite_publications_formed_generations ::
    "(finite_generation option\<times>finite_generation option) list \<Rightarrow> bool" where
  "finite_publications_formed_generations ps \<longleftrightarrow>
    (\<forall>(I,A)\<in>set ps. pred_option finite_generation_formed I \<and> pred_option finite_generation_formed A)"

fun finite_locus_publications_body ::
    "finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow>
      finite_transaction_result option list" where
  "finite_locus_publications_body S []=[]"
| "finite_locus_publications_body S ((I,A)#ps)=(case A of
     None \<Rightarrow> None#finite_locus_publications_body S ps
   | Some G \<Rightarrow> (let result=finite_transact_body S (finite_locus_transaction I G) in
       result#(case result of Some (Finite_Applied U) \<Rightarrow> finite_locus_publications_body U ps
         | _ \<Rightarrow> finite_locus_publications_body S ps)))"

lemma finite_locus_publications_body_established:
  "established_premise (finite_locus_publications_formed S) finite_publications_formed_generations
    (finite_locus_publications_body S)"
proof unfold_locales
  fix ps
  assume "finite_publications_formed_generations ps"
  then show "finite_locus_publications_formed S ps=finite_locus_publications_body S ps"
  proof (induction ps arbitrary: S)
    case Nil
    then show ?case by simp
  next
    case (Cons q ps)
    obtain I A where q: "q=(I,A)" by (cases q) auto
    have rest: "finite_publications_formed_generations ps"
      and here: "pred_option finite_generation_formed I" "pred_option finite_generation_formed A"
      using Cons.prems by (simp_all add: finite_publications_formed_generations_def q)
    show ?case
    proof (cases A)
      case None
      then show ?thesis using Cons.IH[OF rest] by (simp add: q)
    next
      case (Some G)
      have premise: "fBall (finite_transaction_generations (finite_locus_transaction I G)) finite_generation_formed"
        using here Some by (simp add: finite_locus_transaction_generations)
      have same: "finite_transact_formed S (finite_locus_transaction I G)=
          finite_transact_body S (finite_locus_transaction I G)"
        by (rule established_premise.exact[OF finite_transact_body_established premise])
      show ?thesis using Cons.IH[OF rest] same
        by (simp add: q Some Let_def split: option.split finite_transaction_result.split)
    qed
  qed
qed

section \<open>A snapshot of formed generations checks only its loci\<close>

text \<open>
  A snapshot's formation is the formation of its generations and the distinctness of their loci. Where
  every generation of the snapshot is formed already, as where each was made by a constructor whose
  contract states it formed, the snapshot checks only its loci: the first notion of
  @{text Established_Premises} at its third place, the premise established by the constructor.
\<close>

definition finite_snapshot_loci_formed :: "finite_snapshot \<Rightarrow> bool" where
  "finite_snapshot_loci_formed S \<longleftrightarrow> fcard (finite_snapshot_loci S)=fcard S"

lemma finite_snapshot_loci_established:
  "established_premise finite_snapshot_formed (\<lambda>S. fBall S finite_generation_formed) finite_snapshot_loci_formed"
  by unfold_locales (simp add: finite_snapshot_formed_def finite_snapshot_loci_formed_def)

end
