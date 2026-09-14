theory Factor_Finite_Source_Decisions
  imports Factor_Finite_Source_Construction Factor_Finite_Native_Proof_Construction
    Factor_Finite_Term_Demands
begin

definition finite_source_decision where
  "finite_source_decision supported construct E pu pr Xs=(case finite_construct_source supported construct E pu pr of
    None \<Rightarrow> None | Some (d,F,u) \<Rightarrow> (case finite_native_source F u [] of
      None \<Rightarrow> None | Some Q \<Rightarrow> (let D=finite_program_term_demand Q Xs in
        map_option (\<lambda>(P,A,T). (d,F,u,P,D,A,T,ffilter (\<lambda>t. (d,t) |\<in>| A) Xs))
          (finite_native_program_proofs F u [] D))))"

lemma finite_source_decision_conditions:
  "finite_source_decision supported construct E pu pr Xs=Some (d,F,u,Q,D,A,T,Ys) \<longleftrightarrow>
    finite_construct_source supported construct E pu pr=Some (d,F,u) \<and>
    finite_native_source F u []=Some Q \<and> D=finite_program_term_demand Q Xs \<and>
    finite_native_program_proofs F u [] D=Some (Q,A,T) \<and>
    Ys=ffilter (\<lambda>t. (d,t) |\<in>| A) Xs"
proof -
  have source: "finite_native_program_proofs F u [] D=Some (Q,A,T) \<Longrightarrow>
    finite_native_source F u []=Some Q" for D Q A T
    by (simp only: finite_native_program_proofs_conditions finite_native_source_correct; blast)
  show ?thesis using source
    by (auto simp: finite_source_decision_def Let_def split: option.splits prod.splits)
qed

context finite_native_source_constructor
begin

lemma constructed_entry_at_readings:
  assumes constructed: "finite_construct_source supported C E pu pr=Some (d,F,u)"
    and original: "finite_native_source E pu pr=Some P"
    and target: "finite_native_source F u []=Some Q"
  shows "d |\<in>| finite_system_definitions Q"
    "(d,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t"
proof -
  obtain P' e R T where first: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P')"
    and second: "native_package_at (decode_finite_environment F) u [] T"
    and entry: "d\<in>system_definitions T"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> expected P' t"
    using correct[OF constructed] by blast
  have same: "P'=P" using first original
    by (simp only: finite_native_source_correct[symmetric]; simp)
  have actual: "T=decode_finite_system Q"
    by (rule native_package_unique[OF second target[unfolded finite_native_source_correct]])
  show "d |\<in>| finite_system_definitions Q" using entry
    by (simp only: actual finite_system_definitions_correct)
  show "(d,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t"
    using meaning by (simp only: actual same)
qed

theorem finite_source_decision_exact:
  assumes result: "finite_source_decision supported C E pu pr Xs=Some (d,F,u,Q,D,A,T,Ys)"
    and original: "finite_native_source E pu pr=Some P"
  shows "fset Ys={t\<in>fset Xs. expected P (decode_finite_term t)}"
    "fimage fst T=A"
    "finite_proofs_sound Q T"
    "t |\<in>| Ys \<Longrightarrow> \<exists>p. ((d,t),p) |\<in>| T"
proof -
  have constructed: "finite_construct_source supported C E pu pr=Some (d,F,u)"
    and source: "finite_native_source F u []=Some Q"
    and demand: "D=finite_program_term_demand Q Xs"
    and proofs: "finite_native_program_proofs F u [] D=Some (Q,A,T)"
    and answers: "Ys=ffilter (\<lambda>t. (d,t) |\<in>| A) Xs"
    using result by (simp only: finite_source_decision_conditions; blast)+
  have entry: "d |\<in>| finite_system_definitions Q"
    by (rule constructed_entry_at_readings(1)[OF constructed original source])
  have each: "(d,t) |\<in>| A \<longleftrightarrow> expected P (decode_finite_term t)" if "t |\<in>| Xs" for t
  proof -
    have requested: "(d,t) |\<in>| D"
      by (simp only: demand; rule finite_program_term_demand_root[OF entry that])
    show ?thesis by (simp only: finite_native_program_evaluation_call[OF
        finite_native_program_proofs_evaluation[OF proofs] requested]
      constructed_entry_at_readings(2)[OF constructed original source])
  qed
  show "fset Ys={t\<in>fset Xs. expected P (decode_finite_term t)}"
    using each by (auto simp: answers)
  show domain: "fimage fst T=A"
    by (rule finite_native_program_proofs_correct(2)[OF proofs])
  show "finite_proofs_sound Q T"
    by (rule finite_native_program_proofs_correct(3)[OF proofs])
  show "t |\<in>| Ys \<Longrightarrow> \<exists>p. ((d,t),p) |\<in>| T"
  proof -
    assume admitted: "t |\<in>| Ys"
    have head: "(d,t) |\<in>| A" using admitted by (auto simp: answers)
    show "\<exists>p. ((d,t),p) |\<in>| T"
      using head by (simp only: domain[symmetric] finite_first_projection_member)
  qed
qed

end

export_code finite_source_decision checking SML

text \<open>
  One shared operation constructs the required entry from the complete actual
  source, reads the installed native program, derives its finite demand from
  whole input terms, and generates the complete answer and certificate family.
  No supplied truth or certificate enters the calculation. A successful result
  retains the complete installed environment, actual definition, program,
  demand, all answers and proofs, and every qualifying original term.

  Source-constructor contracts establish the independent condition for each
  use. Failed source construction, an unreadable installed package, or an
  unsupported finite evaluation yields no result. A successful empty answer
  remains distinct. This construction supplies no claim that an arbitrary
  requirement family covers the original development problem.
\<close>

end
