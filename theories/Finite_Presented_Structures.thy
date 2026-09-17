theory Finite_Presented_Structures
  imports Finite_Presented_Coordinates
    Factor_Admission_Plans
    RRA_Finite_Generations
    Factor_Derivation
begin

section \<open>Admission goals reuse their presentation over any site encoding\<close>

fun finite_goal_value :: "('d \<Rightarrow> finite_factor_term) \<Rightarrow> 'd admission_goal \<Rightarrow> finite_factor_term" where
  "finite_goal_value f (Existing_Admission d)=Finite_Pair (Finite_Payload [0]) (f d)"
| "finite_goal_value f (Paired_Admission g h)=
    Finite_Pair (Finite_Payload [1]) (Finite_Pair (finite_goal_value f g) (finite_goal_value f h))"
| "finite_goal_value f (Collected_Admission g)=Finite_Pair (Finite_Payload [2]) (finite_goal_value f g)"

lemma decode_finite_goal_value [simp]:
  "decode_finite_term (finite_goal_value f g)=admission_goal_value_with (decode_finite_term \<circ> f) g"
  by (induction g) simp_all

lemma finite_goal_value_injective [intro]:
  assumes "inj f"
  shows "inj (finite_goal_value f)"
proof (rule injI)
  fix g h assume "finite_goal_value f g=finite_goal_value f h"
  then have same: "admission_goal_value_with (decode_finite_term \<circ> f) g=admission_goal_value_with (decode_finite_term \<circ> f) h"
    by (metis decode_finite_goal_value)
  have "inj (decode_finite_term \<circ> f)" using assms by (auto simp: inj_def)
  then show "g=h" using same by (simp add: admission_goal_value_with_injective)
qed

section \<open>Generations and proofs present their complete predecessor collections\<close>

primrec finite_generation_value ::
  "('t \<Rightarrow> finite_factor_term) \<Rightarrow> 't generation_structure \<Rightarrow> finite_factor_term" where
  "finite_generation_value f (Generation l P p c)=Finite_Pair (f l)
    (Finite_Pair (finite_collection_presentation id (fimage (finite_generation_value f) P))
      (Finite_Pair (f p) (f c)))"

lemma finite_generation_value_injective [intro]:
  assumes f: "inj f"
  shows "inj (finite_generation_value f)"
proof (rule injI)
  fix G H show "finite_generation_value f G=finite_generation_value f H \<Longrightarrow> G=H"
  proof (induction G arbitrary: H)
    case (Generation l P p c)
    obtain l' P' p' c' where H: "H=Generation l' P' p' c'" by (cases H)
    have members: "\<And>x y. x |\<in>| P \<Longrightarrow> finite_generation_value f x=finite_generation_value f y \<longleftrightarrow> x=y"
      using Generation.IH by blast
    have collections: "inj (finite_collection_presentation (id::finite_factor_term \<Rightarrow> _))"
      by (intro finite_collection_presentation_injective inj_on_id)
    have "fimage (finite_generation_value f) P=fimage (finite_generation_value f) P'"
      and parts: "l=l'" "p=p'" "c=c'"
      using Generation.prems by (simp_all add: H inj_eq[OF collections] inj_eq[OF f])
    then have "P=P'" by (simp only: fimage_injective_on_left[OF members])
    then show ?case using parts by (simp add: H)
  qed
qed

primrec finite_proof_value ::
  "('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('a\<times>'v \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('a,'s,'c,'v) inference_proof \<Rightarrow> finite_factor_term" where
  "finite_proof_value fc fb fs (Schema_Proof c V B)=Finite_Pair (fc c)
    (Finite_Pair (finite_collection_presentation fb V)
      (finite_collection_presentation (finite_pair_presentation fs id)
        (fimage (map_prod id (finite_proof_value fc fb fs)) B)))"

lemma finite_proof_value_injective [intro]:
  assumes c: "inj fc" and b: "inj fb" and s: "inj fs"
  shows "inj (finite_proof_value fc fb fs)"
proof (rule injI)
  fix p q show "finite_proof_value fc fb fs p=finite_proof_value fc fb fs q \<Longrightarrow> p=q"
  proof (induction p arbitrary: q)
    case (Schema_Proof k V B)
    obtain k' V' B' where q: "q=Schema_Proof k' V' B'" by (cases q)
    let ?r="map_prod id (finite_proof_value fc fb fs)"
    have members: "\<And>x y. x |\<in>| B \<Longrightarrow> ?r x=?r y \<longleftrightarrow> x=y"
    proof -
      fix x y assume x: "x |\<in>| B"
      show "?r x=?r y \<longleftrightarrow> x=y"
      proof (cases x, cases y)
        fix s t s' t' assume xs: "x=(s,t)" and ys: "y=(s',t')"
        have "finite_proof_value fc fb fs t=finite_proof_value fc fb fs t' \<Longrightarrow> t=t'"
          by (rule Schema_Proof.IH[OF x]) (simp_all add: xs)
        then show ?thesis by (auto simp: xs ys)
      qed
    qed
    have bindings: "inj (finite_collection_presentation fb)"
      using b by (rule finite_collection_presentation_injective)
    have slots: "inj (finite_collection_presentation (finite_pair_presentation fs (id::finite_factor_term \<Rightarrow> _)))"
      using s by (intro finite_collection_presentation_injective finite_pair_presentation_injective inj_on_id)
    have "fimage ?r B=fimage ?r B'" and parts: "k=k'" "V=V'"
      using Schema_Proof.prems
      by (simp_all add: q inj_eq[OF c] inj_eq[OF bindings] inj_eq[OF slots])
    then have "B=B'" by (simp only: fimage_injective_on_left[OF members])
    then show ?case using parts by (simp add: q)
  qed
qed

text \<open>
  An admission goal is presented by the existing admission_goal_value_with
  construction over the decoded site presentation. A generation keeps its locus,
  payload and cause and the complete collection of its predecessors' presentations;
  a proof keeps its clause, its binding collection and the collection of premise
  sites with their subproof presentations. Injectivity of every recursive
  presentation follows from injectivity of its components.
\<close>

end
