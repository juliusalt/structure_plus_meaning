theory RRA_Finite_Generations
  imports RRA_Generation RRA_Finite_Environments Finite_Set_Encoding
begin

type_synonym finite_generation = "finite_exact_target generation_structure"

definition decode_finite_generation :: "finite_generation\<Rightarrow>generation_core" where
  "decode_finite_generation=map_generation_structure decode_finite_target"

definition finite_generation_of :: "generation_core\<Rightarrow>finite_generation" where
  "finite_generation_of=map_generation_structure finite_target_of"

lemma decode_finite_generation_node:
  "decode_finite_generation (Generation l P p c)=Generation (decode_finite_target l)
    (fimage decode_finite_generation P) (decode_finite_target p) (decode_finite_target c)"
  by (simp add: decode_finite_generation_def)

lemma finite_generation_of_node:
  "finite_generation_of (Generation l P p c)=Generation (finite_target_of l)
    (fimage finite_generation_of P) (finite_target_of p) (finite_target_of c)"
  by (simp add: finite_generation_of_def)

lemma finite_generation_of_decode [simp]:
  "finite_generation_of (decode_finite_generation G)=G"
  by (simp add: finite_generation_of_def decode_finite_generation_def
    generation_structure.map_comp comp_def generation_structure.map_ident)

lemma decode_finite_generation_injective [simp]:
  "decode_finite_generation G=decode_finite_generation H \<longleftrightarrow> G=H"
  using finite_generation_of_decode[of G] finite_generation_of_decode[of H] by metis

primrec finite_generation_formed :: "finite_generation\<Rightarrow>bool" where
  "finite_generation_formed (Generation l P p c)=(finite_target_formed l \<and>
    finite_target_formed p \<and> finite_target_formed c \<and>
    fBall (fimage finite_generation_formed P) id)"

lemma finite_generation_formed_node:
  "finite_generation_formed (Generation l P p c)=(finite_target_formed l \<and>
    finite_target_formed p \<and> finite_target_formed c \<and> (\<forall>G\<in>fset P. finite_generation_formed G))"
  by auto

theorem finite_generation_formed_correct:
  "finite_generation_formed G \<longleftrightarrow> generation_formed (decode_finite_generation G)"
proof (induction G rule: generation_structure.induct)
  case (Generation l P p c)
  have original: "generation_formed (Generation l' P' p' c') \<longleftrightarrow>
    target_formed l' \<and> target_formed p' \<and> target_formed c' \<and>
    (\<forall>H\<in>fset P'. generation_formed H)" for l' P' p' c'
    by (auto intro: generation_formed.formed dest: generation_formed_fields)
  show ?case using Generation.IH
    by (auto simp: finite_generation_formed_node decode_finite_generation_node original
      finite_target_formed_correct)
qed

theorem decode_finite_generation_of:
  assumes "generation_formed G"
  shows "decode_finite_generation (finite_generation_of G)=G"
  using assms
proof (induction G rule: generation_structure.induct)
  case (Generation l P p c)
  have fields: "target_formed l" "target_formed p" "target_formed c"
    "\<forall>H\<in>fset P. generation_formed H"
    using generation_formed_fields[OF Generation.prems] by simp_all
  have children: "fimage (\<lambda>H. decode_finite_generation (finite_generation_of H)) P=P"
    using Generation.IH fields(4) by (auto simp: fset_inject[symmetric] fimage.rep_eq)
  show ?case by (simp only: finite_generation_of_node
      decode_finite_generation_node fimage_fimage comp_def children
      decode_finite_target_of[OF fields(1)] decode_finite_target_of[OF fields(2)]
      decode_finite_target_of[OF fields(3)])
qed

theorem finite_generation_representation:
  assumes "generation_formed G"
  shows "\<exists>!F. finite_generation_formed F \<and> decode_finite_generation F=G"
  by (rule ex1I[of _ "finite_generation_of G"])
    (use decode_finite_generation_of[OF assms] assms in
      \<open>auto simp: finite_generation_formed_correct\<close>)

export_code finite_generation_formed checking SML

text \<open>
  Every complete finite target is retained recursively, including each exact
  predecessor value. Decoding is injective and covers every formed original
  generation. Formation does not establish an actual generation reading,
  validate the cause target or supply a historical permission.
\<close>

end
