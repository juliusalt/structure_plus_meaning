theory Factor_Pattern_Determination
  imports Factor_Rule_Instances Factor_Pattern_Programs
begin

section \<open>Two substitutions determine the complete pattern\<close>

lemma graph_pattern_instance:
  "pattern_instance ((\<lambda>a. (a,h a)) ` B) p t \<longleftrightarrow>
    pattern_formed p \<and> pattern_variables p\<subseteq>B \<and> t=evaluate_pattern h p"
  by (induction p arbitrary: t) auto

lemma graph_term_bindings_formed:
  assumes "finite B" "\<forall>a\<in>B. term_formed (h a)"
  shows "term_bindings_formed B ((\<lambda>a. (a,h a)) ` B)"
  using assms by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def)

theorem pattern_evaluations_determine:
  assumes injective: "inj_on f B"
    and scope: "pattern_variables p\<subseteq>B" "pattern_variables q\<subseteq>B"
    and payloads: "evaluate_pattern (\<lambda>a. Payload_Term (f a)) p =
      evaluate_pattern (\<lambda>a. Payload_Term (f a)) q"
    and targets: "evaluate_pattern (\<lambda>_. Target_Term k) p =
      evaluate_pattern (\<lambda>_. Target_Term k) q"
  shows "p=q"
  using scope payloads targets
proof (induction p arbitrary: q)
  case (Pattern_Variable a)
  then show ?case using injective by (cases q) (auto simp: inj_on_def)
next
  case (Pattern_Target t)
  then show ?case by (cases q) auto
next
  case (Pattern_Payload b)
  then show ?case by (cases q) auto
next
  case (Pattern_Pair p s)
  then show ?case by (cases q) auto
qed

theorem pattern_instances_determine:
  assumes injective: "inj_on f B"
    and first: "pattern_instance ((\<lambda>a. (a,Payload_Term (f a))) ` B) p x"
      "pattern_instance ((\<lambda>a. (a,Payload_Term (f a))) ` B) q x"
    and second: "pattern_instance ((\<lambda>a. (a,Target_Term k)) ` B) p y"
      "pattern_instance ((\<lambda>a. (a,Target_Term k)) ` B) q y"
  shows "p=q"
  by (rule pattern_evaluations_determine[OF injective])
    (use first second in \<open>auto simp: graph_pattern_instance\<close>)

section \<open>Complete material operands determine all five patterns\<close>

theorem material_pattern_instances_determine:
  assumes injective: "inj_on f B"
    and first: "material_pattern_instance ((\<lambda>a. (a,Payload_Term (f a))) ` B) M x a e b g"
      "material_pattern_instance ((\<lambda>a. (a,Payload_Term (f a))) ` B) N x a e b g"
    and second: "material_pattern_instance ((\<lambda>a. (a,Target_Term k)) ` B) M y a' e' b' g'"
      "material_pattern_instance ((\<lambda>a. (a,Target_Term k)) ` B) N y a' e' b' g'"
  shows "M=N"
proof -
  have fields: "material_source M=material_source N" "material_atoms M=material_atoms N"
    "material_edges M=material_edges N" "material_counts M=material_counts N"
    "material_functions M=material_functions N"
    using first second unfolding material_pattern_instance_def
    by (blast intro: pattern_instances_determine[OF injective])+
  show ?thesis using fields by (cases M; cases N) auto
qed

section \<open>A single substitution cannot distinguish every literal from a variable\<close>

lemma evaluate_exact_term_pattern [simp]:
  "evaluate_pattern h (exact_term_pattern t)=t"
  by (induction t) auto

theorem one_substitution_does_not_determine:
  assumes "term_formed (h a)"
  shows "\<exists>p q. pattern_formed p \<and> pattern_formed q \<and> p\<noteq>q \<and>
    pattern_variables p\<subseteq>{a} \<and> pattern_variables q\<subseteq>{a} \<and>
    evaluate_pattern h p=evaluate_pattern h q"
proof -
  have different: "Pattern_Variable a \<noteq> exact_term_pattern (h a)"
  proof
    assume same: "Pattern_Variable a = exact_term_pattern (h a)"
    have "{a}={}" using arg_cong[OF same, where f=pattern_variables] by simp
    then show False by simp
  qed
  show ?thesis
    by (rule exI[of _ "Pattern_Variable a"], rule exI[of _ "exact_term_pattern (h a)"])
      (use assms different in auto)
qed

text \<open>
  The first substitution gives distinct payload values to the variables in
  the supplied scope. The second gives every variable one target value.
  A variable cannot agree with a fixed payload under the second substitution,
  or with a fixed target under the first. Pair structure is preserved by both.
  Induction therefore recovers the complete pattern, including repeated uses
  of the same variable and every literal value.

  The target is arbitrary. Formation is required when these substitutions
  are used as admitted binding tables; the algebraic determination theorem
  itself needs only the stated constructor separation and injective payloads.
  This is a property of the finite pattern grammar, with no restriction on
  future terms or pattern depth. It does not infer a program's meaning from
  finitely many calls. The single-substitution counterexample identifies why
  both readings are needed for this general class.
\<close>

end
