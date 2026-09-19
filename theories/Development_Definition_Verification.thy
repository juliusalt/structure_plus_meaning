theory Development_Definition_Verification
  imports Development_Refinement_Verification
begin

section \<open>A definition answer replaces the kernel definitions of its constant\<close>

text \<open>
  A definition problem is the problem of a constant under the definition reading: its contract is
  the constant as the state declares it, marked as a definition, and its incumbent the kernel
  definitions the state states for it. Its request is the request of a problem of a constant under
  that reading, with the support and the least context of the constant's whole scope, as a
  refinement request has.

  A definition answer changes what the constant is. It replaces the constant's kernel definitions,
  and the code equations derived from them change with them, so both kinds of the subject's
  statements are replaceable; it must state a kernel definition of the subject, and nothing else
  may change. Its verdict is the verdict of an answer to a problem of a constant under these two
  readings. That every contract the library states of the constant still holds under the new
  definition is not read from the state: it is Isabelle's acceptance of every theory that states or
  consumes those contracts, established when the answer's checked context is built.
\<close>

definition development_definition_request :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_request option" where
  "development_definition_request C r a c=development_constant_request isabelle_definition_proposition
     Development_Definition C r a c"

theorem development_definition_request_fields:
  assumes request: "development_definition_request C r a c=Some (p,s,S,E)"
  shows "development_constant_problem isabelle_definition_proposition Development_Definition C r a c=Some p"
    "problem_contract p=Development_Definition s" "problem_subject p={|c|}"
    "S=development_request_support C c" "E=development_request_context C c"
    "\<forall>q\<in>set (development_statements isabelle_definition_proposition C c). Isabelle_Definition q |\<in>| E"
proof -
  note fields=development_constant_request_fields[OF request[unfolded development_definition_request_def]]
  show "development_constant_problem isabelle_definition_proposition Development_Definition C r a c=Some p"
    by (rule fields(1))
  show "problem_contract p=Development_Definition s" by (rule fields(2))
  show "problem_subject p={|c|}" by (rule fields(3))
  show "S=development_request_support C c" by (rule fields(4))
  show "E=development_request_context C c" by (rule fields(5))
  show "\<forall>q\<in>set (development_statements isabelle_definition_proposition C c). Isabelle_Definition q |\<in>| E"
  proof
    fix q assume "q\<in>set (development_statements isabelle_definition_proposition C c)"
    then obtain e where read: "isabelle_definition_proposition e=Some q" and member: "e |\<in>| E"
      using fields(6) by blast
    have "e=Isabelle_Definition q" using read by (simp only: isabelle_definition_proposition_exact)
    then show "Isabelle_Definition q |\<in>| E" using member by simp
  qed
qed

definition development_definition_replaceable :: "isabelle_entity \<Rightarrow> bool" where
  "development_definition_replaceable e \<longleftrightarrow> development_demanded isabelle_definition_proposition e \<or>
    development_demanded isabelle_code_equation_proposition e"

definition development_definition_verdict ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_constant_verdict" where
  "development_definition_verdict=development_constant_verdict development_definition_replaceable
    (development_demanded isabelle_definition_proposition)"

text \<open>
  An accepted definition verdict states what the request demanded of the answer state: every
  entity other than the subject's kernel definitions and code equations and the declarations
  persists under the correspondence, nothing but kernel definitions and code equations of the
  subject is added, the subject has a kernel definition, every definition and code equation of the
  subject stays within the issued support, the answer state is closed and keeps the roots, and the
  correspondence is injective: the general contract read through the definition instance.
\<close>

theorem development_definition_verdict_contract:
  assumes accepted: "development_verdict_accepted (development_definition_verdict S (p,s,support,E) S')"
  defines "f\<equiv>isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  shows "\<And>e. e\<in>set (snd (snd S)) \<Longrightarrow>
      \<not>development_answer_statement development_definition_replaceable (snd S) (problem_subject p) e \<Longrightarrow>
      isabelle_declared_constant e=None \<Longrightarrow> isabelle_entity_rename f e\<in>set (snd (snd S'))"
    and "\<And>e'. e'\<in>set (snd (snd S')) \<Longrightarrow>
      (\<exists>e\<in>set (snd (snd S)). e'=isabelle_entity_rename f e) \<or>
      development_answer_statement development_definition_replaceable (snd S') (fimage f (problem_subject p)) e'"
    and "\<exists>e'\<in>set (snd (snd S')). development_answer_statement
      (development_demanded isabelle_definition_proposition) (snd S') (fimage f (problem_subject p)) e'"
    and "\<And>e' q d. e'\<in>set (snd (snd S')) \<Longrightarrow>
      development_answer_statement development_definition_replaceable (snd S') (fimage f (problem_subject p)) e' \<Longrightarrow>
      isabelle_specified_proposition e'=Some q \<Longrightarrow> d\<in>set (isabelle_term_constants q) \<Longrightarrow> d |\<in>| fimage f support"
    and "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))"
    and "map (isabelle_term_rename f) (fst S)=fst S'"
    and "inj f"
  using development_constant_verdict_contract[OF accepted[unfolded development_definition_verdict_def]]
  unfolding f_def by blast+

end
