theory Development_Entity_Keys
  imports Isabelle_Entities Natural_Binary_Digits Complete_Value_References
begin

section \<open>A subject's key is the path of its first occurrence\<close>

text \<open>
  A keyed question names each of its candidates by a key, a path of shapes, and asks of the key only that
  it be injective on the candidates. The first-occurrence key of a subject in a list is the path of the
  binary digits of the position of its first occurrence there: it is determined by the subject's identity
  and the list alone, so one list names one subject by one key in every question asked on it. It orders
  nothing and no program compares its value.
\<close>

definition first_occurrence_key :: "'a list \<Rightarrow> 'a \<Rightarrow> bool list" where
  "first_occurrence_key xs x=natural_binary_digits
    (case value_reference_index x xs of None \<Rightarrow> length xs | Some i \<Rightarrow> i)"

lemma first_occurrence_key_at:
  assumes "x\<in>set xs"
  obtains i where "value_reference_index x xs=Some i" "i<length xs" "xs!i=x"
    "first_occurrence_key xs x=natural_binary_digits i"
proof -
  obtain i where index: "value_reference_index x xs=Some i"
    using assms value_reference_index_absent[of x xs] by (cases "value_reference_index x xs") auto
  show thesis using that[OF index] value_reference_index_read[OF index]
    by (simp add: first_occurrence_key_def index)
qed

lemma first_occurrence_key_injective:
  assumes x: "x\<in>set xs" and y: "y\<in>set xs"
    and same: "first_occurrence_key xs x=first_occurrence_key xs y"
  shows "x=y"
proof -
  obtain i where "xs!i=x" "first_occurrence_key xs x=natural_binary_digits i"
    by (rule first_occurrence_key_at[OF x])
  moreover obtain j where "xs!j=y" "first_occurrence_key xs y=natural_binary_digits j"
    by (rule first_occurrence_key_at[OF y])
  ultimately show ?thesis using same by simp
qed

lemma first_occurrence_key_inj_on: "inj_on (first_occurrence_key xs) (set xs)"
  by (rule inj_onI) (rule first_occurrence_key_injective)

text \<open>
  A value absent from the list takes the key of the list's length, past every position, so a value whose key
  is the key of a member is a member.
\<close>

lemma first_occurrence_key_member:
  assumes y: "y\<in>set xs" and same: "first_occurrence_key xs x=first_occurrence_key xs y"
  shows "x\<in>set xs"
proof -
  obtain i where i: "value_reference_index y xs=Some i" "i<length xs" "xs!i=y"
    "first_occurrence_key xs y=natural_binary_digits i"
    by (rule first_occurrence_key_at[OF y])
  show ?thesis
  proof (cases "value_reference_index x xs")
    case None
    then have "natural_binary_digits (length xs)=natural_binary_digits i"
      using same i(4) by (simp add: first_occurrence_key_def)
    then have "length xs=i" by simp
    then show ?thesis using i(2) by simp
  next
    case (Some j)
    then show ?thesis using value_reference_index_read[OF Some] nth_mem by metis
  qed
qed

text \<open>A first occurrence in a prefix stays where it was, so keys continue when a list is extended.\<close>

lemma first_occurrence_key_append:
  assumes member: "x\<in>set xs"
  shows "first_occurrence_key (xs@ys) x=first_occurrence_key xs x"
  using member value_reference_index_absent[of x xs]
  by (cases "value_reference_index x xs") (simp_all add: first_occurrence_key_def value_reference_index_append_member[OF member])

text \<open>
  The executable key of a state's entities is the first-occurrence key of an entity in the state's own
  entity list; it is injective on those entities, which is all a keyed question asks of its key, and one
  key names one entity across every question asked on that state.
\<close>

definition development_entity_key :: "isabelle_context \<Rightarrow> isabelle_entity \<Rightarrow> bool list" where
  "development_entity_key C=first_occurrence_key (snd C)"

lemma development_entity_key_injective: "inj_on (development_entity_key C) (set (snd C))"
  by (simp only: development_entity_key_def first_occurrence_key_inj_on)

end
