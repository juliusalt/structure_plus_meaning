theory Factor_Executable_Instances
  imports Factor_Executable_Material Factor_Material_Patterns
begin

section \<open>Every instance determined by a finite binding relation\<close>

fun finite_pattern_instances ::
  "('a \<times> finite_factor_term) fset \<Rightarrow> 'a finite_term_pattern \<Rightarrow> finite_factor_term fset" where
  "finite_pattern_instances V (Finite_Variable a) = fimage snd (ffilter (\<lambda>x. fst x=a) V)"
| "finite_pattern_instances V (Finite_Pattern_Target t) =
    (if finite_target_formed t then {|Finite_Target t|} else {||})"
| "finite_pattern_instances V (Finite_Pattern_Payload v) =
    (if octets_formed v then {|Finite_Payload v|} else {||})"
| "finite_pattern_instances V (Finite_Pattern_Pair p q) =
    ffUnion (fimage (\<lambda>x. fimage (Finite_Pair x) (finite_pattern_instances V q))
      (finite_pattern_instances V p))"

theorem finite_pattern_instances_complete:
  "pattern_instance (decode_finite_term_bindings V) (decode_finite_pattern p) t \<longleftrightarrow>
    (\<exists>C\<in>fset (finite_pattern_instances V p). decode_finite_term C=t)"
proof (induction p arbitrary: t)
  case (Finite_Variable a)
  then show ?case
    by (auto simp: decode_finite_term_bindings_def fimage.rep_eq Bex_def split_paired_Ex)
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto simp: finite_target_formed_correct)
next
  case (Finite_Pattern_Payload v)
  then show ?case by auto
next
  case (Finite_Pattern_Pair p q)
  then show ?case by (auto simp: fimage.rep_eq ffUnion.rep_eq Bex_def;
      metis decode_finite_term.simps(3) imageI)
qed

lemma finite_pattern_instances_member:
  "t |\<in>| finite_pattern_instances V p \<longleftrightarrow> finite_pattern_instance V p t"
  using finite_pattern_instances_complete[of V p "decode_finite_term t"]
  by (simp add: finite_pattern_instance_correct)

lemma finite_pattern_instances_exists:
  "fBex (finite_pattern_instances V p) (\<lambda>C. P (decode_finite_term C)) \<longleftrightarrow>
    (\<exists>t. pattern_instance (decode_finite_term_bindings V) (decode_finite_pattern p) t \<and> P t)"
  by (auto simp: finite_pattern_instances_complete)

section \<open>Material patterns preserve all five operands\<close>

record 'a finite_material_pattern =
  finite_material_source :: "'a finite_term_pattern"
  finite_material_atoms :: "'a finite_term_pattern"
  finite_material_edges :: "'a finite_term_pattern"
  finite_material_counts :: "'a finite_term_pattern"
  finite_material_functions :: "'a finite_term_pattern"

definition decode_finite_material :: "'a finite_material_pattern \<Rightarrow> 'a material_pattern" where
  "decode_finite_material M =
    \<lparr>material_source=decode_finite_pattern (finite_material_source M),
     material_atoms=decode_finite_pattern (finite_material_atoms M),
     material_edges=decode_finite_pattern (finite_material_edges M),
     material_counts=decode_finite_pattern (finite_material_counts M),
     material_functions=decode_finite_pattern (finite_material_functions M)\<rparr>"

definition finite_material_of :: "'a material_pattern \<Rightarrow> 'a finite_material_pattern" where
  "finite_material_of M =
    \<lparr>finite_material_source=finite_pattern_of (material_source M),
     finite_material_atoms=finite_pattern_of (material_atoms M),
     finite_material_edges=finite_pattern_of (material_edges M),
     finite_material_counts=finite_pattern_of (material_counts M),
     finite_material_functions=finite_pattern_of (material_functions M)\<rparr>"

definition finite_material_formed :: "'a finite_material_pattern \<Rightarrow> bool" where
  "finite_material_formed M \<longleftrightarrow>
    finite_pattern_formed (finite_material_source M) \<and>
    finite_pattern_formed (finite_material_atoms M) \<and>
    finite_pattern_formed (finite_material_edges M) \<and>
    finite_pattern_formed (finite_material_counts M) \<and>
    finite_pattern_formed (finite_material_functions M)"

definition finite_material_variables :: "'a finite_material_pattern \<Rightarrow> 'a fset" where
  "finite_material_variables M = finite_pattern_variables (finite_material_source M) |\<union>|
    finite_pattern_variables (finite_material_atoms M) |\<union>|
    finite_pattern_variables (finite_material_edges M) |\<union>|
    finite_pattern_variables (finite_material_counts M) |\<union>|
    finite_pattern_variables (finite_material_functions M)"

lemma finite_material_formed_correct:
  "finite_material_formed M \<longleftrightarrow> material_pattern_formed (decode_finite_material M)"
  by (simp add: finite_material_formed_def material_pattern_formed_def material_fields_def
      decode_finite_material_def finite_pattern_formed_correct)

lemma finite_material_variables_correct:
  "fset (finite_material_variables M) = material_variables (decode_finite_material M)"
  by (auto simp: finite_material_variables_def material_variables_def material_fields_def
      decode_finite_material_def finite_pattern_variables_correct)

lemma finite_material_of_decode [simp]: "finite_material_of (decode_finite_material M) = M"
  by (cases M) (simp add: finite_material_of_def decode_finite_material_def)

lemma decode_finite_material_injective [simp]:
  "decode_finite_material M = decode_finite_material N \<longleftrightarrow> M=N"
  using finite_material_of_decode[of M] finite_material_of_decode[of N] by metis

lemma decode_finite_material_of:
  assumes "material_pattern_formed M"
  shows "decode_finite_material (finite_material_of M) = M"
  using assms by (cases M)
    (simp add: decode_finite_material_def finite_material_of_def material_pattern_formed_def
      material_fields_def decode_finite_pattern_of)

definition finite_material_satisfied ::
  "('a \<times> finite_factor_term) fset \<Rightarrow> 'a finite_material_pattern \<Rightarrow> bool" where
  "finite_material_satisfied V M \<longleftrightarrow>
    fBex (finite_pattern_instances V (finite_material_source M)) (\<lambda>s.
    fBex (finite_pattern_instances V (finite_material_atoms M)) (\<lambda>a.
    fBex (finite_pattern_instances V (finite_material_edges M)) (\<lambda>e.
    fBex (finite_pattern_instances V (finite_material_counts M)) (\<lambda>b.
    fBex (finite_pattern_instances V (finite_material_functions M)) (\<lambda>f.
      finite_material_observation s a e b f)))))"

theorem finite_material_satisfied_correct:
  "finite_material_satisfied V M \<longleftrightarrow>
    material_pattern_satisfied (decode_finite_term_bindings V) (decode_finite_material M)"
  by (auto simp: finite_material_satisfied_def finite_material_observation_correct
      material_pattern_satisfied_def material_pattern_instance_def decode_finite_material_def
      finite_pattern_instances_complete; blast)

export_code finite_pattern_instances finite_material_formed finite_material_satisfied checking SML

text \<open>
  The candidates arise only from the supplied bindings and literal subterms.
  The completeness equation covers every abstract instance, including terms
  not separately supplied as finite values. It does not search the positive
  consequence relation. Set operations preserve every possible instance without
  choosing an enumeration order, even when the supplied bindings conflict.
\<close>

end
