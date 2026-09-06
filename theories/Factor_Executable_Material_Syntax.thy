theory Factor_Executable_Material_Syntax
  imports Factor_Executable_Patterns Factor_Executable_Instances
begin

section \<open>Complete ordered vectors of actual pattern readings\<close>

fun finite_pattern_vector_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address list \<Rightarrow> local_address finite_term_pattern list finite_syntax_reading fset" where
  "finite_pattern_vector_readings E u V [] =
    (if finite_environment_formed E then {|([],{||},{||})|} else {||})"
| "finite_pattern_vector_readings E u V (r#rs) = ffUnion (fimage (\<lambda>(p,A,B).
    ffUnion (fimage (\<lambda>(ps,J,W).
      if A |\<inter>| J={||} \<and> (A |\<union>| J) |\<inter>| (B |\<union>| W)={||}
      then {|(p#ps,A |\<union>| J,B |\<union>| W)|} else {||})
        (finite_pattern_vector_readings E u V rs))) (finite_pattern_readings E u V r))"

lemma finite_pattern_vector_cons_member:
  "(ps,I,K) |\<in>| finite_pattern_vector_readings E u V (r#rs) \<longleftrightarrow>
    (\<exists>p qs A B J W. ps=p#qs \<and> (p,A,B) |\<in>| finite_pattern_readings E u V r \<and>
      (qs,J,W) |\<in>| finite_pattern_vector_readings E u V rs \<and>
      A |\<inter>| J={||} \<and> (A |\<union>| J) |\<inter>| (B |\<union>| W)={||} \<and>
      I=A |\<union>| J \<and> K=B |\<union>| W)"
  by (simp only: finite_pattern_vector_readings.simps(2) finite_union_image_member split_paired_Ex
      prod.case finite_singleton_when_member prod.inject; auto; blast)

lemma finite_pattern_vector_readings_sound:
  assumes "(ps,I,K) |\<in>| finite_pattern_vector_readings E u V rs"
  shows "pattern_vector_at (decode_finite_environment E) u (fset V) rs
    (map decode_finite_pattern ps) (fset I) (fset K)"
  using assms
proof (induction rs arbitrary: ps I K)
  case Nil
  then show ?case by (auto simp: pattern_vector_nil finite_environment_formed_correct split: if_splits)
next
  case (Cons r rs)
  obtain p qs A B J W where shape: "ps=p#qs"
    and head: "(p,A,B) |\<in>| finite_pattern_readings E u V r"
    and tail: "(qs,J,W) |\<in>| finite_pattern_vector_readings E u V rs"
    and boundary: "A |\<inter>| J={||}" "(A |\<union>| J) |\<inter>| (B |\<union>| W)={||}"
      "I=A |\<union>| J" "K=B |\<union>| W"
    using Cons.prems by (simp only: finite_pattern_vector_cons_member; blast)
  have first: "pattern_quoted_at (decode_finite_environment E) u (fset V) r
      (decode_finite_pattern p) (fset A) (fset B)"
    using head by (simp add: finite_pattern_readings_correct)
  have rest: "pattern_vector_at (decode_finite_environment E) u (fset V) rs
      (map decode_finite_pattern qs) (fset J) (fset W)"
    by (rule Cons.IH[OF tail])
  have separate: "fset A \<inter> fset J={}" "(fset A \<union> fset J) \<inter> (fset B \<union> fset W)={}"
    using boundary by (simp_all add: fset_inject[symmetric])
  show ?case using pattern_vector_at.cons[OF first rest separate] shape boundary by simp
qed

lemma finite_pattern_vector_readings_complete:
  assumes "pattern_vector_at (decode_finite_environment E) u (fset V) rs ps I K"
  shows "\<exists>P F W. (P,F,W) |\<in>| finite_pattern_vector_readings E u V rs \<and>
    map decode_finite_pattern P=ps \<and> fset F=I \<and> fset W=K"
  using assms
proof (induction rule: pattern_vector_at.induct)
  case empty
  have member: "([],{||},{||}) |\<in>| finite_pattern_vector_readings E u V []"
    using empty by (simp add: finite_environment_formed_correct)
  show ?case by (rule exI[of _ "[]"], rule exI[of _ "{||}"], rule exI[of _ "{||}"])
    (use member in auto)
next
  case (cons r p A B rs ps I K)
  obtain P F G where head: "(P,F,G) |\<in>| finite_pattern_readings E u V r"
    and first: "decode_finite_pattern P=p" "fset F=A" "fset G=B"
    using finite_pattern_readings_complete[OF cons.hyps(1)] by blast
  obtain PS J W where tail: "(PS,J,W) |\<in>| finite_pattern_vector_readings E u V rs"
    and rest: "map decode_finite_pattern PS=ps" "fset J=I" "fset W=K"
    using cons.IH by blast
  have separate: "F |\<inter>| J={||}" "(F |\<union>| J) |\<inter>| (G |\<union>| W)={||}"
    using cons.hyps(3,4) first rest by (simp_all add: fset_inject[symmetric])
  have member: "(P#PS,F |\<union>| J,G |\<union>| W) |\<in>| finite_pattern_vector_readings E u V (r#rs)"
    unfolding finite_pattern_vector_cons_member
    by (rule exI[of _ P], rule exI[of _ PS], rule exI[of _ F], rule exI[of _ G],
        rule exI[of _ J], rule exI[of _ W]) (use head tail separate in blast)
  show ?case
    by (rule exI[of _ "P#PS"], rule exI[of _ "F |\<union>| J"], rule exI[of _ "G |\<union>| W"])
       (use member first rest in auto)
qed

lemma decode_finite_patterns_injective [simp]:
  "map decode_finite_pattern ps=map decode_finite_pattern qs \<longleftrightarrow> ps=qs"
proof (induction ps arbitrary: qs)
  case Nil
  then show ?case by (cases qs) auto
next
  case (Cons p ps)
  then show ?case by (cases qs) auto
qed

theorem finite_pattern_vector_readings_correct:
  "(ps,I,K) |\<in>| finite_pattern_vector_readings E u V rs \<longleftrightarrow>
    pattern_vector_at (decode_finite_environment E) u (fset V) rs
      (map decode_finite_pattern ps) (fset I) (fset K)"
proof
  show "(ps,I,K) |\<in>| finite_pattern_vector_readings E u V rs \<Longrightarrow>
    pattern_vector_at (decode_finite_environment E) u (fset V) rs
      (map decode_finite_pattern ps) (fset I) (fset K)"
    by (rule finite_pattern_vector_readings_sound)
next
  assume read: "pattern_vector_at (decode_finite_environment E) u (fset V) rs
      (map decode_finite_pattern ps) (fset I) (fset K)"
  show "(ps,I,K) |\<in>| finite_pattern_vector_readings E u V rs"
    using finite_pattern_vector_readings_complete[OF read] by (simp add: fset_inject)
qed

section \<open>Record frames retain their physical boundary\<close>

definition finite_frame_readings ::
  "local_address fset \<Rightarrow> local_address \<Rightarrow> local_address list \<Rightarrow>
    'a finite_syntax_reading fset \<Rightarrow> 'a finite_syntax_reading fset" where
  "finite_frame_readings V r ps X = ffUnion (fimage (\<lambda>(p,J,K).
    let F=finsert r (fset_of_list ps); I=F |\<union>| J in
    if F |\<inter>| J={||} \<and> I |\<inter>| (K |\<union>| V)={||}
    then {|(p,I,K)|} else {||}) X)"

lemma finite_frame_readings_member:
  "(p,I,K) |\<in>| finite_frame_readings V r ps X \<longleftrightarrow>
    (\<exists>J. (p,J,K) |\<in>| X \<and> finsert r (fset_of_list ps) |\<inter>| J={||} \<and>
      I=finsert r (fset_of_list ps |\<union>| J) \<and> I |\<inter>| (K |\<union>| V)={||})"
  by (simp only: finite_frame_readings_def Let_def finite_union_image_member split_paired_Ex
      prod.case finite_singleton_when_member prod.inject; auto; blast)

definition finite_pattern_record_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> nat \<Rightarrow>
    local_address finite_term_pattern list finite_syntax_reading fset" where
  "finite_pattern_record_readings E u V r n = (if finite_environment_formed E then
    ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>(ports,roots).
      finite_frame_readings V r ports (finite_pattern_vector_readings E u V roots))
        (finite_record_candidates C r n))) (finite_artifacts_at E u)) else {||})"

lemma finite_pattern_record_readings_step:
  "(ps,I,K) |\<in>| finite_pattern_record_readings E u V r n \<longleftrightarrow>
    finite_environment_formed E \<and> (\<exists>C ports roots J.
      C |\<in>| finite_artifacts_at E u \<and> record_at (decode_finite_object C) r ports roots \<and>
      length roots=n \<and> (ps,J,K) |\<in>| finite_pattern_vector_readings E u V roots \<and>
      finsert r (fset_of_list ports) |\<inter>| J={||} \<and>
      I=finsert r (fset_of_list ports |\<union>| J) \<and> I |\<inter>| (K |\<union>| V)={||})"
  by (cases "finite_environment_formed E";
      simp only: finite_pattern_record_readings_def if_True if_False finite_union_image_member
      split_paired_Ex prod.case finite_frame_readings_member finite_record_candidates_correct; auto)

theorem finite_pattern_record_readings_correct:
  "(ps,I,K) |\<in>| finite_pattern_record_readings E u V r n \<longleftrightarrow>
    pattern_record_at (decode_finite_environment E) u (fset V) r
      (map decode_finite_pattern ps) (fset I) (fset K) \<and> length ps=n"
proof
  assume member: "(ps,I,K) |\<in>| finite_pattern_record_readings E u V r n"
  obtain C ports roots J where ef: "finite_environment_formed E"
    and source: "C |\<in>| finite_artifacts_at E u"
    and rec: "record_at (decode_finite_object C) r ports roots" and arity: "length roots=n"
    and vector: "(ps,J,K) |\<in>| finite_pattern_vector_readings E u V roots"
    and boundary: "finsert r (fset_of_list ports) |\<inter>| J={||}"
      "I=finsert r (fset_of_list ports |\<union>| J)" "I |\<inter>| (K |\<union>| V)={||}"
    using member by (simp only: finite_pattern_record_readings_step; blast)
  have formed: "environment_formed (decode_finite_environment E)"
    using ef by (simp add: finite_environment_formed_correct)
  have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
    using source by (simp add: finite_artifacts_at_member)
  have body: "pattern_vector_at (decode_finite_environment E) u (fset V) roots
      (map decode_finite_pattern ps) (fset J) (fset K)"
    using vector by (simp add: finite_pattern_vector_readings_correct)
  have read: "pattern_record_at (decode_finite_environment E) u (fset V) r
      (map decode_finite_pattern ps) (fset I) (fset K)"
    unfolding pattern_record_at_def
    apply (rule conjI[OF formed])
    apply (rule exI[of _ "decode_finite_object C"], rule exI[of _ ports], rule exI[of _ roots])
    apply (rule exI[of _ "fset J"])
    using art rec body boundary by (auto simp: fset_inject[symmetric] fset_of_list.rep_eq)
  have "length ps=n" using pattern_vector_formed[OF body] arity by simp
  then show "pattern_record_at (decode_finite_environment E) u (fset V) r
      (map decode_finite_pattern ps) (fset I) (fset K) \<and> length ps=n"
    using read by blast
next
  assume read: "pattern_record_at (decode_finite_environment E) u (fset V) r
      (map decode_finite_pattern ps) (fset I) (fset K) \<and> length ps=n"
  obtain C ports roots J where ef: "environment_formed (decode_finite_environment E)"
    and source: "C |\<in>| finite_artifacts_at E u"
    and rec: "record_at (decode_finite_object C) r ports roots"
    and body: "pattern_vector_at (decode_finite_environment E) u (fset V) roots
      (map decode_finite_pattern ps) J (fset K)"
    and boundary: "insert r (set ports) \<inter> J={}"
      "fset I=insert r (set ports \<union> J)" "fset I \<inter> (fset K \<union> fset V)={}"
    using read by (auto simp: pattern_record_at_def finite_artifacts_at_member)
  have fin: "finite J" using pattern_vector_boundary[OF body] by blast
  have interior: "fset (Abs_fset J)=J" by (rule Abs_fset_inverse) (simp add: fin)
  have vector: "(ps,Abs_fset J,K) |\<in>| finite_pattern_vector_readings E u V roots"
    using body interior by (simp add: finite_pattern_vector_readings_correct)
  have arity: "length roots=n" using pattern_vector_formed[OF body] read by auto
  have physical: "finsert r (fset_of_list ports) |\<inter>| Abs_fset J={||}"
    "I=finsert r (fset_of_list ports |\<union>| Abs_fset J)" "I |\<inter>| (K |\<union>| V)={||}"
    using boundary interior by (simp_all add: fset_inject[symmetric] fset_of_list.rep_eq)
  show "(ps,I,K) |\<in>| finite_pattern_record_readings E u V r n"
    unfolding finite_pattern_record_readings_step
    apply (rule conjI)
     apply (use ef in \<open>simp add: finite_environment_formed_correct\<close>)
    apply (rule exI[of _ C], rule exI[of _ ports], rule exI[of _ roots], rule exI[of _ "Abs_fset J"])
    using source rec arity vector physical by blast
qed

section \<open>All five operands of a native material premise\<close>

definition finite_material_fields :: "'a finite_material_pattern \<Rightarrow> 'a finite_term_pattern list" where
  "finite_material_fields M = [finite_material_source M,finite_material_atoms M,finite_material_edges M,
    finite_material_counts M,finite_material_functions M]"

lemma finite_material_fields_correct:
  "map decode_finite_pattern (finite_material_fields M)=material_fields (decode_finite_material M)"
  by (simp add: finite_material_fields_def material_fields_def decode_finite_material_def)

fun finite_material_from_fields :: "'a finite_term_pattern list \<Rightarrow> 'a finite_material_pattern fset" where
  "finite_material_from_fields [s,a,e,b,f] =
    {|\<lparr>finite_material_source=s,finite_material_atoms=a,finite_material_edges=e,
      finite_material_counts=b,finite_material_functions=f\<rparr>|}"
| "finite_material_from_fields _ = {||}"

lemma finite_material_from_fields_member:
  "M |\<in>| finite_material_from_fields ps \<longleftrightarrow> ps=finite_material_fields M"
  by (cases M; cases ps rule: finite_material_from_fields.cases)
     (auto simp: finite_material_fields_def)

definition finite_native_material_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address finite_material_pattern finite_syntax_reading fset" where
  "finite_native_material_readings E u V r = ffUnion (fimage (\<lambda>(ps,I,K).
    fimage (\<lambda>M. (M,I,K)) (finite_material_from_fields ps))
      (finite_pattern_record_readings E u V r 5))"

lemma finite_native_material_readings_step:
  "(M,I,K) |\<in>| finite_native_material_readings E u V r \<longleftrightarrow>
    (finite_material_fields M,I,K) |\<in>| finite_pattern_record_readings E u V r 5"
  by (simp only: finite_native_material_readings_def finite_union_image_member split_paired_Ex
      prod.case finite_image_member prod.inject finite_material_from_fields_member; auto)

theorem finite_native_material_readings_correct:
  "(M,I,K) |\<in>| finite_native_material_readings E u V r \<longleftrightarrow>
    native_material_at (decode_finite_environment E) u (fset V) r
      (decode_finite_material M) (fset I) (fset K)"
  by (simp only: finite_native_material_readings_step finite_pattern_record_readings_correct
      finite_material_fields_correct; simp add: finite_material_fields_def native_material_at_def)

theorem finite_native_material_readings_complete:
  assumes read: "native_material_at (decode_finite_environment E) u (fset V) r M I K"
  shows "\<exists>N F W. (N,F,W) |\<in>| finite_native_material_readings E u V r \<and>
    decode_finite_material N=M \<and> fset F=I \<and> fset W=K"
proof -
  have formed: "material_pattern_formed M" and fi: "finite I" and fk: "finite K"
    using native_material_formed[OF read] by auto
  have encoded: "decode_finite_material (finite_material_of M)=M"
    by (rule decode_finite_material_of[OF formed])
  have interior: "fset (Abs_fset I)=I" by (rule Abs_fset_inverse) (simp add: fi)
  have slots: "fset (Abs_fset K)=K" by (rule Abs_fset_inverse) (simp add: fk)
  have member: "(finite_material_of M,Abs_fset I,Abs_fset K) |\<in>| finite_native_material_readings E u V r"
    using read encoded interior slots by (simp add: finite_native_material_readings_correct)
  show ?thesis using member encoded interior slots by blast
qed

corollary finite_native_material_readings_unique:
  assumes "(M,I,K) |\<in>| finite_native_material_readings E u V r"
    "(N,J,W) |\<in>| finite_native_material_readings E u V r"
  shows "M=N \<and> I=J \<and> K=W"
proof -
  have first: "native_material_at (decode_finite_environment E) u (fset V) r
      (decode_finite_material M) (fset I) (fset K)"
    and second: "native_material_at (decode_finite_environment E) u (fset V) r
      (decode_finite_material N) (fset J) (fset W)"
    using assms by (simp_all add: finite_native_material_readings_correct)
  show ?thesis using native_material_unique[OF first second] by (simp add: fset_inject)
qed

export_code finite_pattern_vector_readings finite_pattern_record_readings finite_native_material_readings checking SML

text \<open>
  Vectors follow the fields of the actual ordered record. Their readers check
  disjoint interiors and the complete external boundary at every join. A native
  material premise recovers exactly five operands, preserving their distinct
  roles. The arity is part of this grammar, while the recursive pattern readers
  cover every finite body admitted by that grammar.
\<close>

end
