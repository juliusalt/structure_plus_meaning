theory Factor_Executable_Premises
  imports Factor_Executable_Calls Factor_Executable_Material_Syntax
    Factor_Executable_Families Factor_Executable_Schemas
begin

section \<open>Recovering the two native premise forms\<close>

type_synonym 'u finite_native_premise =
  "('u definition_site \<times> local_address finite_term_pattern) + local_address finite_material_pattern"

fun decode_finite_native_premise :: "'u finite_native_premise \<Rightarrow> 'u native_premise" where
  "decode_finite_native_premise (Inl c) = Inl (decode_finite_call_pattern c)"
| "decode_finite_native_premise (Inr M) = Inr (decode_finite_material M)"

lemma decode_finite_native_premise_injective [simp]:
  "decode_finite_native_premise p=decode_finite_native_premise q \<longleftrightarrow> p=q"
  using decode_finite_call_inj(1)
  by (cases p; cases q; auto simp: inj_def)

definition finite_native_premise_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> 'u finite_native_premise finite_syntax_reading fset" where
  "finite_native_premise_readings E u V r =
    fimage (\<lambda>(c,I,K). (Inl c,I,K)) (finite_prospective_call_readings E u V r) |\<union>|
    fimage (\<lambda>(M,I,K). (Inr M,I,K)) (finite_native_material_readings E u V r)"

theorem finite_native_premise_readings_correct:
  "(p,I,K) |\<in>| finite_native_premise_readings E u V r \<longleftrightarrow>
    native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) (fset I) (fset K)"
  by (cases p; auto simp: finite_native_premise_readings_def finite_image_member
      finite_prospective_call_readings_correct finite_native_material_readings_correct
      split: prod.splits)

theorem finite_native_premise_readings_complete:
  assumes read: "native_premise_at (decode_finite_environment E) u (fset V) r p I K"
  shows "\<exists>P F W. (P,F,W) |\<in>| finite_native_premise_readings E u V r \<and>
    decode_finite_native_premise P=p \<and> fset F=I \<and> fset W=K"
  using read
proof (cases rule: native_premise_at.cases)
  case (call d p)
  obtain P F W where member: "((d,P),F,W) |\<in>| finite_prospective_call_readings E u V r"
    and represented: "decode_finite_pattern P=p" "fset F=I" "fset W=K"
    using finite_prospective_call_readings_complete[OF call(2)] by blast
  show ?thesis
    by (rule exI[of _ "Inl (d,P)"], rule exI[of _ F], rule exI[of _ W])
       (use call(1) member represented in \<open>auto simp: finite_native_premise_readings_def finite_image_member\<close>)
next
  case (material M)
  obtain N F W where member: "(N,F,W) |\<in>| finite_native_material_readings E u V r"
    and represented: "decode_finite_material N=M" "fset F=I" "fset W=K"
    using finite_native_material_readings_complete[OF material(2)] by blast
  show ?thesis
    by (rule exI[of _ "Inr N"], rule exI[of _ F], rule exI[of _ W])
       (use material(1) member represented in \<open>auto simp: finite_native_premise_readings_def finite_image_member\<close>)
qed

corollary finite_native_premise_readings_unique:
  assumes "(p,I,K) |\<in>| finite_native_premise_readings E u V r"
    "(q,J,W) |\<in>| finite_native_premise_readings E u V r"
  shows "p=q \<and> I=J \<and> K=W"
proof -
  have first: "native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) (fset I) (fset K)"
    and second: "native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise q) (fset J) (fset W)"
    using assms by (simp_all add: finite_native_premise_readings_correct)
  show ?thesis using native_premise_unique[OF first second] by (simp add: fset_inject)
qed

lemma finite_native_premise_values_correct:
  "p |\<in>| finite_reading_values (finite_native_premise_readings E u V r) \<longleftrightarrow>
    (\<exists>I K. native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) I K)"
proof
  assume member: "p |\<in>| finite_reading_values (finite_native_premise_readings E u V r)"
  show "\<exists>I K. native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) I K"
    using member by (auto simp: finite_reading_values_member finite_native_premise_readings_correct)
next
  assume read: "\<exists>I K. native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) I K"
  obtain I K where body: "native_premise_at (decode_finite_environment E) u (fset V) r
      (decode_finite_native_premise p) I K" using read by blast
  obtain q F W where member: "(q,F,W) |\<in>| finite_native_premise_readings E u V r"
    and same: "decode_finite_native_premise q=decode_finite_native_premise p"
    using finite_native_premise_readings_complete[OF body] by blast
  show "p |\<in>| finite_reading_values (finite_native_premise_readings E u V r)"
    using member same by (auto simp: finite_reading_values_member)
qed

section \<open>Splitting a complete mixed family preserves its sockets\<close>

definition finite_socket_sum ::
  "('s \<times> 'a) fset \<Rightarrow> ('s \<times> 'b) fset \<Rightarrow> ('s \<times> ('a + 'b)) fset" where
  "finite_socket_sum Q A =
    fimage (\<lambda>(s,x). (s,Inl x)) Q |\<union>| fimage (\<lambda>(s,x). (s,Inr x)) A"

definition finite_left_sockets :: "('s \<times> ('a + 'b)) fset \<Rightarrow> ('s \<times> 'a) fset" where
  "finite_left_sockets F =
    ffUnion (fimage (\<lambda>(s,p). case p of Inl x \<Rightarrow> {|(s,x)|} | Inr y \<Rightarrow> {||}) F)"

definition finite_right_sockets :: "('s \<times> ('a + 'b)) fset \<Rightarrow> ('s \<times> 'b) fset" where
  "finite_right_sockets F =
    ffUnion (fimage (\<lambda>(s,p). case p of Inl x \<Rightarrow> {||} | Inr y \<Rightarrow> {|(s,y)|}) F)"

lemma finite_socket_sum_correct:
  "fset (finite_socket_sum Q A)=socket_sum (fset Q) (fset A)"
  by (auto simp: finite_socket_sum_def socket_sum_def fimage.rep_eq)

lemma finite_socket_parts_member [simp]:
  "(s,x) |\<in>| finite_left_sockets F \<longleftrightarrow> (s,Inl x) |\<in>| F"
  "(s,y) |\<in>| finite_right_sockets F \<longleftrightarrow> (s,Inr y) |\<in>| F"
  by (auto simp: finite_left_sockets_def finite_right_sockets_def
      finite_union_image_member split: sum.splits; metis sum.exhaust)+

lemma finite_socket_parts_inverse [simp]:
  "finite_left_sockets (finite_socket_sum Q A)=Q"
  "finite_right_sockets (finite_socket_sum Q A)=A"
  by (auto simp: fset_inject[symmetric] finite_socket_sum_correct)

lemma finite_socket_sum_inverse [simp]:
  "finite_socket_sum (finite_left_sockets F) (finite_right_sockets F)=F"
proof -
  have "(s,p) |\<in>| finite_socket_sum (finite_left_sockets F) (finite_right_sockets F)
      \<longleftrightarrow> (s,p) |\<in>| F" for s p
    by (cases p; simp add: finite_socket_sum_correct)
  then show ?thesis by (auto simp: fset_inject[symmetric])
qed

lemma decode_finite_premise_socket_sum:
  "map_relation_values decode_finite_native_premise (fset (finite_socket_sum Q A)) =
    socket_sum (map_relation_values decode_finite_call_pattern (fset Q))
      (map_relation_values decode_finite_material (fset A))"
  by (auto simp: finite_socket_sum_correct socket_sum_def map_relation_values_def
      image_Un image_image intro: rev_image_eqI)

definition finite_native_premise_family_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow>
    ((local_address \<times> ('u definition_site \<times> local_address finite_term_pattern)) fset \<times>
      (local_address \<times> local_address finite_material_pattern) fset) fset" where
  "finite_native_premise_family_readings E u V r =
    fimage (\<lambda>F. (finite_left_sockets F,finite_right_sockets F))
      (finite_family_readings E u r (\<lambda>a. finite_reading_values (finite_native_premise_readings E u V a)))"

lemma finite_native_premise_family_readings_step:
  "(Q,A) |\<in>| finite_native_premise_family_readings E u V r \<longleftrightarrow>
    finite_socket_sum Q A |\<in>| finite_family_readings E u r
      (\<lambda>a. finite_reading_values (finite_native_premise_readings E u V a))"
proof
  assume member: "(Q,A) |\<in>| finite_native_premise_family_readings E u V r"
  obtain F where present: "F |\<in>| finite_family_readings E u r
      (\<lambda>a. finite_reading_values (finite_native_premise_readings E u V a))"
    and parts: "Q=finite_left_sockets F" "A=finite_right_sockets F"
    using member by (auto simp: finite_native_premise_family_readings_def finite_image_member)
  show "finite_socket_sum Q A |\<in>| finite_family_readings E u r
      (\<lambda>a. finite_reading_values (finite_native_premise_readings E u V a))"
    using present parts by simp
next
  assume member: "finite_socket_sum Q A |\<in>| finite_family_readings E u r
      (\<lambda>a. finite_reading_values (finite_native_premise_readings E u V a))"
  show "(Q,A) |\<in>| finite_native_premise_family_readings E u V r"
    unfolding finite_native_premise_family_readings_def finite_image_member
    by (rule exI[of _ "finite_socket_sum Q A"]) (simp add: member)
qed

theorem finite_native_premise_family_readings_correct:
  "(Q,A) |\<in>| finite_native_premise_family_readings E u V r \<longleftrightarrow>
    native_premise_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset Q))
      (map_relation_values decode_finite_material (fset A))"
proof -
  have injective: "inj (decode_finite_native_premise :: 'u finite_native_premise \<Rightarrow> _)"
    by (auto simp: inj_def)
  have unique: "\<And>a p q.
    (\<exists>I K. native_premise_at (decode_finite_environment E) u (fset V) a p I K) \<Longrightarrow>
    (\<exists>I K. native_premise_at (decode_finite_environment E) u (fset V) a q I K) \<Longrightarrow> p=q"
    by (blast dest: native_premise_unique)
  show ?thesis
    by (simp only: finite_native_premise_family_readings_step
        finite_family_readings_correct[OF injective finite_native_premise_values_correct unique]
        decode_finite_premise_socket_sum native_premise_family_at_def ex_simps)
qed

theorem finite_native_premise_family_readings_complete:
  assumes family: "native_premise_family_at (decode_finite_environment E) u (fset V) r Q A"
  shows "\<exists>F G. (F,G) |\<in>| finite_native_premise_family_readings E u V r \<and>
    map_relation_values decode_finite_call_pattern (fset F)=Q \<and>
    map_relation_values decode_finite_material (fset G)=A"
proof -
  have finite: "finite Q" "finite A" using native_premise_family_formed[OF family] by auto
  have call: "\<And>s x. (s,x) \<in> Q \<Longrightarrow>
    decode_finite_call_pattern (map_prod id finite_pattern_of x)=x"
    using native_premise_family_formed[OF family]
    by (auto simp: decode_finite_call_pattern_def decode_finite_pattern_of split: prod.splits)
  have material: "\<And>s M. (s,M) \<in> A \<Longrightarrow>
    decode_finite_material (finite_material_of M)=M"
    using native_premise_family_formed[OF family] by (auto intro: decode_finite_material_of)
  have "\<exists>F. map_relation_values decode_finite_call_pattern (fset F)=Q"
    by (rule finite_relation_value_representation[OF finite(1)], rule call)
  then obtain F where calls: "map_relation_values decode_finite_call_pattern (fset F)=Q" by blast
  have "\<exists>G. map_relation_values decode_finite_material (fset G)=A"
    by (rule finite_relation_value_representation[OF finite(2)], rule material)
  then obtain G where materials: "map_relation_values decode_finite_material (fset G)=A" by blast
  have member: "(F,G) |\<in>| finite_native_premise_family_readings E u V r"
    using family calls materials by (simp add: finite_native_premise_family_readings_correct)
  show ?thesis using member calls materials by blast
qed

corollary finite_native_premise_family_readings_unique:
  assumes "(Q,A) |\<in>| finite_native_premise_family_readings E u V r"
    "(W,B) |\<in>| finite_native_premise_family_readings E u V r"
  shows "Q=W \<and> A=B"
proof -
  have first: "native_premise_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset Q))
      (map_relation_values decode_finite_material (fset A))"
    and second: "native_premise_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset W))
      (map_relation_values decode_finite_material (fset B))"
    using assms by (simp_all add: finite_native_premise_family_readings_correct)
  have injective: "inj (decode_finite_material :: local_address finite_material_pattern \<Rightarrow> _)"
    by (auto simp: inj_def)
  show ?thesis using native_premise_family_unique[OF first second]
    by (simp add: map_relation_values_injective[OF decode_finite_call_inj(1)]
        map_relation_values_injective[OF injective] fset_inject)
qed

section \<open>The prospective family is the call-only case\<close>

definition finite_prospective_family_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow>
    (local_address \<times> ('u definition_site \<times> local_address finite_term_pattern)) fset fset" where
  "finite_prospective_family_readings E u V r =
    fimage fst (ffilter (\<lambda>(Q,A). A={||}) (finite_native_premise_family_readings E u V r))"

theorem finite_prospective_family_readings_correct:
  "Q |\<in>| finite_prospective_family_readings E u V r \<longleftrightarrow>
    prospective_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset Q))"
proof -
  have step: "Q |\<in>| finite_prospective_family_readings E u V r \<longleftrightarrow>
      (Q,{||}) |\<in>| finite_native_premise_family_readings E u V r"
    by (simp only: finite_prospective_family_readings_def finite_image_member
        split_paired_Ex fst_conv; auto)
  show ?thesis
    by (simp only: step finite_native_premise_family_readings_correct)
       (simp add: map_relation_values_def native_premise_family_calls_only)
qed

theorem finite_prospective_family_readings_complete:
  assumes read: "prospective_family_at (decode_finite_environment E) u (fset V) r Q"
  shows "\<exists>F. F |\<in>| finite_prospective_family_readings E u V r \<and>
    map_relation_values decode_finite_call_pattern (fset F)=Q"
proof -
  have finite: "finite Q" using prospective_family_formed[OF read] by blast
  have inverse: "\<And>s x. (s,x) \<in> Q \<Longrightarrow>
    decode_finite_call_pattern (map_prod id finite_pattern_of x)=x"
    using prospective_family_formed[OF read]
    by (auto simp: decode_finite_call_pattern_def decode_finite_pattern_of split: prod.splits)
  have "\<exists>F. map_relation_values decode_finite_call_pattern (fset F)=Q"
    by (rule finite_relation_value_representation[OF finite], rule inverse)
  then obtain F where represented: "map_relation_values decode_finite_call_pattern (fset F)=Q" by blast
  show ?thesis by (rule exI[of _ F])
    (use read represented in \<open>simp add: finite_prospective_family_readings_correct\<close>)
qed

corollary finite_prospective_family_readings_unique:
  assumes "Q |\<in>| finite_prospective_family_readings E u V r"
    "W |\<in>| finite_prospective_family_readings E u V r"
  shows "Q=W"
proof -
  have first: "prospective_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset Q))"
    and second: "prospective_family_at (decode_finite_environment E) u (fset V) r
      (map_relation_values decode_finite_call_pattern (fset W))"
    using assms by (simp_all add: finite_prospective_family_readings_correct)
  show ?thesis using prospective_family_unique[OF first second]
    by (simp add: map_relation_values_injective[OF decode_finite_call_inj(1)] fset_inject)
qed

export_code finite_native_premise_readings finite_native_premise_family_readings
  finite_prospective_family_readings checking SML

text \<open>
  Each native premise retains its full syntax interior and external slots.
  A family is read as one complete relation before its call and material rows
  are separated. This preserves their joint domain and rejects a socket that
  lacks a reading. The finite reader covers every admitted native premise
  family and returns the same uniquely determined values at the same sockets.
\<close>

end
