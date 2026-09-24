theory Development_Loci
  imports Native_Path_Stores Development_Problems Factor_Finite_Payload_Literals
begin

section \<open>A locus is a path, and a role and a kind are the families that hold a row\<close>

text \<open>
  A locus is a path and nothing else, and a row is what the development's store holds at it. A kind is the
  family that holds a row and a role is the family that holds it; both are realized as prefixes of the
  locus, so no program compares a kind or a role and no octet distinguishes a refinement problem from a
  definition problem, or a request from the answer to it. A locus is a role prefix, a kind prefix and the
  key of the constant the row is about, in that order and of nothing else, so a problem, its issue, its
  request and its answer stand at one locus under four role prefixes.

  The prefixes are of one fixed width, which is what makes the three parts of a locus recoverable from it:
  a variable-width prefix would let a longer role and a shorter kind spell the same path as a shorter role
  and a longer kind. Five roles and five kinds fit in three bits each, and the assignments below are stated
  rather than computed from a numbering, so nothing but the shapes of the bits tells two loci apart.

  A HOL function reads a datatype's constructor here to compute a path; what the native program sees is the
  path, and it descends it. The contract term a problem carries stays inert: the kind prefix depends on
  which constructor the contract is and on nothing inside it.
\<close>

datatype development_role =
  Development_Problem_Role
| Development_Issue_Role
| Development_Request_Role
| Development_Answer_Role
| Development_Incumbent_Role

fun development_role_path :: "development_role \<Rightarrow> bool list" where
  "development_role_path Development_Problem_Role=[False,False,False]"
| "development_role_path Development_Issue_Role=[True,False,False]"
| "development_role_path Development_Request_Role=[False,True,False]"
| "development_role_path Development_Answer_Role=[True,True,False]"
| "development_role_path Development_Incumbent_Role=[False,False,True]"

fun development_kind_path :: "development_contract \<Rightarrow> bool list" where
  "development_kind_path (Development_Refinement t)=[False,False,False]"
| "development_kind_path (Development_Proof t)=[True,False,False]"
| "development_kind_path (Development_Presentation t)=[False,True,False]"
| "development_kind_path (Development_Definition t)=[True,True,False]"
| "development_kind_path (Development_Amendment t)=[False,False,True]"

lemma development_role_path_length [simp]: "length (development_role_path r)=3"
  by (cases r) simp_all

lemma development_kind_path_length [simp]: "length (development_kind_path k)=3"
  by (cases k) simp_all

lemma development_role_path_injective: "development_role_path r=development_role_path s \<longleftrightarrow> r=s"
  by (cases r; cases s) simp_all

text \<open>
  A kind is a family, so its prefix separates the five constructors of a contract and reads nothing inside
  the term one carries: two contracts have the same kind prefix exactly when they are the same constructor.
\<close>

lemma development_kind_path_cases:
  "development_kind_path k=development_kind_path l \<longleftrightarrow>
    (\<exists>s t. k=Development_Refinement s \<and> l=Development_Refinement t) \<or>
    (\<exists>s t. k=Development_Proof s \<and> l=Development_Proof t) \<or>
    (\<exists>s t. k=Development_Presentation s \<and> l=Development_Presentation t) \<or>
    (\<exists>s t. k=Development_Definition s \<and> l=Development_Definition t) \<or>
    (\<exists>s t. k=Development_Amendment s \<and> l=Development_Amendment t)"
  by (cases k; cases l) simp_all

lemma development_kind_path_inert:
  "development_kind_path (Development_Refinement s)=development_kind_path (Development_Refinement t)"
  "development_kind_path (Development_Proof s)=development_kind_path (Development_Proof t)"
  "development_kind_path (Development_Presentation s)=development_kind_path (Development_Presentation t)"
  "development_kind_path (Development_Definition s)=development_kind_path (Development_Definition t)"
  "development_kind_path (Development_Amendment s)=development_kind_path (Development_Amendment t)"
  by simp_all

section \<open>A locus is a role prefix, a kind prefix and the key of its constant\<close>

text \<open>
  The key of a constant is supplied, not fixed here: it is the assignment the state's own presentation
  makes, and every contract below asks of it only what @{text readiness_presents} asks of the key it takes,
  that it be injective on the constants in question. Nothing of this line therefore waits on the structural
  state that assigns it.
\<close>

definition development_locus ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_role \<Rightarrow> development_contract \<Rightarrow> nat \<Rightarrow> bool list" where
  "development_locus key r k c=development_role_path r @ development_kind_path k @ key c"

lemma development_locus_parts:
  "take 3 (development_locus key r k c)=development_role_path r"
  "take 3 (drop 3 (development_locus key r k c))=development_kind_path k"
  "drop 6 (development_locus key r k c)=key c"
  by (cases r; cases k; simp_all add: development_locus_def)+

text \<open>
  A locus is composed of those three parts and of nothing else, so the three are recovered from it. The
  prefixes are of one width, which is what makes the recovery exact.
\<close>

lemma development_locus_composed:
  "development_locus key r k c=
    take 3 (development_locus key r k c) @ take 3 (drop 3 (development_locus key r k c)) @
      drop 6 (development_locus key r k c)"
  by (cases r; cases k; simp_all add: development_locus_def)

text \<open>
  Each part of a locus is determined by the locus: the role and the kind directly, and the constant
  through whatever key assignment was supplied.
\<close>

lemma development_locus_role_determines:
  assumes same: "development_locus key r k c=development_locus key s l d"
  shows "r=s"
proof -
  have "take 3 (development_locus key r k c)=take 3 (development_locus key s l d)"
    by (simp add: same)
  then have "development_role_path r=development_role_path s"
    by (simp add: development_locus_parts)
  then show ?thesis by (simp add: development_role_path_injective)
qed

lemma development_locus_kind_determines:
  assumes same: "development_locus key r k c=development_locus key s l d"
  shows "development_kind_path k=development_kind_path l"
proof -
  have "take 3 (drop 3 (development_locus key r k c))=take 3 (drop 3 (development_locus key s l d))"
    by (simp add: same)
  then show ?thesis by (simp add: development_locus_parts)
qed

lemma development_locus_key_determines:
  assumes same: "development_locus key r k c=development_locus key s l d"
  shows "key c=key d"
proof -
  have "drop 6 (development_locus key r k c)=drop 6 (development_locus key s l d)"
    by (simp add: same)
  then show ?thesis by (simp add: development_locus_parts)
qed

text \<open>
  The key assignment is a parameter and the only thing asked of it is that it be injective on the
  constants in question, as @{text readiness_presents} asks of the key it takes.
\<close>

theorem development_locus_injective:
  assumes injective: "inj_on key S" and c: "c\<in>S" and d: "d\<in>S"
    and same: "development_locus key r k c=development_locus key s l d"
  shows "r=s \<and> development_kind_path k=development_kind_path l \<and> c=d"
  using development_locus_role_determines[OF same] development_locus_kind_determines[OF same]
    inj_onD[OF injective development_locus_key_determines[OF same] c d] by simp

text \<open>
  A problem, its issue, its request and its answer stand at one locus under four role prefixes: the tail
  after the role is the kind and the key, and it does not depend on the role.
\<close>

theorem development_locus_shared_tail:
  "drop 3 (development_locus key r k c)=drop 3 (development_locus key s k c)"
  by (cases r; cases s; simp_all add: development_locus_def)


section \<open>The locus of a problem, where its subject is exactly one constant\<close>

text \<open>
  A problem's locus is stated exactly where its subject is one constant, and nowhere else: a problem whose
  subject is empty, or names more than one constant, has none. The partiality is the one the state already
  retains, and this states it rather than inventing a subject.
\<close>

definition development_subject_constant :: "development_problem \<Rightarrow> nat option" where
  "development_subject_constant p=finite_singleton_option (problem_subject p)"

theorem development_subject_constant_exact:
  "development_subject_constant p=Some c \<longleftrightarrow> problem_subject p={|c|}"
  by (simp only: development_subject_constant_def finite_singleton_option_some)

theorem development_subject_constant_absent:
  "development_subject_constant p=None \<longleftrightarrow> (\<nexists>c. problem_subject p={|c|})"
proof
  assume none: "development_subject_constant p=None"
  show "\<nexists>c. problem_subject p={|c|}"
  proof
    assume "\<exists>c. problem_subject p={|c|}"
    then obtain c where "problem_subject p={|c|}" by blast
    then have "development_subject_constant p=Some c"
      using development_subject_constant_exact[of p c] by simp
    then show False using none by simp
  qed
next
  assume absent: "\<nexists>c. problem_subject p={|c|}"
  show "development_subject_constant p=None"
  proof (cases "development_subject_constant p")
    case None
    then show ?thesis .
  next
    case (Some c)
    then have "problem_subject p={|c|}"
      using development_subject_constant_exact[of p c] by simp
    then show ?thesis using absent by blast
  qed
qed

lemma development_subject_constant_unique:
  assumes first: "problem_subject p={|c|}" and second: "problem_subject p={|d|}"
  shows "c=d"
proof -
  have "development_subject_constant p=Some c"
    using development_subject_constant_exact[of p c] first by simp
  moreover have "development_subject_constant p=Some d"
    using development_subject_constant_exact[of p d] second by simp
  ultimately show ?thesis by simp
qed

definition development_problem_locus_at ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_role \<Rightarrow> development_problem \<Rightarrow> bool list option" where
  "development_problem_locus_at key r p=
    map_option (development_locus key r (problem_contract p)) (development_subject_constant p)"

theorem development_problem_locus_at_exact:
  "development_problem_locus_at key r p=Some l \<longleftrightarrow>
    (\<exists>c. problem_subject p={|c|} \<and> l=development_locus key r (problem_contract p) c)"
proof (cases "development_subject_constant p")
  case None
  then have absent: "\<nexists>c. problem_subject p={|c|}"
    using development_subject_constant_absent[of p] by simp
  have "development_problem_locus_at key r p=None"
    using None by (simp add: development_problem_locus_at_def)
  then show ?thesis using absent by auto
next
  case (Some c)
  then have subject: "problem_subject p={|c|}"
    using development_subject_constant_exact[of p c] by simp
  have locus: "development_problem_locus_at key r p=
      Some (development_locus key r (problem_contract p) c)"
    using Some by (simp add: development_problem_locus_at_def)
  show ?thesis
  proof
    assume "development_problem_locus_at key r p=Some l"
    then have "l=development_locus key r (problem_contract p) c" using locus by simp
    then show "\<exists>c. problem_subject p={|c|} \<and> l=development_locus key r (problem_contract p) c"
      using subject by blast
  next
    assume "\<exists>c. problem_subject p={|c|} \<and> l=development_locus key r (problem_contract p) c"
    then obtain d where dsub: "problem_subject p={|d|}"
      and ld: "l=development_locus key r (problem_contract p) d" by blast
    have "d=c" by (rule development_subject_constant_unique[OF dsub subject])
    then show "development_problem_locus_at key r p=Some l" using locus ld by simp
  qed
qed

theorem development_problem_locus_at_absent:
  "development_problem_locus_at key r p=None \<longleftrightarrow> (\<nexists>c. problem_subject p={|c|})"
proof (cases "development_subject_constant p")
  case None
  then have absent: "\<nexists>c. problem_subject p={|c|}"
    using development_subject_constant_absent[of p] by simp
  have "development_problem_locus_at key r p=None"
    using None by (simp add: development_problem_locus_at_def)
  then show ?thesis using absent by simp
next
  case (Some c)
  then have subject: "problem_subject p={|c|}"
    using development_subject_constant_exact[of p c] by simp
  have "development_problem_locus_at key r p=
      Some (development_locus key r (problem_contract p) c)"
    using Some by (simp add: development_problem_locus_at_def)
  then show ?thesis using subject by auto
qed

text \<open>
  A notion stands at the locus of its problem under its role. The locus is stated where the problem's
  subject is one constant; every presented problem has one, so its row locus is that locus.
\<close>

definition development_located_at ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_role \<Rightarrow> development_problem \<Rightarrow> bool list" where
  "development_located_at key r p=the (development_problem_locus_at key r p)"

lemma development_located_at_subject:
  assumes subject: "problem_subject p={|c|}"
  shows "development_located_at key r p=development_locus key r (problem_contract p) c"
proof -
  have "development_subject_constant p=Some c" using subject development_subject_constant_exact by blast
  then show ?thesis by (simp add: development_located_at_def development_problem_locus_at_def)
qed

corollary development_without_subject_has_no_locus:
  assumes retained: "p\<in>set (development_without_subject ps)"
  shows "development_problem_locus_at key r p=None"
proof -
  have empty: "problem_subject p={||}"
    using retained by (simp add: development_without_subject_def)
  have "\<nexists>c. problem_subject p={|c|}"
  proof
    assume "\<exists>c. problem_subject p={|c|}"
    then obtain c where subject: "problem_subject p={|c|}" by blast
    have "c |\<in>| problem_subject p" using subject by simp
    then show False using empty by simp
  qed
  then show ?thesis by (simp add: development_problem_locus_at_absent)
qed

text \<open>
  The loci of two problems of one constant are told apart by their kinds, and the loci of one problem under
  two roles by their roles: the key assignment need only be injective on the constants the problems concern.
\<close>

theorem development_problem_locus_injective:
  assumes injective: "inj_on key S"
    and first: "development_problem_locus_at key r p=Some l"
    and second: "development_problem_locus_at key s q=Some l"
    and subjects: "\<And>c. problem_subject p={|c|} \<Longrightarrow> c\<in>S" "\<And>c. problem_subject q={|c|} \<Longrightarrow> c\<in>S"
  shows "r=s \<and> development_kind_path (problem_contract p)=development_kind_path (problem_contract q) \<and>
    problem_subject p=problem_subject q"
proof -
  obtain c where cp: "problem_subject p={|c|}"
    and lc: "l=development_locus key r (problem_contract p) c"
    using first development_problem_locus_at_exact[of key r p l] by blast
  obtain d where dq: "problem_subject q={|d|}"
    and ld: "l=development_locus key s (problem_contract q) d"
    using second development_problem_locus_at_exact[of key s q l] by blast
  have same: "development_locus key r (problem_contract p) c=
      development_locus key s (problem_contract q) d"
    using lc ld by simp
  have "r=s \<and> development_kind_path (problem_contract p)=development_kind_path (problem_contract q) \<and> c=d"
    by (rule development_locus_injective[OF injective subjects(1)[OF cp] subjects(2)[OF dq] same])
  then show ?thesis using cp dq by simp
qed

section \<open>A presented locus holds no octet but the empty payload\<close>

text \<open>
  A locus is presented as the path its bits spell, so every leaf of the presented locus is a
  @{const bit_term} shape or the empty payload that ends the list: the only octet anywhere in it is the
  empty one, and two loci are told apart by their shapes alone.
\<close>

theorem development_locus_payload_octets:
  "finite_term_payloads (finite_path (development_locus key r k c))={|[]|}"
proof -
  have "\<And>bs. finite_term_payloads (finite_path bs)={|[]|}"
  proof -
    fix bs show "finite_term_payloads (finite_path bs)={|[]|}"
      by (induction bs) (simp_all add: finite_path_def finite_bit_def)
  qed
  then show ?thesis .
qed

theorem development_locus_term_formed:
  "term_formed (path_term (development_locus key r k c))"
  by simp

theorem development_locus_term_injective:
  assumes injective: "inj_on key S" and c: "c\<in>S" and d: "d\<in>S"
    and same: "path_term (development_locus key r k c)=path_term (development_locus key s l d)"
  shows "r=s \<and> development_kind_path k=development_kind_path l \<and> c=d"
proof (rule development_locus_injective[OF injective c d])
  show "development_locus key r k c=development_locus key s l d"
    using same path_term_injective[of "development_locus key r k c" "development_locus key s l d"]
    by simp
qed

end
