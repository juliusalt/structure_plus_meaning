theory Factor_Constructed_Program_Applications
  imports Factor_Finite_Program_Applications Listed_Set_Unions Finite_Relation_Functionality_Execution
    Established_Premises Candidate_Generators
begin

section \<open>A formed call's applications are constructed, not verified again\<close>

text \<open>
  The applications of a call are constructed by matching each clause's head against the call's term and
  instantiating the clause's premises with the bindings the match returns. The operation then verifies
  the constructed instance as an admitted one: the formation of every value bound and of every premise
  call, the membership of each value in its own bindings, and the interfaces' acceptance of the call and
  of every premise call, each a traversal of the values the call carries. Every value the construction
  binds is a subterm of the call and every premise call an instance of formed patterns with those
  values, so once the call is formed only the shape of each pattern remains to be checked: its pairs and
  literal leaves, and equal values at a variable's repeated occurrences, which is the functionality of
  the rows the match returns. The checks below read the patterns, compare values only at repeated
  occurrences of one variable, and return exactly the admitted applications.
\<close>

fun finite_pattern_fits :: "'a finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_pattern_fits (Finite_Variable a) t=True"
| "finite_pattern_fits (Finite_Pattern_Target x) t=(finite_target_formed x \<and> t=Finite_Target x)"
| "finite_pattern_fits (Finite_Pattern_Payload v) t=(octets_formed v \<and> t=Finite_Payload v)"
| "finite_pattern_fits (Finite_Pattern_Pair p q) t=(case t of Finite_Pair x y \<Rightarrow>
    finite_pattern_fits p x \<and> finite_pattern_fits q y | _ \<Rightarrow> False)"

fun finite_matching_rows :: "'a finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> ('a\<times>finite_factor_term) list" where
  "finite_matching_rows (Finite_Variable a) t=[(a,t)]"
| "finite_matching_rows (Finite_Pattern_Target x) t=[]"
| "finite_matching_rows (Finite_Pattern_Payload v) t=[]"
| "finite_matching_rows (Finite_Pattern_Pair p q) t=(case t of Finite_Pair x y \<Rightarrow>
    finite_matching_rows p x@finite_matching_rows q y | _ \<Rightarrow> [])"

lemma finite_matching_rows_bindings:
  "fset_of_list (finite_matching_rows p t)=finite_matching_bindings p t"
  by (induction p arbitrary: t) (simp_all split: finite_factor_term.splits)

definition finite_matching_functional :: "'a finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_matching_functional p t=relation_rows_functional (finite_matching_rows p t)"

lemma finite_matching_functional_exact:
  "finite_matching_functional p t \<longleftrightarrow> finite_relation_functional (finite_matching_bindings p t)"
  by (simp only: finite_matching_functional_def relation_rows_functional_exact finite_relation_functional_correct
    finite_matching_rows_bindings[symmetric] fset_of_list.rep_eq)

section \<open>The shape of a pattern decides its instance under its own match\<close>

lemma finite_pattern_instance_fits:
  "finite_pattern_instance V p t \<Longrightarrow> finite_pattern_fits p t"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_pattern_instance_mono:
  "finite_pattern_instance V p t \<Longrightarrow> V |\<subseteq>| W \<Longrightarrow> finite_pattern_instance W p t"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_pattern_fits_instance:
  "finite_pattern_fits p t \<Longrightarrow> finite_pattern_instance (finite_matching_bindings p t) p t"
proof (induction p arbitrary: t)
  case (Finite_Pattern_Pair p q)
  obtain x y where shape: "t=Finite_Pair x y"
    using Finite_Pattern_Pair.prems by (cases t) simp_all
  have left: "finite_pattern_instance (finite_matching_bindings p x) p x"
    using Finite_Pattern_Pair.IH(1) Finite_Pattern_Pair.prems by (simp add: shape)
  have right: "finite_pattern_instance (finite_matching_bindings q y) q y"
    using Finite_Pattern_Pair.IH(2) Finite_Pattern_Pair.prems by (simp add: shape)
  have left': "finite_pattern_instance (finite_matching_bindings p x |\<union>| finite_matching_bindings q y) p x"
    by (rule finite_pattern_instance_mono[OF left]) simp
  have right': "finite_pattern_instance (finite_matching_bindings p x |\<union>| finite_matching_bindings q y) q y"
    by (rule finite_pattern_instance_mono[OF right]) simp
  show ?case using left' right' by (simp add: shape)
qed simp_all

lemma finite_matching_domain:
  "fimage fst (finite_matching_bindings p t) |\<subseteq>| finite_pattern_variables p"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_matching_fits_domain:
  "finite_pattern_fits p t \<Longrightarrow> fimage fst (finite_matching_bindings p t)=finite_pattern_variables p"
proof (induction p arbitrary: t)
  case (Finite_Pattern_Pair p q)
  obtain x y where shape: "t=Finite_Pair x y"
    using Finite_Pattern_Pair.prems by (cases t) simp_all
  have left: "fimage fst (finite_matching_bindings p x)=finite_pattern_variables p"
    using Finite_Pattern_Pair.IH(1) Finite_Pattern_Pair.prems by (simp add: shape)
  have right: "fimage fst (finite_matching_bindings q y)=finite_pattern_variables q"
    using Finite_Pattern_Pair.IH(2) Finite_Pattern_Pair.prems by (simp add: shape)
  show ?case by (simp add: shape fimage_funion left right)
qed simp_all

lemma finite_matching_formed:
  "finite_term_formed t \<Longrightarrow> (a,x) |\<in>| finite_matching_bindings p t \<Longrightarrow> finite_term_formed x"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_pattern_accepts_fits:
  assumes formed: "finite_term_formed t"
  shows "finite_pattern_accepts p t \<longleftrightarrow> finite_pattern_fits p t \<and> finite_matching_functional p t"
proof
  assume "finite_pattern_accepts p t"
  then have bindings: "finite_term_bindings_formed (finite_pattern_variables p) (finite_matching_bindings p t)"
    and inst: "finite_pattern_instance (finite_matching_bindings p t) p t"
    by (simp_all add: finite_pattern_accepts_def)
  show "finite_pattern_fits p t \<and> finite_matching_functional p t"
    using finite_pattern_instance_fits[OF inst] bindings
    by (simp add: finite_term_bindings_formed_def finite_matching_functional_exact)
next
  assume shape: "finite_pattern_fits p t \<and> finite_matching_functional p t"
  then have fits: "finite_pattern_fits p t" and functional: "finite_matching_functional p t" by simp_all
  have valued: "fBall (finite_matching_bindings p t) (\<lambda>(a,x). finite_term_formed x)"
    using finite_matching_formed[OF formed] by auto
  have bindings: "finite_term_bindings_formed (finite_pattern_variables p) (finite_matching_bindings p t)"
    using functional finite_matching_fits_domain[OF fits] valued
    by (simp add: finite_term_bindings_formed_def finite_matching_functional_exact)
  show "finite_pattern_accepts p t"
    using formed bindings finite_pattern_fits_instance[OF fits] by (simp add: finite_pattern_accepts_def)
qed

lemma finite_pattern_instance_formed:
  "finite_pattern_instance V p x \<Longrightarrow> finite_pattern_formed p \<Longrightarrow>
    fBall V (\<lambda>(a,u). finite_term_formed u) \<Longrightarrow> finite_term_formed x"
  by (induction p arbitrary: x) (auto split: finite_factor_term.splits)

section \<open>A clause's instance at a formed call is its shape\<close>

lemma finite_constructed_instance:
  fixes S :: "('a,'s,'d) finite_factor_schema"
  assumes formed: "finite_term_formed t" and schema: "finite_schema_formed S"
    and covered: "finite_schema_head_missing S={||}"
  shows "finite_schema_instance S (finite_matching_bindings (finite_schema_conclusion S) t) t
      (finite_instantiated_premises S (finite_matching_bindings (finite_schema_conclusion S) t)) \<longleftrightarrow>
    finite_pattern_fits (finite_schema_conclusion S) t \<and> finite_matching_functional (finite_schema_conclusion S) t"
proof -
  let ?p="finite_schema_conclusion S"
  let ?B="finite_matching_bindings ?p t"
  let ?H="finite_instantiated_premises S ?B"
  have scope: "finite_schema_variables S=finite_pattern_variables ?p"
    using covered by (auto simp: finite_schema_head_missing_def finite_schema_variables_def)
  show ?thesis
  proof
    assume "finite_schema_instance S ?B t ?H"
    then have bindings: "finite_term_bindings_formed (finite_schema_variables S) ?B"
      and head: "finite_pattern_instance ?B ?p t"
      by (simp_all add: finite_schema_instance_def)
    show "finite_pattern_fits ?p t \<and> finite_matching_functional ?p t"
      using finite_pattern_instance_fits[OF head] bindings
      by (simp add: finite_term_bindings_formed_def finite_matching_functional_exact)
  next
    assume shape: "finite_pattern_fits ?p t \<and> finite_matching_functional ?p t"
    then have fits: "finite_pattern_fits ?p t" and functional: "finite_matching_functional ?p t" by simp_all
    have valued: "fBall ?B (\<lambda>(a,x). finite_term_formed x)"
      using finite_matching_formed[OF formed] by auto
    have bindings: "finite_term_bindings_formed (finite_schema_variables S) ?B"
      using functional finite_matching_fits_domain[OF fits] valued
      by (simp add: finite_term_bindings_formed_def finite_matching_functional_exact scope)
    have native_bindings: "term_bindings_formed (schema_variables (decode_finite_schema S))
        (decode_finite_term_bindings ?B)"
      using bindings by (simp only: finite_term_bindings_formed_correct finite_schema_variables_correct)
    have native_schema: "schema_formed (decode_finite_schema S)"
      using schema by (simp only: finite_schema_formed_correct)
    obtain u Q where inst: "schema_instance (decode_finite_schema S) (decode_finite_term_bindings ?B) u Q"
      using schema_instance_exists[OF native_schema native_bindings] by blast
    have head_u: "pattern_instance (decode_finite_term_bindings ?B) (decode_finite_pattern ?p) u"
      using inst by (simp add: schema_instance_def decode_finite_schema_def)
    have head_t: "pattern_instance (decode_finite_term_bindings ?B) (decode_finite_pattern ?p) (decode_finite_term t)"
      using finite_pattern_fits_instance[OF fits] by (simp only: finite_pattern_instance_correct)
    have sv: "single_valued (decode_finite_term_bindings ?B)"
      using native_bindings by (simp add: term_bindings_formed_def)
    have same: "u=decode_finite_term t" by (rule pattern_instance_unique[OF sv head_u head_t])
    have inst_t: "schema_instance (decode_finite_schema S) (decode_finite_term_bindings ?B) (decode_finite_term t) Q"
      using inst by (simp only: same)
    show "finite_schema_instance S ?B t ?H"
      using finite_requested_instance_reading(3)[OF inst_t covered] by simp
  qed
qed

lemma finite_requested_constructed:
  assumes formed: "finite_term_formed t"
  shows "finite_requested_schema_applications S t=(let B=finite_matching_bindings (finite_schema_conclusion S) t in
    if finite_schema_formed S \<and> finite_schema_head_missing S={||} \<and>
      finite_pattern_fits (finite_schema_conclusion S) t \<and> finite_matching_functional (finite_schema_conclusion S) t \<and>
      finite_schema_material_satisfied S B
    then {|(t,B,finite_instantiated_premises S B)|} else {||})"
proof (cases "finite_schema_formed S \<and> finite_schema_head_missing S={||}")
  case True
  then have schema: "finite_schema_formed S" and covered: "finite_schema_head_missing S={||}" by simp_all
  show ?thesis
    using finite_constructed_instance[OF formed schema covered] True
    by (simp add: finite_requested_schema_applications_def Let_def)
next
  case False
  let ?p="finite_schema_conclusion S"
  let ?B="finite_matching_bindings ?p t"
  have refused: "\<not>finite_schema_instance S ?B t (finite_instantiated_premises S ?B)"
  proof
    assume inst: "finite_schema_instance S ?B t (finite_instantiated_premises S ?B)"
    have schema: "finite_schema_formed S" using inst by (simp add: finite_schema_instance_def)
    have domain: "fimage fst ?B=finite_schema_variables S"
      using inst by (simp add: finite_schema_instance_def finite_term_bindings_formed_def)
    have "finite_schema_variables S |\<subseteq>| finite_pattern_variables ?p"
      using domain finite_matching_domain[of ?p t] by simp
    then have "finite_schema_head_missing S={||}"
      by (simp add: finite_schema_head_missing_def)
    then show False using False schema by simp
  qed
  show ?thesis using False refused
    by (auto simp: finite_requested_schema_applications_def Let_def)
qed

section \<open>The admitted applications of a formed call\<close>

definition finite_interface_fits ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_interface_fits P d t \<longleftrightarrow> fBex (finite_system_interfaces P)
    (\<lambda>(e,p). e=d \<and> finite_pattern_fits p t \<and> finite_matching_functional p t)"

lemma finite_call_formed_fits:
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
  shows "finite_schema_call_formed P d t \<longleftrightarrow> finite_interface_fits P d t"
  by (simp add: finite_schema_call_formed_def finite_interface_fits_def system finite_pattern_accepts_fits[OF formed])

lemma finite_instantiated_premise_formed:
  assumes schema: "finite_schema_formed S" and valued: "fBall V (\<lambda>(a,u). finite_term_formed u)"
    and member: "(s,e,x) |\<in>| finite_instantiated_premises S V"
  shows "finite_term_formed x"
proof -
  obtain p where premise: "(s,e,p) |\<in>| finite_schema_premises S" and inst: "x |\<in>| finite_pattern_instances V p"
    using member by (auto simp: finite_instantiated_premises_member)
  have pattern: "finite_pattern_formed p" using schema premise by (auto simp: finite_schema_formed_def)
  show ?thesis
    by (rule finite_pattern_instance_formed[OF inst[unfolded finite_pattern_instances_member] pattern valued])
qed

lemma finite_admitted_constructed:
  fixes S :: "('a,'s,'d) finite_factor_schema"
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and instantiated: "finite_schema_instance S B t H" and material: "finite_schema_material_satisfied S B"
  shows "finite_admitted_schema_instance P d c B t H \<longleftrightarrow>
    finite_interface_fits P d t \<and> fBall H (\<lambda>(s,e,x). finite_interface_fits P e x)"
proof -
  have schema: "finite_schema_formed S" using instantiated by (simp add: finite_schema_instance_def)
  have valued: "fBall B (\<lambda>(a,u). finite_term_formed u)"
    using instantiated by (simp add: finite_schema_instance_def finite_term_bindings_formed_def)
  have body: "finite_instantiated_premises S B=H" by (rule finite_instantiated_premises_exact[OF instantiated])
  have clause_holds: "fBex (finite_system_clauses P) (\<lambda>((e,k),S'). e=d \<and> k=c \<and>
      finite_schema_instance S' B t H \<and> finite_schema_material_satisfied S' B)"
    using clause instantiated material by blast
  have premise_calls: "fBall H (\<lambda>(s,e,x). finite_schema_call_formed P e x) \<longleftrightarrow>
      fBall H (\<lambda>(s,e,x). finite_interface_fits P e x)"
  proof (rule fBall_cong[OF refl])
    fix z assume member: "z |\<in>| H"
    obtain s e x where shape: "z=(s,e,x)" using prod_cases3 by blast
    have "(s,e,x) |\<in>| finite_instantiated_premises S B" using member by (simp add: shape body)
    then have "finite_term_formed x" by (rule finite_instantiated_premise_formed[OF schema valued])
    then show "(\<lambda>(s,e,x). finite_schema_call_formed P e x) z=(\<lambda>(s,e,x). finite_interface_fits P e x) z"
      by (simp add: shape finite_call_formed_fits[OF system])
  qed
  show ?thesis
    using clause_holds premise_calls finite_call_formed_fits[OF system formed]
    by (simp add: finite_admitted_schema_instance_def)
qed


definition finite_constructed_requests ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> finite_factor_term \<Rightarrow>
      (finite_factor_term\<times>('a\<times>finite_factor_term) fset\<times>('s\<times>('d\<times>finite_factor_term)) fset) fset" where
  "finite_constructed_requests P d S t=(let B=finite_matching_bindings (finite_schema_conclusion S) t;
     H=finite_instantiated_premises S B in
     if finite_schema_formed S \<and> finite_schema_head_missing S={||} \<and>
       finite_pattern_fits (finite_schema_conclusion S) t \<and> finite_matching_functional (finite_schema_conclusion S) t \<and>
       finite_schema_material_satisfied S B \<and>
       finite_interface_fits P d t \<and> fBall H (\<lambda>(s,e,x). finite_interface_fits P e x)
     then {|(t,B,H)|} else {||})"

lemma finite_constructed_requests_exact:
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "ffilter (\<lambda>(x,V,H). finite_admitted_schema_instance P d c V x H) (finite_requested_schema_applications S t)=
    finite_constructed_requests P d S t"
proof -
  let ?p="finite_schema_conclusion S"
  let ?B="finite_matching_bindings ?p t"
  let ?H="finite_instantiated_premises S ?B"
  show ?thesis
  proof (cases "finite_schema_formed S \<and> finite_schema_head_missing S={||} \<and> finite_pattern_fits ?p t \<and>
      finite_matching_functional ?p t \<and> finite_schema_material_satisfied S ?B")
    case True
    then have schema: "finite_schema_formed S" and covered: "finite_schema_head_missing S={||}"
      and shape: "finite_pattern_fits ?p t \<and> finite_matching_functional ?p t"
      and material: "finite_schema_material_satisfied S ?B" by simp_all
    have instantiated: "finite_schema_instance S ?B t ?H"
      using finite_constructed_instance[OF formed schema covered] shape by simp
    have admitted: "finite_admitted_schema_instance P d c ?B t ?H \<longleftrightarrow>
        finite_interface_fits P d t \<and> fBall ?H (\<lambda>(s,e,x). finite_interface_fits P e x)"
      by (rule finite_admitted_constructed[OF system formed clause instantiated material])
    show ?thesis using True admitted
      by (simp add: finite_requested_constructed[OF formed] finite_constructed_requests_def Let_def
        Candidate_Generators.accepted_singleton)
  next
    case False
    have requested: "finite_requested_schema_applications S t={||}"
      using False by (auto simp: finite_requested_constructed[OF formed] Let_def)
    have constructed: "finite_constructed_requests P d S t={||}"
      using False by (auto simp: finite_constructed_requests_def Let_def)
    show ?thesis by (simp add: requested constructed fset_eq_iff)
  qed
qed

definition finite_constructed_applications ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('d\<times>'c\<times>finite_factor_term\<times>('a\<times>finite_factor_term) fset\<times>('s\<times>('d\<times>finite_factor_term)) fset) fset" where
  "finite_constructed_applications P d t=ffUnion (fimage (\<lambda>((e,c),S). if e=d then
    fimage (\<lambda>(x,V,H). (d,c,x,V,H)) (finite_constructed_requests P d S t) else {||}) (finite_system_clauses P))"

theorem finite_constructed_applications_exact:
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
  shows "finite_program_applications P {|(d,t)|}=finite_constructed_applications P d t"
proof -
  have "finite_program_applications P {|(d,t)|}=ffUnion (fimage (\<lambda>((e,c),S). if e=d then
      fimage (\<lambda>(x,V,H). (d,c,x,V,H))
        (ffilter (\<lambda>(x,V,H). finite_admitted_schema_instance P d c V x H)
          (finite_requested_schema_applications S t)) else {||}) (finite_system_clauses P))"
    by (simp add: finite_program_applications_def)
  also have "\<dots>=finite_constructed_applications P d t"
    unfolding finite_constructed_applications_def
  proof (rule arg_cong[where f=ffUnion], rule fimage_cong[OF refl])
    fix z assume member: "z |\<in>| finite_system_clauses P"
    obtain e c S where shape: "z=((e,c),S)" by (metis prod.collapse)
    show "(\<lambda>((e,c),S). if e=d then fimage (\<lambda>(x,V,H). (d,c,x,V,H))
          (ffilter (\<lambda>(x,V,H). finite_admitted_schema_instance P d c V x H)
            (finite_requested_schema_applications S t)) else {||}) z=
        (\<lambda>((e,c),S). if e=d then fimage (\<lambda>(x,V,H). (d,c,x,V,H)) (finite_constructed_requests P d S t)
          else {||}) z"
    proof (cases "e=d")
      case True
      have clause: "((d,c),S) |\<in>| finite_system_clauses P" using member by (simp add: shape True)
      show ?thesis by (simp add: shape True finite_constructed_requests_exact[OF system formed clause])
    next
      case False
      then show ?thesis by (simp add: shape)
    qed
  qed
  finally show ?thesis .
qed

section \<open>The applications of a demand are listed call by call\<close>

lemma finite_program_applications_unformed:
  assumes unformed: "\<not>finite_term_formed t"
  shows "finite_program_applications P {|(d,t)|}={||}"
proof -
  have none: "z |\<notin>| finite_program_applications P {|(d,t)|}" for z
  proof -
    obtain d' c t' V H where shape: "z=(d',c,t',V,H)" using prod_cases5 by blast
    have "\<not>finite_admitted_schema_instance P d' c V t H" for d' c V H
      using unformed by (auto simp: finite_admitted_schema_instance_def finite_schema_call_formed_def
        finite_pattern_accepts_def)
    then show ?thesis by (auto simp: shape finite_program_application_member)
  qed
  show ?thesis using none by (simp add: fset_eq_iff)
qed

lemma finite_program_applications_unformed_system:
  assumes unformed: "\<not>finite_system_formed P"
  shows "finite_program_applications P D={||}"
proof -
  have none: "z |\<notin>| finite_program_applications P D" for z
  proof -
    obtain d c t V H where shape: "z=(d,c,t,V,H)" using prod_cases5 by blast
    have "\<not>finite_admitted_schema_instance P d c V t H"
      using unformed by (auto simp: finite_admitted_schema_instance_def finite_schema_call_formed_def)
    then show ?thesis by (auto simp: shape finite_program_application_member)
  qed
  show ?thesis using none by (simp add: fset_eq_iff)
qed

lemma finite_program_applications_calls:
  "fset (finite_program_applications P D)=(\<Union>q\<in>fset D. fset (finite_program_applications P {|q|}))"
  by (auto simp: finite_program_applications_def ffUnion.rep_eq fimage.rep_eq)

lemma finite_program_applications_listed [code abstract]:
  "fset (finite_program_applications P D)=(if finite_system_formed P then listed_image_union
    (\<lambda>q. if finite_term_formed (snd q) then fset (finite_constructed_applications P (fst q) (snd q)) else {})
    (fset D) else {})"
proof -
  have entry: "checked_premise (\<lambda>P D. fset (finite_program_applications P D)) finite_system_formed
      (\<lambda>P D. listed_image_union (\<lambda>q. if finite_term_formed (snd q) then
        fset (finite_constructed_applications P (fst q) (snd q)) else {}) (fset D)) (\<lambda>P D. {})"
  proof (unfold_locales)
    fix P assume True: "finite_system_formed P"
    have calls: "checked_premise (\<lambda>q. fset (finite_program_applications P {|q|})) (\<lambda>q. finite_term_formed (snd q))
        (\<lambda>q. fset (finite_constructed_applications P (fst q) (snd q))) (\<lambda>q. {})"
    proof (unfold_locales, goal_cases)
      case (1 q)
      obtain d t where q: "q=(d,t)" by (cases q) auto
      show ?case using 1 by (simp add: q finite_constructed_applications_exact[OF True])
    next
      case (2 q)
      obtain d t where q: "q=(d,t)" by (cases q) auto
      show ?case using 2 by (simp add: q finite_program_applications_unformed)
    qed
    have call: "fset (finite_program_applications P {|q|})=(if finite_term_formed (snd q) then
        fset (finite_constructed_applications P (fst q) (snd q)) else {})" for q
      by (rule checked_premise.checked_at_entry[OF calls])
    have "fset (finite_program_applications P D)=listed_image_union (\<lambda>q. if finite_term_formed (snd q) then
        fset (finite_constructed_applications P (fst q) (snd q)) else {}) (fset D)" for D
    proof -
      have "fset (finite_program_applications P D)=(\<Union>q\<in>fset D. fset (finite_program_applications P {|q|}))"
        by (rule finite_program_applications_calls)
      also have "\<dots>=(\<Union>q\<in>fset D. if finite_term_formed (snd q) then
          fset (finite_constructed_applications P (fst q) (snd q)) else {})"
        by (simp only: call)
      also have "\<dots>=listed_image_union (\<lambda>q. if finite_term_formed (snd q) then
          fset (finite_constructed_applications P (fst q) (snd q)) else {}) (fset D)"
        by (simp only: listed_image_union_def)
      finally show ?thesis .
    qed
    then show "(\<lambda>D. fset (finite_program_applications P D))=(\<lambda>D. listed_image_union (\<lambda>q.
        if finite_term_formed (snd q) then fset (finite_constructed_applications P (fst q) (snd q)) else {})
        (fset D))" by (rule ext)
  next
    fix P assume "\<not> finite_system_formed P"
    then show "(\<lambda>D. fset (finite_program_applications P D))=(\<lambda>D. {})"
      by (simp add: finite_program_applications_unformed_system)
  qed
  show ?thesis by (rule checked_premise.checked_through[OF entry, where t="\<lambda>f. f D"])
qed

text \<open>
  An evaluation checks in every round that a rule's premises are functional. That is the functionality
  of a relation, whose execution compares a row only with the rows after it, so two premises at distinct
  sockets are never compared by their calls and no premise is compared with itself.
\<close>

lemma finite_premise_functional_rows [code]:
  "finite_premise_functional H=finite_relation_functional H"
  by (simp add: finite_premise_functional_def finite_relation_functional_def case_prod_unfold)

end
