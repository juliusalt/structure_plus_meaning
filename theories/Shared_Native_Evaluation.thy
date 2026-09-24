theory Shared_Native_Evaluation
  imports Positioned_Native_Evaluation
begin

section \<open>A demand is settled over the shared subterms of its requests\<close>

text \<open>
  DECISIONS.md, "An evaluation's calls are built over the shared subterms of its requests", B5. The
  positioned evaluation renames every call of its demand's rule table to the call's position, and
  finding a position compares the call with the demand's calls through the call key: whole terms,
  walked to their end by every comparison that ends equal, as every lookup of a demanded premise does.
  Over the table of the requests' shared subterms (@{text Shared_Call_Closures}) the demand is canonical
  shared calls, the rule table's premise calls are built by the canonical constructors
  (@{text Presented_Program_Applications}) and the positions are keyed by the shared call, so what a
  premise shares with its demanded call is one reference. The rounds are the positioned evaluation's,
  and the answers are decoded once, where they leave. Its result is the original evaluation
  (@{text presented_program_evaluation_exact}).
\<close>

subsection \<open>A traversal stays within a set its successors keep\<close>

lemma finite_demanded_sites_within:
  assumes roots: "fset roots\<subseteq>Q"
    and closed: "\<And>q x e. q\<in>Q \<Longrightarrow> x |\<in>| read q \<Longrightarrow> e |\<in>| succ x \<Longrightarrow> e\<in>Q"
    and sites: "finite_demanded_sites read succ roots=Some C"
  shows "fset C\<subseteq>Q"
proof -
  obtain T where run: "while_option (\<lambda>(S,T). T\<noteq>{||}) (finite_demanded_sites_step read succ) ({||},roots)=Some (C,T)"
    using sites by (auto simp: finite_demanded_sites_def)
  have "(\<lambda>(S,T). fset S\<subseteq>Q \<and> fset T\<subseteq>Q) (C,T)"
  proof (rule while_option_rule[OF _ run])
    fix s assume inv: "(\<lambda>(S,T). fset S\<subseteq>Q \<and> fset T\<subseteq>Q) s"
    obtain S T where s: "s=(S,T)" by (cases s)
    have "fset (finite_row_successors read succ T)\<subseteq>Q"
      using inv closed by (auto simp: s finite_row_successors_union ffUnion.rep_eq fimage.rep_eq)
    then show "(\<lambda>(S,T). fset S\<subseteq>Q \<and> fset T\<subseteq>Q) (finite_demanded_sites_step read succ s)"
      using inv by (auto simp: s finite_demanded_sites_step_def Let_def)
  next
    show "(\<lambda>(S,T). fset S\<subseteq>Q \<and> fset T\<subseteq>Q) ({||},roots)" using roots by simp
  qed
  then show ?thesis by simp
qed


lemma finite_embedded_inferences_comp:
  "finite_embedded_inferences g (finite_embedded_inferences f F)=finite_embedded_inferences (g \<circ> f) F"
  by (simp add: finite_embedded_inferences_def fset.map_comp comp_def split_def)

lemma fBall_member: "fBall A P \<longleftrightarrow> (\<forall>x. x |\<in>| A \<longrightarrow> P x)"
  by (auto intro: fBallI dest: fbspec)

lemma fBall_image: "fBall (fimage f A) P \<longleftrightarrow> fBall A (\<lambda>x. P (f x))"
  by (auto simp: fBall_member fimage.rep_eq)

subsection \<open>The rules and the settled answers of a presented demand\<close>

definition presented_rule_table ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> ('d\<times>'p) fset \<Rightarrow>
      (('d\<times>'p)\<times>('s\<times>('d\<times>'p)) fset) fset" where
  "presented_rule_table S Q C=ffUnion (fimage (\<lambda>q. fimage finite_program_application_rule
    (presented_constructed_applications S Q (fst q) (snd q))) C)"

definition presented_settled_answers ::
    "'p term_presentation \<Rightarrow> ('d::linorder\<times>'p::linorder,nat) rbt \<Rightarrow> (('d\<times>'p)\<times>('s\<times>('d\<times>'p)) fset) fset \<Rightarrow>
      ('d\<times>'p) fset \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "presented_settled_answers S N F C=map_option (\<lambda>A. let U=ordered_member_tree A in
    fimage (map_prod id (presented_decode S)) (ffilter (\<lambda>q. RBT.lookup U (positioned_call id N q)\<noteq>None) C))
    (keyed_inference_settled id id (finite_embedded_inferences (positioned_call id N) F) {||})"

definition presented_program_evaluation ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('d::linorder\<times>'p::linorder) fset \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "presented_program_evaluation S Q P C=(let N=demand_positions id C; F=presented_rule_table S Q C in
    if finite_program_head_covered P C \<and> fBall F (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup N r\<noteq>None))
    then presented_settled_answers S N F C else None)"

text \<open>
  Where the demand is closed under the premise calls of its applications, every premise of the rule table
  has its position, and the evaluation asks only for the heads' scope: a check made where its premise is
  established (@{text Established_Premises}), the premise being the closure's.
\<close>

definition presented_closed_evaluation ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('d::linorder\<times>'p::linorder) fset \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "presented_closed_evaluation S Q P C=(if finite_program_head_covered P C
    then presented_settled_answers S (demand_positions id C) (presented_rule_table S Q C) C else None)"

subsection \<open>Over a formed table, the presented evaluation is the original one\<close>

context
  fixes T :: "shape list"
  assumes formed: "table_formed T"
begin

lemma table_decode_form: "presented_decode (table_presentation T) (shared_form (table_find T) t)=t"
  using shared_form_exact[OF formed, of t] by (simp add: table_presentation_def)

lemma table_form_decode:
  assumes canonical: "shared_canonical T s"
  shows "shared_form (table_find T) (presented_decode (table_presentation T) s)=s"
proof -
  obtain t where decoded: "shared_decode T s=Some t" using canonical_decodes[OF formed canonical] by blast
  then have "presented_decode (table_presentation T) s=t" by (simp add: table_presentation_def)
  then show ?thesis using shared_form_canonical[OF formed canonical decoded] by simp
qed

text \<open>
  The rules of a presented demand of canonical calls are the program's rules at the decoded demand,
  carried by the canonical form: every presented application decodes to an application of the program
  (@{text presented_constructed_applications_decode}), and the canonical form returns each of
  its canonical calls.
\<close>

theorem presented_rule_table_embedded:
  fixes P :: "('a,'s,'d,'c) finite_schema_system" and C :: "('d\<times>shared_term) fset"
  assumes system: "finite_system_formed P"
    and calls: "\<And>q. q |\<in>| C \<Longrightarrow>
      shared_canonical T (snd q) \<and> finite_term_formed (presented_decode (table_presentation T) (snd q))"
  shows "presented_rule_table (table_presentation T) (prepare_program (table_presentation T) P) C=
    finite_embedded_inferences (map_prod id (shared_form (table_find T)))
      (finite_program_rule_table P (fimage (map_prod id (presented_decode (table_presentation T))) C))"
proof -
  interpret shared: presented_terms "table_presentation T" "{s. shared_canonical T s}"
    unfolding table_presentation_def by (rule shared_presentation_terms[OF formed])
  let ?S="table_presentation T"
  let ?Q="prepare_program ?S P"
  let ?h="map_prod (id::'d\<Rightarrow>'d) (presented_decode ?S)"
  let ?f="map_prod (id::'d\<Rightarrow>'d) (shared_form (table_find T))"
  let ?apps="\<lambda>q::'d\<times>shared_term. presented_constructed_applications ?S ?Q (fst q) (snd q)"
  have plain: "finite_program_applications P {|?h q|}=fimage (presented_application_decode ?S) (?apps q)"
    if q: "q |\<in>| C" for q
  proof -
    obtain d t where qs: "q=(d,t)" by (cases q)
    have t: "t\<in>{s. shared_canonical T s}" and tf: "finite_term_formed (presented_decode ?S t)"
      using calls[OF q] by (simp_all add: qs)
    have "finite_program_applications P {|(d,presented_decode ?S t)|}=
        finite_constructed_applications P d (presented_decode ?S t)"
      by (rule finite_constructed_applications_exact[OF system tf])
    also have "\<dots>=fimage (presented_application_decode ?S) (presented_constructed_applications ?S ?Q d t)"
      by (rule shared.presented_constructed_applications_decode[OF t, symmetric])
    finally show ?thesis by (simp add: qs)
  qed
  have per_call: "fimage (\<lambda>(a,H). (?f a,fimage (\<lambda>(i,b). (i,?f b)) H))
      (fimage (\<lambda>x. finite_program_application_rule (presented_application_decode ?S x)) (?apps q))=
    fimage finite_program_application_rule (?apps q)" if q: "q |\<in>| C" for q
  proof -
    obtain d t where qs: "q=(d,t)" by (cases q)
    have t: "t\<in>{s. shared_canonical T s}" using calls[OF q] by (simp add: qs)
    show ?thesis unfolding fset.map_comp
    proof (rule fset.map_cong0)
      fix x assume x: "x\<in>fset (?apps q)"
      obtain e c y V H where xs: "x=(e,c,y,V,H)" using prod_cases5 by blast
      have member: "(e,c,y,V,H) |\<in>| presented_constructed_applications ?S ?Q d t" using x by (simp add: qs xs)
      have domain: "e=d \<and> y=t \<and> (\<forall>s e' z. (s,e',z) |\<in>| H \<longrightarrow> z\<in>{s. shared_canonical T s})"
        using shared.presented_constructed_application_domain[OF t member] by blast
      have mapped: "fimage (\<lambda>(i,b). (i,?f b)) (fimage (\<lambda>(s,e,z). (s,e,presented_decode ?S z)) H)=H"
      proof -
        have "fimage (\<lambda>(i,b). (i,?f b)) (fimage (\<lambda>(s,e,z). (s,e,presented_decode ?S z)) H)=fimage id H"
          unfolding fset.map_comp
        proof (rule fset.map_cong0)
          fix z assume z: "z\<in>fset H"
          obtain s e' w where zs: "z=(s,e',w)" using prod_cases3 by blast
          have "shared_canonical T w" using domain z by (auto simp: zs)
          then show "((\<lambda>(i,b). (i,?f b)) \<circ> (\<lambda>(s,e,z). (s,e,presented_decode ?S z))) z=id z"
            by (simp add: zs table_form_decode)
        qed
        then show ?thesis by simp
      qed
      show "((\<lambda>(a,H). (?f a,fimage (\<lambda>(i,b). (i,?f b)) H)) \<circ>
          (\<lambda>x. finite_program_application_rule (presented_application_decode ?S x))) x=
        finite_program_application_rule x"
        using domain t mapped
        by (simp add: xs presented_application_decode_def presented_request_decode_def table_form_decode)
    qed
  qed
  have applications: "finite_program_applications P (fimage ?h C)=
      ffUnion (fimage (\<lambda>q. fimage (presented_application_decode ?S) (?apps q)) C)"
  proof -
    have "fset (finite_program_applications P (fimage ?h C))=(\<Union>q\<in>fset C. fset (finite_program_applications P {|?h q|}))"
      by (subst finite_program_applications_calls) (simp add: fimage.rep_eq)
    also have "\<dots>=(\<Union>q\<in>fset C. fset (fimage (presented_application_decode ?S) (?apps q)))"
      by (rule SUP_cong) (simp_all add: plain)
    also have "\<dots>=fset (ffUnion (fimage (\<lambda>q. fimage (presented_application_decode ?S) (?apps q)) C))"
      by (simp add: ffUnion.rep_eq fimage.rep_eq)
    finally show ?thesis by (simp only: fset_inject)
  qed
  have "fimage (\<lambda>q. fimage (\<lambda>(a,H). (?f a,fimage (\<lambda>(i,b). (i,?f b)) H))
      (fimage (\<lambda>x. finite_program_application_rule (presented_application_decode ?S x)) (?apps q))) C=
    fimage (\<lambda>q. fimage finite_program_application_rule (?apps q)) C"
    by (rule fset.map_cong0) (simp only: per_call)
  then show ?thesis
    by (simp add: presented_rule_table_def finite_program_rule_table_def applications finite_embedded_inferences_def
      fimage_ffUnion_member fset.map_comp comp_def)
qed

text \<open>
  The presented evaluation is the positioned evaluation at the canonical form as the key, whose left
  inverse is the decoding (@{text table_decode_form}): the image of the decoded demand under the key is the
  demand, so its positions, its renamed rules, its guards and its answers are the positioned evaluation's at
  the decoded demand. Its exactness is then the positioned evaluation's
  (@{thm [source] positioned_program_evaluation_exact}), consumed and not argued again.
\<close>

lemma ffilter_fimage: "ffilter P (fimage f A)=fimage f (ffilter (\<lambda>x. P (f x)) A)"
  by (rule fset_eqI) (auto simp: fimage.rep_eq)

theorem presented_program_evaluation_positioned:
  fixes P :: "('a,'s,'d::linorder,'c) finite_schema_system" and C :: "('d\<times>shared_term) fset"
  assumes system: "finite_system_formed P"
    and calls: "\<And>q. q |\<in>| C \<Longrightarrow>
      shared_canonical T (snd q) \<and> finite_term_formed (presented_decode (table_presentation T) (snd q))"
  shows "presented_program_evaluation (table_presentation T) (prepare_program (table_presentation T) P) P C=
    positioned_program_evaluation (map_prod id (shared_form (table_find T))) P
      (fimage (map_prod id (presented_decode (table_presentation T))) C)"
proof -
  let ?S="table_presentation T"
  let ?h="map_prod (id::'d\<Rightarrow>'d) (presented_decode ?S)"
  let ?f="map_prod (id::'d\<Rightarrow>'d) (shared_form (table_find T))"
  let ?D="fimage ?h C"
  let ?F="finite_program_rule_table P ?D"
  let ?N="demand_positions id C"
  have hf: "?h (?f b)=b" for b by (cases b) (simp add: table_decode_form)
  have fh: "?f (?h q)=q" if "q |\<in>| C" for q using calls[OF that] by (cases q) (simp add: table_form_decode)
  have restore: "fimage ?h (fimage ?f Y)=Y" for Y
  proof -
    have "fimage ?h (fimage ?f Y)=fimage id Y"
      unfolding fset.map_comp by (rule fset.map_cong0) (simp only: comp_apply hf id_apply)
    then show ?thesis by simp
  qed
  have Cf: "fimage ?f ?D=C"
  proof -
    have "fimage ?f ?D=fimage id C"
      unfolding fset.map_comp by (rule fset.map_cong0) (simp only: comp_apply fh id_apply)
    then show ?thesis by simp
  qed
  have rules: "presented_rule_table ?S (prepare_program ?S P) C=finite_embedded_inferences ?f ?F"
    by (rule presented_rule_table_embedded[OF system calls])
  have covered: "finite_program_head_covered P C \<longleftrightarrow> finite_program_head_covered P ?D"
    by (simp add: finite_program_head_covered_def fset.map_comp comp_def)
  have positions: "demand_positions ?f ?D=?N" unfolding demand_positions_def by (simp only: Cf fset.map_id)
  have calls_f: "positioned_call ?f ?N=positioned_call id ?N \<circ> ?f" by (rule ext) (simp add: positioned_call_def)
  have renamed: "finite_embedded_inferences (positioned_call id ?N) (presented_rule_table ?S (prepare_program ?S P) C)=
      finite_embedded_inferences (positioned_call ?f ?N) ?F"
    by (simp only: rules finite_embedded_inferences_comp calls_f)
  have guard: "fBall (presented_rule_table ?S (prepare_program ?S P) C)
        (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup ?N r\<noteq>None)) \<longleftrightarrow>
      fBall ?F (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup ?N (?f r)\<noteq>None))"
    unfolding rules finite_embedded_inferences_def fBall_image
    by (rule fBall_cong[OF refl], case_tac x, simp add: fBall_image split_def)
  have selected: "fimage ?h (ffilter (\<lambda>q. RBT.lookup U (positioned_call id ?N q)\<noteq>None) C)=
      ffilter (\<lambda>q. RBT.lookup U (positioned_call ?f ?N q)\<noteq>None) ?D" for U
  proof -
    have "ffilter (\<lambda>q. RBT.lookup U (positioned_call id ?N q)\<noteq>None) C=
        ffilter (\<lambda>q. RBT.lookup U (positioned_call id ?N q)\<noteq>None) (fimage ?f ?D)" by (simp only: Cf)
    also have "\<dots>=fimage ?f (ffilter (\<lambda>q. RBT.lookup U (positioned_call ?f ?N q)\<noteq>None) ?D)"
      by (simp only: ffilter_fimage calls_f comp_apply)
    finally show ?thesis by (simp only: restore)
  qed
  show ?thesis
    unfolding presented_program_evaluation_def positioned_program_evaluation_def presented_settled_answers_def Let_def
    by (simp only: positions renamed guard covered selected system simp_thms)
qed

theorem presented_program_evaluation_exact:
  fixes P :: "('a,'s,'d::linorder,'c) finite_schema_system" and C :: "('d\<times>shared_term) fset"
  assumes system: "finite_system_formed P"
    and calls: "\<And>q. q |\<in>| C \<Longrightarrow>
      shared_canonical T (snd q) \<and> finite_term_formed (presented_decode (table_presentation T) (snd q))"
  shows "presented_program_evaluation (table_presentation T) (prepare_program (table_presentation T) P) P C=
    finite_program_evaluation P (fimage (map_prod id (presented_decode (table_presentation T))) C)"
proof -
  have hf: "map_prod (id::'d\<Rightarrow>'d) (presented_decode (table_presentation T)) (map_prod id (shared_form (table_find T)) b)=b"
    for b by (cases b) (simp add: table_decode_form)
  have "presented_program_evaluation (table_presentation T) (prepare_program (table_presentation T) P) P C=
      positioned_program_evaluation (map_prod id (shared_form (table_find T))) P
        (fimage (map_prod id (presented_decode (table_presentation T))) C)"
    by (rule presented_program_evaluation_positioned[where P=P and C=C, OF system calls])
  also have "\<dots>=finite_program_evaluation P (fimage (map_prod id (presented_decode (table_presentation T))) C)"
    by (rule positioned_program_evaluation_exact) (rule hf)
  finally show ?thesis .
qed

theorem presented_closed_evaluation_exact:
  fixes P :: "('a,'s,'d::linorder,'c) finite_schema_system" and C :: "('d\<times>shared_term) fset"
  assumes system: "finite_system_formed P"
    and calls: "\<And>q. q |\<in>| C \<Longrightarrow>
      shared_canonical T (snd q) \<and> finite_term_formed (presented_decode (table_presentation T) (snd q))"
    and closed: "\<And>q x e. q |\<in>| C \<Longrightarrow>
      x |\<in>| presented_constructed_applications (table_presentation T) (prepare_program (table_presentation T) P)
        (fst q) (snd q) \<Longrightarrow> e |\<in>| finite_application_premise_calls x \<Longrightarrow> e |\<in>| C"
  shows "presented_closed_evaluation (table_presentation T) (prepare_program (table_presentation T) P) P C=
    finite_program_evaluation P (fimage (map_prod id (presented_decode (table_presentation T))) C)"
proof -
  let ?S="table_presentation T"
  have premise: "RBT.lookup (demand_positions id C) r\<noteq>None"
    if rule: "(q',H) |\<in>| presented_rule_table ?S (prepare_program ?S P) C" and r: "r |\<in>| fimage snd H" for q' H r
  proof -
    from rule obtain q x where q: "q |\<in>| C"
        and x: "x |\<in>| presented_constructed_applications ?S (prepare_program ?S P) (fst q) (snd q)"
        and xr: "finite_program_application_rule x=(q',H)"
      unfolding presented_rule_table_def by (auto simp: ffUnion.rep_eq fimage.rep_eq)
    obtain d c t V G where xs: "x=(d,c,t,V,G)" using prod_cases5 by blast
    have "r |\<in>| finite_application_premise_calls x" using xr r by (simp add: xs finite_application_premise_calls_def)
    then have "r |\<in>| C" by (rule closed[OF q x])
    then show ?thesis using demand_positions_member[of id C r] by simp
  qed
  have positioned: "fBall (presented_rule_table ?S (prepare_program ?S P) C)
      (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup (demand_positions id C) r\<noteq>None))"
  proof (rule fBallI)
    fix p assume p: "p |\<in>| presented_rule_table ?S (prepare_program ?S P) C"
    obtain q' H where ps: "p=(q',H)" by (cases p)
    have "fBall (fimage snd H) (\<lambda>r. RBT.lookup (demand_positions id C) r\<noteq>None)"
      by (rule fBallI) (rule premise[OF p[unfolded ps]])
    then show "(\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup (demand_positions id C) r\<noteq>None)) p"
      by (simp only: ps prod.case)
  qed
  have "presented_closed_evaluation ?S (prepare_program ?S P) P C=
      presented_program_evaluation ?S (prepare_program ?S P) P C"
    using positioned unfolding presented_closed_evaluation_def presented_program_evaluation_def Let_def by simp
  also have "\<dots>=finite_program_evaluation P (fimage (map_prod id (presented_decode ?S)) C)"
    by (rule presented_program_evaluation_exact[where P=P and C=C, OF system calls])
  finally show ?thesis .
qed

end

section \<open>The generation, the reference and the evidence evaluate over shared calls\<close>

text \<open>
  A plain demand is evaluated over the table of its own calls' terms, built once where it is evaluated.
\<close>

definition shared_program_evaluation ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset option" where
  "shared_program_evaluation P D=(case shared_request_table D of (C,T,S) \<Rightarrow>
    presented_program_evaluation S (prepare_program S P) P C)"

theorem shared_program_evaluation_exact:
  assumes system: "finite_system_formed P" and demand: "fBall D (\<lambda>q. finite_term_formed (snd q))"
  shows "shared_program_evaluation P D=finite_program_evaluation P D"
proof -
  obtain C T S where table: "shared_request_table D=(C,T,S)" using prod_cases3 by blast
  note fields=shared_request_table_exact[OF table]
  let ?S="table_presentation T"
  have decoded: "fimage (map_prod id (presented_decode ?S)) C=D" using fields(2,4) by simp
  have calls: "shared_canonical T (snd q) \<and> finite_term_formed (presented_decode ?S (snd q))" if q: "q |\<in>| C" for q
  proof -
    have "map_prod id (presented_decode ?S) q |\<in>| fimage (map_prod id (presented_decode ?S)) C" using q by (rule fimageI)
    then have "map_prod id (presented_decode ?S) q |\<in>| D" by (simp only: decoded)
    then have "finite_term_formed (snd (map_prod id (presented_decode ?S) q))" by (rule fbspec[OF demand])
    then show ?thesis using fields(3) q by auto
  qed
  have "shared_program_evaluation P D=presented_program_evaluation ?S (prepare_program ?S P) P C"
    by (simp add: shared_program_evaluation_def table fields(2))
  also have "\<dots>=finite_program_evaluation P (fimage (map_prod id (presented_decode ?S)) C)"
    by (rule presented_program_evaluation_exact[where T=T and P=P and C=C, OF fields(1) system calls])
  finally show ?thesis by (simp only: decoded)
qed

text \<open>
  The demand of a stage's requests is their closure (@{text Shared_Call_Closures}); computed over the table
  of the requests, it is evaluated there, without decoding between: the closure's traversal returns the
  shared demand, closed under the premise calls of its applications, and the answers are decoded once.
\<close>

definition shared_call_evaluation ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "shared_call_evaluation P R=(case shared_request_table R of (C,T,S) \<Rightarrow> let Q=prepare_program S P in
    case keyed_demanded_sites id id (\<lambda>q. presented_constructed_applications S Q (fst q) (snd q))
      finite_application_premise_calls C of None \<Rightarrow> (R,finite_program_evaluation P R)
    | Some D \<Rightarrow> (fimage (map_prod id (presented_decode S)) D,presented_closed_evaluation S Q P D))"

definition native_call_evaluation ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_call_evaluation P R=(let D=native_call_closure P R in (D,finite_program_evaluation P D))"

theorem shared_call_evaluation_exact:
  assumes system: "finite_system_formed P" and requests: "fBall R (\<lambda>q. finite_term_formed (snd q))"
  shows "shared_call_evaluation P R=native_call_evaluation P R"
proof -
  obtain roots T S where table: "shared_request_table R=(roots,T,S)" using prod_cases3 by blast
  note fields=shared_request_table_exact[OF table]
  have tableT: "shared_request_table R=(roots,T,table_presentation T)" using table fields(2) by simp
  let ?S="table_presentation T"
  interpret shared: presented_terms ?S "{s. shared_canonical T s}"
    unfolding table_presentation_def by (rule shared_presentation_terms[OF fields(1)])
  define h where "h=map_prod (id::local_address option definition_site \<Rightarrow> _) (presented_decode ?S)"
  define readS where "readS=(\<lambda>q::local_address option definition_site\<times>shared_term.
    presented_constructed_applications ?S (prepare_program ?S P) (fst q) (snd q))"
  define U where "U={q::local_address option definition_site\<times>shared_term.
    shared_canonical T (snd q) \<and> finite_term_formed (presented_decode ?S (snd q))}"
  have image: "fimage h roots=R" using fields(2,4) by (simp add: h_def)
  have closure: "native_call_closure P R=(case finite_demanded_sites readS finite_application_premise_calls roots of
      None \<Rightarrow> R | Some D \<Rightarrow> fimage h D)"
  proof -
    have "native_call_closure P R=shared_call_closure P R"
      by (simp only: native_call_closure_def keyed_call_closure_formed[OF system requests] shared_call_closure_formed)
    also have "\<dots>=(case finite_demanded_sites readS finite_application_premise_calls roots of None \<Rightarrow> R | Some D \<Rightarrow> fimage h D)"
      unfolding h_def by (simp add: shared_call_closure_table tableT shared_call_demanded_sites readS_def)
    finally show ?thesis .
  qed
  have evaluation: "shared_call_evaluation P R=(case finite_demanded_sites readS finite_application_premise_calls roots of
      None \<Rightarrow> (R,finite_program_evaluation P R)
    | Some D \<Rightarrow> (fimage h D,presented_closed_evaluation ?S (prepare_program ?S P) P D))"
    unfolding h_def by (simp add: shared_call_evaluation_def tableT shared_call_demanded_sites readS_def Let_def)
  show ?thesis
  proof (cases "finite_demanded_sites readS finite_application_premise_calls roots")
    case None
    then show ?thesis by (simp add: evaluation closure native_call_evaluation_def)
  next
    case (Some D)
    obtain A where readings: "finite_demanded_readings readS finite_application_premise_calls roots=Some (D,A)"
      using Some by (auto simp: finite_demanded_sites_readings)
    have closed: "e |\<in>| D" if "q |\<in>| D" "x |\<in>| readS q" "e |\<in>| finite_application_premise_calls x" for q x e
      by (rule finite_demanded_readings_closed(2)[OF readings that])
    have roots_in: "fset roots\<subseteq>U"
    proof
      fix q assume q: "q\<in>fset roots"
      have "h q |\<in>| fimage h roots" using q by (rule fimageI)
      then have "h q |\<in>| R" by (simp only: image)
      then have formed_q: "finite_term_formed (snd (h q))" by (rule fbspec[OF requests])
      have "shared_canonical T (snd q)" using fields(3) q by auto
      then show "q\<in>U" using formed_q by (simp add: U_def h_def)
    qed
    have within: "e\<in>U" if "q\<in>U" "x |\<in>| readS q" "e |\<in>| finite_application_premise_calls x" for q x e
    proof -
      obtain d t where qs: "q=(d,t)" by (cases q)
      have t: "t\<in>{s. shared_canonical T s}" and tf: "finite_term_formed (presented_decode ?S t)"
        using that(1) by (simp_all add: U_def qs)
      have member: "x |\<in>| presented_constructed_applications ?S (prepare_program ?S P) d t"
        using that(2) by (simp add: readS_def qs)
      obtain e' c y V H where xs: "x=(e',c,y,V,H)" using prod_cases5 by blast
      have domain: "\<forall>s e'' z. (s,e'',z) |\<in>| H \<longrightarrow> z\<in>{s. shared_canonical T s}"
        using shared.presented_constructed_application_domain[OF t member[unfolded xs]] by blast
      have canonical: "shared_canonical T (snd e)"
        using domain that(3) by (auto simp: xs finite_application_premise_calls_def)
      have decoded: "presented_application_decode ?S x |\<in>| finite_program_applications P {|(d,presented_decode ?S t)|}"
      proof -
        have "presented_application_decode ?S x |\<in>| fimage (presented_application_decode ?S)
            (presented_constructed_applications ?S (prepare_program ?S P) d t)" using member by (rule fimageI)
        then show ?thesis
          by (simp only: shared.presented_constructed_applications_decode[OF t]
            finite_constructed_applications_exact[OF system tf, symmetric])
      qed
      have "map_prod id (presented_decode ?S) e |\<in>| fimage (map_prod id (presented_decode ?S)) (finite_application_premise_calls x)"
        using that(3) by (rule fimageI)
      then have "map_prod id (presented_decode ?S) e |\<in>| finite_application_premise_calls (presented_application_decode ?S x)"
        by (simp only: finite_application_premise_calls_decode)
      then have "finite_term_formed (snd (map_prod id (presented_decode ?S) e))"
        by (rule finite_program_call_premise_formed[OF decoded])
      then show "e\<in>U" using canonical by (simp add: U_def)
    qed
    have inside: "fset D\<subseteq>U" by (rule finite_demanded_sites_within[OF roots_in within Some])
    have calls: "shared_canonical T (snd q) \<and> finite_term_formed (presented_decode ?S (snd q))" if "q |\<in>| D" for q
      using inside that by (auto simp: U_def)
    have closedD: "e |\<in>| D"
      if "q |\<in>| D" "x |\<in>| presented_constructed_applications ?S (prepare_program ?S P) (fst q) (snd q)"
        "e |\<in>| finite_application_premise_calls x" for q x e
      by (rule closed[OF that(1) _ that(3)], unfold readS_def, rule that(2))
    have "presented_closed_evaluation ?S (prepare_program ?S P) P D=finite_program_evaluation P (fimage h D)"
      unfolding h_def
      by (rule presented_closed_evaluation_exact[where T=T and P=P and C=D, OF fields(1) system calls closedD])
    then show ?thesis by (simp add: evaluation closure native_call_evaluation_def Some Let_def)
  qed
qed

text \<open>
  The evaluation of a stage's requests checks the program and the requests at its entry, as their closure
  does, and a formed one is computed over shared calls; every result is the original one.
\<close>

lemma native_call_evaluation_shared_code [code]:
  "native_call_evaluation P R=(if finite_system_formed P \<and> fBall R (\<lambda>q. finite_term_formed (snd q))
    then shared_call_evaluation P R
    else (let D=native_call_closure P R in (D,positioned_program_evaluation native_call_key P D)))"
  by (simp add: shared_call_evaluation_exact positioned_program_evaluation_exact[OF native_call_inverse]
    native_call_evaluation_def)

lemma finite_native_generation_shared_code [code]:
  "finite_native_generation E u r x=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> let D=finite_program_term_demand P {|x|} in
      map_option (\<lambda>A. (P,D,A,finite_program_generation_rows P
        (finite_native_seed_rows P x A))) (if finite_system_formed P \<and> fBall D (\<lambda>q. finite_term_formed (snd q))
          then shared_program_evaluation P D else positioned_program_evaluation native_call_key P D))"
  by (simp add: finite_native_generation_positioned_code shared_program_evaluation_exact
    positioned_program_evaluation_exact[OF native_call_inverse] Let_def split: option.split)

lemma workflow_stage_reference_shared_code [code]:
  "workflow_stage_reference S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        map_option (\<lambda>A. filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys)
          (snd (native_call_evaluation P
            (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys)))))))"
  by (simp only: workflow_stage_reference_positioned_code native_call_evaluation_def native_call_closure_def
    Let_def snd_conv positioned_program_evaluation_exact[OF native_call_inverse])

lemma workflow_stage_evidence_shared_code [code]:
  "workflow_stage_evidence S input result=(case result of (P,D,A,T,ys) \<Rightarrow>
    (case workflow_scope_result S input of None \<Rightarrow> False | Some scope \<Rightarrow>
      finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P \<and>
      workflow_entry S |\<in>| finite_system_definitions P \<and>
      (case native_call_evaluation P (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair input) scope))) of
        (D',E) \<Rightarrow> keyed_equal native_call_key D D' \<and> E=Some A) \<and>
      keyed_equal native_call_key (fimage fst T) A \<and> finite_inspection_rows_hold (finite_proof_inspection P T) \<and>
      ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair input y) |\<in>| A) scope))"
  by (simp add: workflow_stage_evidence_positioned_code native_call_evaluation_def Let_def native_call_closure_def
    positioned_program_evaluation_exact[OF native_call_inverse] keyed_equal_exact[OF native_call_inverse]
    cong: conj_cong split: prod.split option.split)

text \<open>
  Each operation computes its original result: over a formed table the presented rules are the program's
  rules carried by the canonical form, the rounds settle their positions as the positioned evaluation
  does, and the answers read back through the positions are decoded once. The evidence evaluates the
  closure its supplied demand is compared with, which is that demand whenever the comparison holds. The
  certificate path keeps the keyed history, as the positioned evaluation left it.
\<close>

end
