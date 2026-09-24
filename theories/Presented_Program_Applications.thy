theory Presented_Program_Applications
  imports Presented_Term_Matching Factor_Demanded_Program_Calls
begin

section \<open>A program whose literal leaves are presented once\<close>

text \<open>
  The applications of a call are built by the operations of @{text Presented_Term_Matching} over a
  presentation of terms (DECISIONS.md "An evaluation's calls are built over the shared subterms of its
  requests", B3). A literal leaf of a pattern is presented by the presentation's canonical constructor.
  An evaluation fits every clause's head and instantiates every clause's premises at every call it
  demands, so the program's literal leaves are presented once, when the program is prepared for the
  evaluation, and every call after that compares with or places the prepared leaf: a prepared pattern
  holds its literal leaf presented, or no leaf where the literal is not formed, which fits no term and
  has no instance. Prepared, a pattern fits, matches and is instantiated exactly as the pattern does
  over the presentation (@{text prepared_pattern_fits_prepare}, @{text prepared_matching_rows_prepare},
  @{text prepared_pattern_instances_prepare}), for every presentation.
\<close>

datatype ('a,'p) prepared_pattern = Prepared_Variable 'a | Prepared_Literal "'p option"
  | Prepared_Pair "('a,'p) prepared_pattern" "('a,'p) prepared_pattern"

fun prepare_pattern :: "'p term_presentation \<Rightarrow> 'a finite_term_pattern \<Rightarrow> ('a,'p) prepared_pattern" where
  "prepare_pattern P (Finite_Variable a)=Prepared_Variable a"
| "prepare_pattern P (Finite_Pattern_Target x)=
    Prepared_Literal (if finite_target_formed x then Some (presented_target P x) else None)"
| "prepare_pattern P (Finite_Pattern_Payload v)=
    Prepared_Literal (if octets_formed v then Some (presented_payload P v) else None)"
| "prepare_pattern P (Finite_Pattern_Pair p q)=Prepared_Pair (prepare_pattern P p) (prepare_pattern P q)"

fun prepared_pattern_fits :: "'p term_presentation \<Rightarrow> ('a,'p) prepared_pattern \<Rightarrow> 'p \<Rightarrow> bool" where
  "prepared_pattern_fits P (Prepared_Variable a) t=True"
| "prepared_pattern_fits P (Prepared_Literal l) t=(l=Some t)"
| "prepared_pattern_fits P (Prepared_Pair p q) t=(case presented_view P t of View_Pair x y \<Rightarrow>
    prepared_pattern_fits P p x \<and> prepared_pattern_fits P q y | _ \<Rightarrow> False)"

fun prepared_matching_rows :: "'p term_presentation \<Rightarrow> ('a,'p) prepared_pattern \<Rightarrow> 'p \<Rightarrow> ('a\<times>'p) list" where
  "prepared_matching_rows P (Prepared_Variable a) t=[(a,t)]"
| "prepared_matching_rows P (Prepared_Literal l) t=[]"
| "prepared_matching_rows P (Prepared_Pair p q) t=(case presented_view P t of View_Pair x y \<Rightarrow>
    prepared_matching_rows P p x@prepared_matching_rows P q y | _ \<Rightarrow> [])"

definition prepared_matching_bindings ::
    "'p term_presentation \<Rightarrow> ('a,'p) prepared_pattern \<Rightarrow> 'p \<Rightarrow> ('a\<times>'p) fset" where
  "prepared_matching_bindings P p t=fset_of_list (prepared_matching_rows P p t)"

definition prepared_matching_functional :: "'p term_presentation \<Rightarrow> ('a,'p) prepared_pattern \<Rightarrow> 'p \<Rightarrow> bool" where
  "prepared_matching_functional P p t=relation_rows_functional (prepared_matching_rows P p t)"

fun prepared_pattern_instances ::
    "'p term_presentation \<Rightarrow> ('a\<times>'p) fset \<Rightarrow> ('a,'p) prepared_pattern \<Rightarrow> 'p fset" where
  "prepared_pattern_instances P V (Prepared_Variable a)=fimage snd (ffilter (\<lambda>x. fst x=a) V)"
| "prepared_pattern_instances P V (Prepared_Literal l)=(case l of None \<Rightarrow> {||} | Some u \<Rightarrow> {|u|})"
| "prepared_pattern_instances P V (Prepared_Pair p q)=
    ffUnion (fimage (\<lambda>x. fimage (presented_pair P x) (prepared_pattern_instances P V q))
      (prepared_pattern_instances P V p))"

definition prepared_instantiated_premises :: "'p term_presentation \<Rightarrow>
    ('s\<times>('d\<times>('a,'p) prepared_pattern)) fset \<Rightarrow> ('a\<times>'p) fset \<Rightarrow> ('s\<times>('d\<times>'p)) fset" where
  "prepared_instantiated_premises P G V=ffUnion (fimage (\<lambda>(s,d,p).
    fimage (\<lambda>t. (s,d,t)) (prepared_pattern_instances P V p)) G)"

definition prepare_premises :: "'p term_presentation \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow>
    ('s\<times>('d\<times>('a,'p) prepared_pattern)) fset" where
  "prepare_premises P S=fimage (\<lambda>(s,d,p). (s,d,prepare_pattern P p)) (finite_schema_premises S)"

lemma prepared_pattern_fits_prepare:
  "prepared_pattern_fits P (prepare_pattern P p) t \<longleftrightarrow> presented_pattern_fits P p t"
  by (induction p arbitrary: t) (auto split: term_view.split if_split)

lemma prepared_matching_rows_prepare:
  "prepared_matching_rows P (prepare_pattern P p) t=presented_matching_rows P p t"
  by (induction p arbitrary: t) (simp_all split: term_view.split)

lemma prepared_matching_bindings_prepare:
  "prepared_matching_bindings P (prepare_pattern P p) t=presented_matching_bindings P p t"
  by (simp add: prepared_matching_bindings_def presented_matching_bindings_def prepared_matching_rows_prepare)

lemma prepared_matching_functional_prepare:
  "prepared_matching_functional P (prepare_pattern P p) t \<longleftrightarrow> presented_matching_functional P p t"
  by (simp add: prepared_matching_functional_def presented_matching_functional_def prepared_matching_rows_prepare)

lemma prepared_pattern_instances_prepare:
  "prepared_pattern_instances P V (prepare_pattern P p)=presented_pattern_instances P V p"
  by (induction p) (simp_all split: if_split)

lemma prepared_instantiated_premises_prepare:
  "prepared_instantiated_premises P (prepare_premises P S) V=presented_instantiated_premises P S V"
  by (simp add: prepared_instantiated_premises_def prepare_premises_def presented_instantiated_premises_def
      fimage_fimage comp_def split_def prepared_pattern_instances_prepare)

type_synonym ('a,'s,'d,'p) prepared_clause =
  "('a,'s,'d) finite_factor_schema\<times>('a,'p) prepared_pattern\<times>('s\<times>('d\<times>('a,'p) prepared_pattern)) fset"

definition prepare_clause :: "'p term_presentation \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'p) prepared_clause" where
  "prepare_clause P S=(S,prepare_pattern P (finite_schema_conclusion S),prepare_premises P S)"

record ('a,'s,'d,'c,'p) prepared_program =
  prepared_interfaces :: "('d\<times>('a,'p) prepared_pattern) fset"
  prepared_clauses :: "(('d\<times>'c)\<times>('a,'s,'d,'p) prepared_clause) fset"

definition prepare_program ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program" where
  "prepare_program P Q=\<lparr>prepared_interfaces=fimage (\<lambda>(e,p). (e,prepare_pattern P p)) (finite_system_interfaces Q),
    prepared_clauses=fimage (\<lambda>(k,S). (k,prepare_clause P S)) (finite_system_clauses Q)\<rparr>"

section \<open>The applications of a presented call\<close>

text \<open>
  The interface's fitting, a clause's constructed requests and a call's constructed applications are
  those of @{text Factor_Constructed_Program_Applications} over the prepared program: the head is fitted
  and matched against the presented call, the premises are instantiated with the presented bindings by
  the canonical constructors, and every premise call is fitted to its callee's interface as a presented
  term. No call is decoded.

  A material premise is read through decoding. It is the complete material equation of an artifact
  (@{text finite_material_observation}), a check of the whole structure of plain terms that no
  presentation's view reaches, so a clause with material premises checks them on its bindings decoded
  (@{text presented_material_satisfied}); a clause without them decodes nothing, the check coming
  after the head's fitting. The decoded bindings are read by the check alone: no call is built from
  them.
\<close>

definition presented_material_satisfied ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a\<times>'p) fset \<Rightarrow> bool" where
  "presented_material_satisfied P S V \<longleftrightarrow> finite_schema_materials S={||} \<or>
    finite_schema_material_satisfied S (fimage (map_prod id (presented_decode P)) V)"

definition presented_interface_fits ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> 'd \<Rightarrow> 'p \<Rightarrow> bool" where
  "presented_interface_fits P R d t \<longleftrightarrow> fBex (prepared_interfaces R)
    (\<lambda>(e,p). e=d \<and> prepared_pattern_fits P p t \<and> prepared_matching_functional P p t)"

definition presented_constructed_requests ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d,'p) prepared_clause \<Rightarrow> 'p \<Rightarrow>
      ('p\<times>('a\<times>'p) fset\<times>('s\<times>('d\<times>'p)) fset) fset" where
  "presented_constructed_requests P R d C t=(case C of (S,p,G) \<Rightarrow>
     let B=prepared_matching_bindings P p t; H=prepared_instantiated_premises P G B in
     if finite_schema_formed S \<and> finite_schema_head_missing S={||} \<and>
       prepared_pattern_fits P p t \<and> prepared_matching_functional P p t \<and>
       presented_material_satisfied P S B \<and>
       presented_interface_fits P R d t \<and> fBall H (\<lambda>(s,e,x). presented_interface_fits P R e x)
     then {|(t,B,H)|} else {||})"

definition presented_constructed_applications ::
    "'p term_presentation \<Rightarrow> ('a,'s,'d,'c,'p) prepared_program \<Rightarrow> 'd \<Rightarrow> 'p \<Rightarrow>
      ('d\<times>'c\<times>'p\<times>('a\<times>'p) fset\<times>('s\<times>('d\<times>'p)) fset) fset" where
  "presented_constructed_applications P R d t=ffUnion (fimage (\<lambda>((e,c),C). if e=d then
    fimage (\<lambda>r. (d,c,r)) (presented_constructed_requests P R d C t) else {||}) (prepared_clauses R))"

text \<open>
  A request and an application leave the evaluation decoded: the call, every bound value and every
  premise call.
\<close>

definition presented_request_decode :: "'p term_presentation \<Rightarrow> ('p\<times>('a\<times>'p) fset\<times>('s\<times>('d\<times>'p)) fset) \<Rightarrow>
    (finite_factor_term\<times>('a\<times>finite_factor_term) fset\<times>('s\<times>('d\<times>finite_factor_term)) fset)" where
  "presented_request_decode P r=(case r of (x,V,H) \<Rightarrow> (presented_decode P x,
    fimage (map_prod id (presented_decode P)) V, fimage (\<lambda>(s,e,y). (s,e,presented_decode P y)) H))"

definition presented_application_decode :: "'p term_presentation \<Rightarrow>
    ('d\<times>'c\<times>'p\<times>('a\<times>'p) fset\<times>('s\<times>('d\<times>'p)) fset) \<Rightarrow>
    ('d\<times>'c\<times>finite_factor_term\<times>('a\<times>finite_factor_term) fset\<times>('s\<times>('d\<times>finite_factor_term)) fset)" where
  "presented_application_decode P=map_prod id (map_prod id (presented_request_decode P))"


lemma fimage_ffUnion_member: "fimage f (ffUnion A)=ffUnion (fimage (fimage f) A)"
  by (rule fset_inject[THEN iffD1]) (auto simp: fimage.rep_eq ffUnion.rep_eq)

lemma presented_material_satisfied_decode:
  "presented_material_satisfied P S V \<longleftrightarrow>
    finite_schema_material_satisfied S (fimage (map_prod id (presented_decode P)) V)"
  by (auto simp: presented_material_satisfied_def finite_schema_material_satisfied_def)

lemma presented_interface_fits_prepare:
  "presented_interface_fits P (prepare_program P Q) d t \<longleftrightarrow> fBex (finite_system_interfaces Q)
    (\<lambda>(e,p). e=d \<and> presented_pattern_fits P p t \<and> presented_matching_functional P p t)"
  by (simp add: presented_interface_fits_def prepare_program_def split_def
      prepared_pattern_fits_prepare prepared_matching_functional_prepare)

lemma presented_constructed_request_member:
  "(x,V,H) |\<in>| presented_constructed_requests P R d (S,p,G) t \<Longrightarrow>
    x=t \<and> V=prepared_matching_bindings P p t \<and> H=prepared_instantiated_premises P G V"
  by (simp add: presented_constructed_requests_def Let_def split: if_splits)

lemma presented_constructed_application_member:
  "(e,c,x,V,H) |\<in>| presented_constructed_applications P (prepare_program P Q) d t \<longleftrightarrow> e=d \<and>
    (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses Q \<and>
      (x,V,H) |\<in>| presented_constructed_requests P (prepare_program P Q) d (prepare_clause P S) t)"
  by (force simp: presented_constructed_applications_def prepare_program_def ffUnion.rep_eq fimage.rep_eq
      split: if_splits)

lemma presented_application_premise_calls_decode:
  "finite_application_premise_calls (presented_application_decode P (e,c,x,V,H))=
    fimage (map_prod id (presented_decode P)) (fimage snd H)"
  by (simp add: finite_application_premise_calls_def presented_application_decode_def
      presented_request_decode_def fimage_fimage comp_def split_def map_prod_def)

section \<open>Every operation is exact through decoding, once for every presentation\<close>

context presented_terms
begin

lemma presented_instantiated_premises_domain:
  assumes V: "snd ` fset V\<subseteq>D" and member: "(s,e,x) |\<in>| presented_instantiated_premises P S V"
  shows "x\<in>D"
proof -
  obtain p where "x |\<in>| presented_pattern_instances P V p"
    using member by (auto simp: presented_instantiated_premises_def ffUnion.rep_eq fimage.rep_eq)
  then show ?thesis using presented_pattern_instances_domain[OF V] by blast
qed

theorem presented_interface_fits_decode:
  assumes t: "t\<in>D"
  shows "presented_interface_fits P (prepare_program P Q) d t \<longleftrightarrow> finite_interface_fits Q d (presented_decode P t)"
  by (simp add: presented_interface_fits_prepare finite_interface_fits_def
      presented_pattern_fits_decode[OF t] presented_matching_functional_decode[OF t])

theorem presented_constructed_requests_decode:
  assumes t: "t\<in>D"
  shows "fimage (presented_request_decode P) (presented_constructed_requests P (prepare_program P Q) d (prepare_clause P S) t)=
    finite_constructed_requests Q d S (presented_decode P t)"
proof -
  define B where "B=presented_matching_bindings P (finite_schema_conclusion S) t"
  define H where "H=presented_instantiated_premises P S B"
  have B_domain: "snd ` fset B\<subseteq>D" unfolding B_def by (rule presented_matching_bindings_domain[OF t])
  have B_decode: "fimage (map_prod id (presented_decode P)) B=
      finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t)"
    unfolding B_def by (rule presented_matching_bindings_decode[OF t])
  have H_decode: "fimage (\<lambda>(s,e,x). (s,e,presented_decode P x)) H=
      finite_instantiated_premises S (finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t))"
    unfolding H_def B_decode[symmetric] by (rule presented_instantiated_premises_decode[OF B_domain])
  have H_fits: "fBall H (\<lambda>(s,e,x). presented_interface_fits P (prepare_program P Q) e x) \<longleftrightarrow>
      fBall (finite_instantiated_premises S (finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t)))
        (\<lambda>(s,e,x). finite_interface_fits Q e x)"
    unfolding H_decode[symmetric] FSet.ball_simps(7)
    apply (rule fBall_cong[OF refl])
    subgoal for z
      by (cases z) (auto dest: presented_instantiated_premises_domain[OF B_domain]
          simp: H_def presented_interface_fits_decode)
    done
  have fits: "prepared_pattern_fits P (prepare_pattern P (finite_schema_conclusion S)) t \<longleftrightarrow>
      finite_pattern_fits (finite_schema_conclusion S) (presented_decode P t)"
    by (simp add: prepared_pattern_fits_prepare presented_pattern_fits_decode[OF t])
  have functional: "prepared_matching_functional P (prepare_pattern P (finite_schema_conclusion S)) t \<longleftrightarrow>
      finite_matching_functional (finite_schema_conclusion S) (presented_decode P t)"
    by (simp add: prepared_matching_functional_prepare presented_matching_functional_decode[OF t])
  have bindings: "prepared_matching_bindings P (prepare_pattern P (finite_schema_conclusion S)) t=B"
    by (simp add: B_def prepared_matching_bindings_prepare)
  have instantiated: "prepared_instantiated_premises P (prepare_premises P S) B=H"
    by (simp add: H_def prepared_instantiated_premises_prepare)
  have material: "presented_material_satisfied P S B \<longleftrightarrow>
      finite_schema_material_satisfied S (finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t))"
    by (simp add: presented_material_satisfied_decode B_decode)
  have decoded: "presented_request_decode P (t,B,H)=(presented_decode P t,
      finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t),
      finite_instantiated_premises S (finite_matching_bindings (finite_schema_conclusion S) (presented_decode P t)))"
    by (simp add: presented_request_decode_def B_decode H_decode)
  show ?thesis
    unfolding presented_constructed_requests_def finite_constructed_requests_def prepare_clause_def Let_def
    by (simp add: fits functional bindings instantiated material presented_interface_fits_decode[OF t] H_fits decoded
        split: if_split)
qed

theorem presented_constructed_applications_decode:
  assumes t: "t\<in>D"
  shows "fimage (presented_application_decode P) (presented_constructed_applications P (prepare_program P Q) d t)=
    finite_constructed_applications Q d (presented_decode P t)"
proof -
  have wrap: "(\<lambda>(x,V,H). (e,c,x,V,H))=(\<lambda>r. (e,c,r))" for e c
    by (simp add: fun_eq_iff split_def)
  have clause: "fimage (presented_application_decode P) (if e=d then fimage (\<lambda>r. (d,c,r))
      (presented_constructed_requests P (prepare_program P Q) d (prepare_clause P S) t) else {||})=
    (if e=d then fimage (\<lambda>r. (d,c,r)) (finite_constructed_requests Q d S (presented_decode P t)) else {||})" for e c S
    by (simp add: presented_application_decode_def fimage_fimage comp_def
        flip: presented_constructed_requests_decode[OF t] split: if_split)
  have clauses: "prepared_clauses (prepare_program P Q)=
      fimage (\<lambda>(k,S). (k,prepare_clause P S)) (finite_system_clauses Q)"
    by (simp add: prepare_program_def)
  show ?thesis
    unfolding presented_constructed_applications_def finite_constructed_applications_def clauses wrap
      fimage_ffUnion_member fimage_fimage
    apply (rule arg_cong[where f=ffUnion], rule fset.map_cong[OF refl])
    subgoal for z
      by (cases z) (auto simp: clause split: prod.splits)
    done
qed

corollary presented_constructed_applications_exact:
  assumes system: "finite_system_formed Q" and t: "t\<in>D" and formed: "finite_term_formed (presented_decode P t)"
  shows "fimage (presented_application_decode P) (presented_constructed_applications P (prepare_program P Q) d t)=
    finite_program_applications Q {|(d,presented_decode P t)|}"
  by (simp add: presented_constructed_applications_decode[OF t] finite_constructed_applications_exact[OF system formed])

text \<open>
  An application of a presented call in the domain holds that call, its bindings as the presented
  match returns them and its premise calls as the canonical constructors instantiate them, all
  members of the domain: its premise calls are presented calls the evaluation can demand in turn.
\<close>

theorem presented_constructed_application_domain:
  assumes t: "t\<in>D"
    and member: "(e,c,x,V,H) |\<in>| presented_constructed_applications P (prepare_program P Q) d t"
  shows "e=d \<and> x=t \<and> snd ` fset V\<subseteq>D \<and> (\<forall>s e' y. (s,e',y) |\<in>| H \<longrightarrow> y\<in>D) \<and>
    (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses Q \<and>
      V=presented_matching_bindings P (finite_schema_conclusion S) t \<and> H=presented_instantiated_premises P S V)"
proof -
  obtain S where e: "e=d" and clause: "((d,c),S) |\<in>| finite_system_clauses Q"
    and request: "(x,V,H) |\<in>| presented_constructed_requests P (prepare_program P Q) d (prepare_clause P S) t"
    using member by (auto simp: presented_constructed_application_member)
  have fields: "x=t" "V=presented_matching_bindings P (finite_schema_conclusion S) t"
    "H=presented_instantiated_premises P S V"
    using presented_constructed_request_member[OF request[unfolded prepare_clause_def]]
    by (simp_all add: prepared_matching_bindings_prepare prepared_instantiated_premises_prepare)
  have V: "snd ` fset V\<subseteq>D" using fields(2) presented_matching_bindings_domain[OF t] by simp
  have "y\<in>D" if "(s,e',y) |\<in>| H" for s e' y
    using that unfolding fields(3) by (rule presented_instantiated_premises_domain[OF V])
  then show ?thesis using e fields V clause by blast
qed

end

section \<open>Plain terms are the identity presentation\<close>

lemma plain_request_decode: "presented_request_decode plain_term_presentation=id"
  by (rule ext) (simp add: presented_request_decode_def map_prod.id split_def)

lemma plain_application_decode: "presented_application_decode plain_term_presentation=id"
  by (simp add: presented_application_decode_def plain_request_decode map_prod.id)

theorem plain_material_satisfied:
  "presented_material_satisfied plain_term_presentation S V \<longleftrightarrow> finite_schema_material_satisfied S V"
  by (simp add: presented_material_satisfied_decode map_prod.id)

theorem plain_interface_fits:
  "presented_interface_fits plain_term_presentation (prepare_program plain_term_presentation Q) d t \<longleftrightarrow>
    finite_interface_fits Q d t"
  using plain_terms.presented_interface_fits_decode[of t Q d] by simp

theorem plain_constructed_requests:
  "presented_constructed_requests plain_term_presentation (prepare_program plain_term_presentation Q) d
      (prepare_clause plain_term_presentation S) t=finite_constructed_requests Q d S t"
  using plain_terms.presented_constructed_requests_decode[of t Q d S] by (simp add: plain_request_decode)

theorem plain_constructed_applications:
  "presented_constructed_applications plain_term_presentation (prepare_program plain_term_presentation Q) d t=
    finite_constructed_applications Q d t"
  using plain_terms.presented_constructed_applications_decode[of t Q d] by (simp add: plain_application_decode)

end
