theory Factor_Checked_Certificate_Premises
  imports Factor_Finite_Native_Certificate_Graphs Factor_Constructed_Program_Applications Established_Premises
begin

section \<open>The admitted instance at a formed call\<close>

text \<open>
  The admitted instance at a call checks the formation of the program and of the call's term, of every
  premise call's term, and the interfaces' acceptance of them. At a formed program the premise terms are
  formed by the clause's own instance (@{thm [source] finite_instantiated_premise_formed}), so where the
  call's term is formed only the interfaces' fit remains of those checks
  (@{thm [source] finite_admitted_constructed}): the first notion of @{text Established_Premises}, the
  premise the formation of the call's term, the program's formation a premise of the instance. The
  program's formation is established where the program is read (@{const finite_native_source}), the
  term's where the call is made, and each premise term's by its parent's instance.
\<close>

definition finite_formed_clause_reading ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>'d\<Rightarrow>'c\<Rightarrow>('a\<times>finite_factor_term) fset\<Rightarrow>finite_factor_term\<Rightarrow>
      ('d\<times>'c)\<times>('a,'s,'d) finite_factor_schema\<Rightarrow>('s\<times>('d\<times>finite_factor_term)) fset fset" where
  "finite_formed_clause_reading P d c V t z=(case z of ((e,k),S) \<Rightarrow> if e=d \<and> k=c then
    (let H=finite_instantiated_premises S V in
      if finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V \<and>
        fBall H (\<lambda>(r,g,x). finite_interface_fits P g x) then {|H|} else {||}) else {||})"

lemma finite_formed_clause_reading_member:
  "H |\<in>| finite_formed_clause_reading P d c V t ((e,k),S) \<longleftrightarrow> e=d \<and> k=c \<and>
    H=finite_instantiated_premises S V \<and> finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V \<and>
    fBall H (\<lambda>(r,g,x). finite_interface_fits P g x)"
proof (cases "e=d \<and> k=c \<and> finite_schema_instance S V t (finite_instantiated_premises S V) \<and>
    finite_schema_material_satisfied S V \<and>
    fBall (finite_instantiated_premises S V) (\<lambda>(r,g,x). finite_interface_fits P g x)")
  case True
  then show ?thesis by (auto simp: finite_formed_clause_reading_def Let_def finsert.rep_eq bot_fset.rep_eq)
next
  case False
  have "finite_formed_clause_reading P d c V t ((e,k),S)={||}"
    using False by (auto simp: finite_formed_clause_reading_def Let_def split: if_splits)
  moreover have "\<not>(e=d \<and> k=c \<and> H=finite_instantiated_premises S V \<and> finite_schema_instance S V t H \<and>
      finite_schema_material_satisfied S V \<and> fBall H (\<lambda>(r,g,x). finite_interface_fits P g x))"
    using False by blast
  ultimately show ?thesis by (simp add: bot_fset.rep_eq)
qed

definition finite_formed_premise_readings ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>'d\<Rightarrow>'c\<Rightarrow>('a\<times>finite_factor_term) fset\<Rightarrow>finite_factor_term\<Rightarrow>
      ('s\<times>('d\<times>finite_factor_term)) fset fset" where
  "finite_formed_premise_readings P d c V t=(if finite_interface_fits P d t then
    ffUnion (fimage (finite_formed_clause_reading P d c V t) (finite_system_clauses P)) else {||})"

lemma finite_formed_premise_readings_member:
  "H |\<in>| finite_formed_premise_readings P d c V t \<longleftrightarrow> finite_interface_fits P d t \<and>
    (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses P \<and> H=finite_instantiated_premises S V \<and>
      finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V \<and>
      fBall H (\<lambda>(r,g,x). finite_interface_fits P g x))"
proof (cases "finite_interface_fits P d t")
  case True
  have "H |\<in>| finite_formed_premise_readings P d c V t \<longleftrightarrow>
      (\<exists>z. z |\<in>| finite_system_clauses P \<and> H |\<in>| finite_formed_clause_reading P d c V t z)"
    by (simp only: finite_formed_premise_readings_def if_P[OF True] finite_union_image_member)
  also have "\<dots> \<longleftrightarrow> (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses P \<and> H=finite_instantiated_premises S V \<and>
      finite_schema_instance S V t H \<and> finite_schema_material_satisfied S V \<and>
      fBall H (\<lambda>(r,g,x). finite_interface_fits P g x))"
    by (auto simp: finite_formed_clause_reading_member split_paired_Ex)
  finally show ?thesis using True by simp
next
  case False
  then show ?thesis by (simp add: finite_formed_premise_readings_def bot_fset.rep_eq)
qed

theorem finite_formed_premise_readings_exact:
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
  shows "finite_admitted_premise_readings P d c V t=finite_formed_premise_readings P d c V t"
proof (rule fset_eqI)
  fix H
  show "H |\<in>| finite_admitted_premise_readings P d c V t \<longleftrightarrow> H |\<in>| finite_formed_premise_readings P d c V t"
  proof
    assume "H |\<in>| finite_admitted_premise_readings P d c V t"
    then have admitted: "finite_admitted_schema_instance P d c V t H"
      by (simp only: finite_admitted_premise_reading_exact)
    then obtain S where clause: "((d,c),S) |\<in>| finite_system_clauses P"
      and inst: "finite_schema_instance S V t H" and material: "finite_schema_material_satisfied S V"
      by (auto simp: finite_admitted_schema_instance_def)
    have body: "finite_instantiated_premises S V=H" by (rule finite_instantiated_premises_exact[OF inst])
    have fits: "finite_interface_fits P d t \<and> fBall H (\<lambda>(s,e,x). finite_interface_fits P e x)"
      using admitted finite_admitted_constructed[OF system formed clause inst material] by blast
    show "H |\<in>| finite_formed_premise_readings P d c V t"
      using clause inst material fits body by (auto simp: finite_formed_premise_readings_member)
  next
    assume "H |\<in>| finite_formed_premise_readings P d c V t"
    then obtain S where fits: "finite_interface_fits P d t" and clause: "((d,c),S) |\<in>| finite_system_clauses P"
      and inst: "finite_schema_instance S V t H" and material: "finite_schema_material_satisfied S V"
      and fitting: "fBall H (\<lambda>(r,g,x). finite_interface_fits P g x)"
      by (auto simp: finite_formed_premise_readings_member)
    have "finite_admitted_schema_instance P d c V t H"
      using finite_admitted_constructed[OF system formed clause inst material] fits fitting by blast
    then show "H |\<in>| finite_admitted_premise_readings P d c V t"
      by (simp only: finite_admitted_premise_reading_exact)
  qed
qed

lemma finite_formed_premise_readings_established:
  assumes "finite_system_formed P"
  shows "established_premise (finite_admitted_premise_readings P d c V) finite_term_formed
    (finite_formed_premise_readings P d c V)"
  by (rule established_premise.intro) (rule finite_formed_premise_readings_exact[OF assms])

text \<open>A checked certificate's program and call term are formed, and so is every premise term it reads.\<close>

lemma finite_checked_certificate_formed:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "finite_system_formed P" "finite_term_formed t"
proof -
  obtain c V B where tree: "p=Schema_Proof c V B" by (cases p) auto
  obtain H where "H |\<in>| finite_admitted_premise_readings P d c V t"
    using checked by (auto simp only: tree finite_checks_schema_proof_node)
  then have "finite_schema_call_formed P d t"
    by (simp add: finite_admitted_premise_reading_exact finite_admitted_schema_instance_def)
  then show "finite_system_formed P" "finite_term_formed t"
    by (auto simp: finite_schema_call_formed_def finite_pattern_accepts_def)
qed

lemma finite_admitted_premise_term_formed:
  assumes "H |\<in>| finite_admitted_premise_readings P d c V t" "(s,e,x) |\<in>| H"
  shows "finite_term_formed x"
  using assms by (auto simp: finite_admitted_premise_reading_exact finite_admitted_schema_instance_def
    finite_schema_call_formed_def finite_pattern_accepts_def)

section \<open>A certificate's premise readings, computed once per node\<close>

text \<open>
  A certificate's paths, positions, discharges and coordinates each read the admitted instance at every
  node again (@{const finite_schema_proof_paths}, @{const finite_schema_proof_positions},
  @{const finite_schema_flat_discharges} through @{const finite_schema_proof_children}), and the check
  (@{const finite_checks_schema_proof}) reads it once more. One traversal reads it once at each node: for
  each reading it pairs every socket with the whole result of its child, once, and the node's check, its
  paths and its discharges are read off those results. The traversal returns the node itself beside them,
  so a parent reads its children's nodes from their results. At a formed program and call term it is
  exactly the node, the check, the paths and the discharges over the positions: each child's term is
  formed by its parent's instance, so the formed readings serve at every node.
\<close>

definition finite_socket_results ::
    "('s\<times>('d\<Rightarrow>finite_factor_term\<Rightarrow>'r)) fset\<Rightarrow>('s\<times>('d\<times>finite_factor_term)) fset\<Rightarrow>('s\<times>'r) fset" where
  "finite_socket_results R H=ffUnion (fimage (\<lambda>(s,F). ffUnion (fimage (\<lambda>(r,e,x).
    if r=s then {|(s,F e x)|} else {||}) H)) R)"

lemma finite_union_image_memberI: "w |\<in>| A \<Longrightarrow> z |\<in>| F w \<Longrightarrow> z |\<in>| ffUnion (fimage F A)"
  by (auto simp: finite_union_image_member)

lemma finite_union_image_memberE:
  assumes "z |\<in>| ffUnion (fimage F A)"
  obtains w where "w |\<in>| A" "z |\<in>| F w"
  using assms by (auto simp: finite_union_image_member)

lemma finite_cons_member: "z |\<in>| fimage (map_prod (Cons s) id) X \<longleftrightarrow> (\<exists>ss m. z=(s#ss,m) \<and> (ss,m) |\<in>| X)"
  by (auto simp: fimage.rep_eq intro: rev_image_eqI)

lemma finite_union_singletons: "ffUnion (fimage (\<lambda>z. {|g z|}) A)=fimage g A"
  by (rule fset_eqI) (auto simp: finite_union_image_member fimage.rep_eq finsert.rep_eq bot_fset.rep_eq)

lemma finite_socket_results_keyed:
  "finite_socket_results (fimage (map_prod id f) B) H=
    fimage (\<lambda>(s,q,e,x). (s,f q e x)) (finite_keyed_product B H)"
  unfolding finite_socket_results_def
  using finite_keyed_product_union_values[where R=B and S=H and f=f and F="\<lambda>s a b. {|(s,a (fst b) (snd b))|}"]
  by (simp only: case_prod_unfold fst_conv snd_conv finite_union_singletons)

type_synonym ('a,'s,'d,'c) finite_certificate_premise_rows =
  "('a,'s,'d,'c) finite_instantiated_proof_node\<times>bool\<times>
    ('s list\<times>('a,'s,'d,'c) finite_instantiated_proof_node) fset\<times>
    ((('a,'s,'d,'c) finite_instantiated_proof_node\<times>'s)\<times>('a,'s,'d,'c) finite_instantiated_proof_node) fset"

primrec finite_certificate_premises ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'c) finite_schema_proof\<Rightarrow>'d\<Rightarrow>finite_factor_term\<Rightarrow>
      ('a,'s,'d,'c) finite_certificate_premise_rows" where
  "finite_certificate_premises P (Schema_Proof c V B) d t=(let n=(Schema_Proof c V B,d,t);
    K=fimage (\<lambda>H. (H,finite_socket_results (fimage (map_prod id (finite_certificate_premises P)) B) H))
      (finite_formed_premise_readings P d c V t) in
    (n,finite_relation_functional B \<and> fBex K (\<lambda>(H,Z). fimage fst B=fimage fst H \<and>
        fBall (fimage fst B) (\<lambda>s. fBex Z (\<lambda>(r,y). r=s \<and> fst (snd y)))),
      finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
        fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K)),
      ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K)))"

theorem finite_certificate_premises_exact:
  assumes system: "finite_system_formed P" and formed: "finite_term_formed t"
  shows "finite_certificate_premises P p d t=((p,d,t),finite_checks_schema_proof P p d t,
    finite_schema_proof_paths P p d t,finite_schema_flat_discharges P (finite_schema_proof_positions P p d t))"
  using formed
proof (induction p arbitrary: d t)
  case (Schema_Proof c V B)
  define n where "n=(Schema_Proof c V B,d,t)"
  define Ro where "Ro=finite_admitted_premise_readings P d c V t"
  define orig where "orig=(\<lambda>q e x. ((q,e,x),finite_checks_schema_proof P q e x,finite_schema_proof_paths P q e x,
    finite_schema_flat_discharges P (finite_schema_proof_positions P q e x)))"
  define K where "K=fimage (\<lambda>H. (H,fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H))) Ro"
  have child: "finite_certificate_premises P q e x=orig q e x"
    if "(s,q) |\<in>| B" "H |\<in>| Ro" "(s,e,x) |\<in>| H" for s q e x H
  proof -
    have formed_x: "finite_term_formed x"
      using that(2,3) unfolding Ro_def by (rule finite_admitted_premise_term_formed)
    have q: "q\<in>Basic_BNFs.snds (s,q)" by (simp add: Basic_BNFs.prod_set_defs)
    show ?thesis using Schema_Proof.IH[OF that(1) q formed_x] by (simp add: orig_def)
  qed
  have readings: "finite_formed_premise_readings P d c V t=Ro"
    unfolding Ro_def using finite_formed_premise_readings_exact[OF system Schema_Proof.prems] by simp
  have results: "finite_socket_results (fimage (map_prod id (finite_certificate_premises P)) B) H=
      fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)" if reading: "H |\<in>| Ro" for H
  proof -
    have "fimage (\<lambda>(s,q,e,x). (s,finite_certificate_premises P q e x)) (finite_keyed_product B H)=
        fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)"
    proof (rule fset_inject[THEN iffD1], simp only: fimage.rep_eq, rule image_cong[OF refl])
      fix z assume member: "z\<in>fset (finite_keyed_product B H)"
      obtain s q e x where shape: "z=(s,q,e,x)" using prod_cases4 by blast
      have "(s,q) |\<in>| B" "(s,e,x) |\<in>| H" using member by (simp_all add: shape finite_keyed_product_member)
      then show "(\<lambda>(s,q,e,x). (s,finite_certificate_premises P q e x)) z=(\<lambda>(s,q,e,x). (s,orig q e x)) z"
        using child reading by (simp add: shape)
    qed
    then show ?thesis by (simp only: finite_socket_results_keyed)
  qed
  have K: "fimage (\<lambda>H. (H,finite_socket_results (fimage (map_prod id (finite_certificate_premises P)) B) H)) Ro=K"
    unfolding K_def
    by (rule fset_inject[THEN iffD1], simp only: fimage.rep_eq, rule image_cong[OF refl]) (simp add: results)
  have unfolded: "finite_certificate_premises P (Schema_Proof c V B) d t=(n,
      finite_relation_functional B \<and> fBex K (\<lambda>(H,Z). fimage fst B=fimage fst H \<and>
        fBall (fimage fst B) (\<lambda>s. fBex Z (\<lambda>(r,y). r=s \<and> fst (snd y)))),
      finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
        fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K)),
      ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K))"
    by (simp only: finite_certificate_premises.simps Let_def readings K n_def)
  have children_root: "(s,q,e,x) |\<in>| finite_schema_proof_children P n \<longleftrightarrow>
      (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H)" for s q e x
    by (simp only: n_def Ro_def finite_schema_proof_children_member)
  have paths_root: "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t \<longleftrightarrow> z=([],n) \<or>
      (\<exists>s q e x ss m. z=(s#ss,m) \<and> (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
        (ss,m) |\<in>| finite_schema_proof_paths P q e x)" for z
  proof -
    have unfold: "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t \<longleftrightarrow> z=([],n) \<or>
        (\<exists>w. w |\<in>| finite_schema_proof_children P n \<and>
          z |\<in>| (case w of (s,q,e,x) \<Rightarrow> fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x)))"
      unfolding finite_schema_proof_paths_unfold[of P "Schema_Proof c V B" d t] n_def[symmetric]
      by (simp only: finsert.rep_eq insert_iff finite_union_image_member)
    show ?thesis
    proof
      assume "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t"
      then consider "z=([],n)" | w where "w |\<in>| finite_schema_proof_children P n"
          "z |\<in>| (case w of (s,q,e,x) \<Rightarrow> fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x))"
        using unfold by blast
      then show "z=([],n) \<or> (\<exists>s q e x ss m. z=(s#ss,m) \<and> (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          (ss,m) |\<in>| finite_schema_proof_paths P q e x)"
      proof cases
        case 1
        then show ?thesis by blast
      next
        case (2 w)
        obtain s q e x where w: "w=(s,q,e,x)" using prod_cases4 by blast
        obtain ss m where "z=(s#ss,m)" "(ss,m) |\<in>| finite_schema_proof_paths P q e x"
          using 2(2) by (auto simp: w fimage.rep_eq)
        moreover have "(s,q) |\<in>| B" "\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H"
          using 2(1) by (simp_all add: w children_root)
        ultimately show ?thesis by blast
      qed
    next
      assume "z=([],n) \<or> (\<exists>s q e x ss m. z=(s#ss,m) \<and> (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          (ss,m) |\<in>| finite_schema_proof_paths P q e x)"
      then show "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t"
      proof
        assume "z=([],n)"
        then show ?thesis using unfold by blast
      next
        assume "\<exists>s q e x ss m. z=(s#ss,m) \<and> (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          (ss,m) |\<in>| finite_schema_proof_paths P q e x"
        then obtain s q e x ss m where z: "z=(s#ss,m)" and child: "(s,q,e,x) |\<in>| finite_schema_proof_children P n"
          and path: "(ss,m) |\<in>| finite_schema_proof_paths P q e x"
          using children_root by blast
        have "z |\<in>| (case (s,q,e,x) of (s,q,e,x) \<Rightarrow> fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x))"
          using path by (force simp: z fimage.rep_eq)
        then show ?thesis using unfold child by blast
      qed
    qed
  qed
  have positions_root: "m |\<in>| finite_schema_proof_positions P (Schema_Proof c V B) d t \<longleftrightarrow> m=n \<or>
      (\<exists>s q e x. (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
        m |\<in>| finite_schema_proof_positions P q e x)" for m
    unfolding finite_schema_proof_positions_unfold[of P "Schema_Proof c V B" d t] n_def[symmetric]
    by (simp only: finsert.rep_eq insert_iff finite_union_image_member split_paired_Ex case_prod_conv
      children_root; blast)
  have ok: "(finite_relation_functional B \<and> fBex K (\<lambda>(H,Z). fimage fst B=fimage fst H \<and>
        fBall (fimage fst B) (\<lambda>s. fBex Z (\<lambda>(r,y). r=s \<and> fst (snd y))))) \<longleftrightarrow>
      finite_checks_schema_proof P (Schema_Proof c V B) d t"
  proof (cases "finite_relation_functional B")
    case False
    then show ?thesis by (simp only: finite_checks_schema_proof_node) simp
  next
    case True
    have sv: "p=q" if "(s,p) |\<in>| B" "(s,q) |\<in>| B" for s p q
      using True that by (auto simp: finite_relation_functional_correct single_valued_def)
    have inner: "fBall (fimage fst B) (\<lambda>s. fBex (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H))
          (\<lambda>(r,y). r=s \<and> fst (snd y))) \<longleftrightarrow>
        (\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x))" for H
    proof
      assume all: "fBall (fimage fst B) (\<lambda>s. fBex (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H))
          (\<lambda>(r,y). r=s \<and> fst (snd y)))"
      show "\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)"
      proof (intro allI impI)
        fix s p assume sp: "(s,p) |\<in>| B"
        have "s |\<in>| fimage fst B" using sp by (force simp: fimage.rep_eq)
        then have "fBex (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)) (\<lambda>(r,y). r=s \<and> fst (snd y))"
          by (rule bspec[OF all])
        then obtain w where w: "w |\<in>| fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)"
          and holds: "(\<lambda>(r,y). r=s \<and> fst (snd y)) w" by (rule bexE)
        then obtain r q e x where row: "(r,q,e,x) |\<in>| finite_keyed_product B H" and ww: "w=(r,orig q e x)"
          by (auto simp: fimage.rep_eq)
        have rs: "r=s" and checked: "finite_checks_schema_proof P q e x"
          using holds by (simp_all add: ww orig_def)
        have "(r,q) |\<in>| B" "(r,e,x) |\<in>| H" using row by (simp_all add: finite_keyed_product_member)
        then show "\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x"
          using sv[OF sp] checked rs by auto
      qed
    next
      assume all: "\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)"
      show "fBall (fimage fst B) (\<lambda>s. fBex (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H))
          (\<lambda>(r,y). r=s \<and> fst (snd y)))"
      proof
        fix s assume "s |\<in>| fimage fst B"
        then obtain p where sp: "(s,p) |\<in>| B" by (auto simp: fimage.rep_eq)
        then obtain e x where ex: "(s,e,x) |\<in>| H" and checked: "finite_checks_schema_proof P p e x"
          using all by blast
        have row: "(s,p,e,x) |\<in>| finite_keyed_product B H" using sp ex by (simp add: finite_keyed_product_member)
        have mem: "(s,orig p e x) |\<in>| fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)"
          unfolding fimage.rep_eq by (rule rev_image_eqI[OF row]) simp
        have ok_child: "fst (snd (orig p e x))" using checked by (simp add: orig_def)
        show "fBex (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H))
            (\<lambda>(r,y). r=s \<and> fst (snd y))"
          using mem ok_child by (intro bexI[of _ "(s,orig p e x)"]) simp_all
      qed
    qed
    have "fBex K (\<lambda>(H,Z). fimage fst B=fimage fst H \<and>
        fBall (fimage fst B) (\<lambda>s. fBex Z (\<lambda>(r,y). r=s \<and> fst (snd y)))) \<longleftrightarrow>
      (\<exists>H. H |\<in>| Ro \<and> fimage fst B=fimage fst H \<and>
        (\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)))"
      using inner by (auto simp: K_def fimage.rep_eq)
    then show ?thesis using True by (simp only: finite_checks_schema_proof_node Ro_def; blast)
  qed
  have K_member: "(H,Z) |\<in>| K \<longleftrightarrow> H |\<in>| Ro \<and>
      Z=fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)" for H Z
    by (auto simp: K_def fimage.rep_eq)
  have Z_member: "(s,y) |\<in>| fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H) \<longleftrightarrow>
      (\<exists>q e x. y=orig q e x \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H)" for s y H
    by (simp only: fimage.rep_eq image_iff Bex_def split_paired_Ex case_prod_conv prod.inject
      finite_keyed_product_member; blast)
  have rows: "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). G s y) Z)) K) \<longleftrightarrow>
      (\<exists>H s q e x. H |\<in>| Ro \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H \<and> z |\<in>| G s (orig q e x))" for z G
  proof
    assume "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). G s y) Z)) K)"
    then obtain a where a: "a |\<in>| K" and za: "z |\<in>| (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). G s y) Z)) a"
      by (rule finite_union_image_memberE)
    obtain H Z where aHZ: "a=(H,Z)" by (cases a)
    have H: "H |\<in>| Ro" and Z: "Z=fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)"
      using a unfolding aHZ K_member by blast+
    have "z |\<in>| ffUnion (fimage (\<lambda>(s,y). G s y) Z)" using za by (simp only: aHZ case_prod_conv)
    then obtain b where b: "b |\<in>| Z" and zb: "z |\<in>| (\<lambda>(s,y). G s y) b"
      by (rule finite_union_image_memberE)
    obtain s y where bsy: "b=(s,y)" by (cases b)
    obtain q e x where y: "y=orig q e x" and sq: "(s,q) |\<in>| B" and sex: "(s,e,x) |\<in>| H"
      using b unfolding bsy Z Z_member by blast
    have "z |\<in>| G s (orig q e x)" using zb by (simp only: bsy y case_prod_conv)
    then show "\<exists>H s q e x. H |\<in>| Ro \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H \<and> z |\<in>| G s (orig q e x)"
      using H sq sex by blast
  next
    assume "\<exists>H s q e x. H |\<in>| Ro \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H \<and> z |\<in>| G s (orig q e x)"
    then obtain H s q e x where H: "H |\<in>| Ro" and sq: "(s,q) |\<in>| B" and sex: "(s,e,x) |\<in>| H"
      and z: "z |\<in>| G s (orig q e x)" by blast
    have b: "(s,orig q e x) |\<in>| fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)"
      unfolding Z_member using sq sex by blast
    have a: "(H,fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)) |\<in>| K"
      unfolding K_member using H by blast
    have "z |\<in>| ffUnion (fimage (\<lambda>(s,y). G s y) (fimage (\<lambda>(s,q,e,x). (s,orig q e x)) (finite_keyed_product B H)))"
      by (rule finite_union_image_memberI[OF b]) (simp only: case_prod_conv z)
    then show "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y). G s y) Z)) K)"
      by (intro finite_union_image_memberI[OF a]) (simp only: case_prod_conv)
  qed

  have paths: "finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
        fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K))=
      finite_schema_proof_paths P (Schema_Proof c V B) d t"
  proof (rule fset_eqI)
    fix z
    have mine: "z |\<in>| finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K)) \<longleftrightarrow> z=([],n) \<or>
        (\<exists>H s q e x. H |\<in>| Ro \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H \<and>
          z |\<in>| fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x))"
      by (simp only: finsert.rep_eq insert_iff rows orig_def fst_conv snd_conv)
    show "z |\<in>| finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K)) \<longleftrightarrow>
        z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t"
    proof
      assume "z |\<in>| finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K))"
      then consider "z=([],n)" | H s q e x where "H |\<in>| Ro" "(s,q) |\<in>| B" "(s,e,x) |\<in>| H"
          "z |\<in>| fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x)"
        unfolding mine by blast
      then show "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t"
      proof cases
        case 1
        then show ?thesis unfolding paths_root by blast
      next
        case (2 H s q e x)
        have "\<exists>ss m. z=(s#ss,m) \<and> (ss,m) |\<in>| finite_schema_proof_paths P q e x"
          using 2(4) by (simp only: finite_cons_member)
        then obtain ss m where "z=(s#ss,m)" "(ss,m) |\<in>| finite_schema_proof_paths P q e x" by blast
        then show ?thesis unfolding paths_root using 2 by blast
      qed
    next
      assume "z |\<in>| finite_schema_proof_paths P (Schema_Proof c V B) d t"
      then consider "z=([],n)" | s q e x ss m H where "z=(s#ss,m)" "(s,q) |\<in>| B" "H |\<in>| Ro" "(s,e,x) |\<in>| H"
          "(ss,m) |\<in>| finite_schema_proof_paths P q e x"
        unfolding paths_root by blast
      then show "z |\<in>| finsert ([],n) (ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          fimage (map_prod (Cons s) id) (fst (snd (snd y)))) Z)) K))"
      proof cases
        case 1
        then show ?thesis unfolding mine by blast
      next
        case (2 s q e x ss m H)
        then have "z |\<in>| fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x)"
          by (simp only: finite_cons_member) blast
        then show ?thesis unfolding mine using 2 by blast
      qed
    qed
  qed
  have discharges: "ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
        finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K)=
      finite_schema_flat_discharges P (finite_schema_proof_positions P (Schema_Proof c V B) d t)"
  proof (rule fset_eqI)
    fix z
    have mine: "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K) \<longleftrightarrow>
        (\<exists>H s q e x. H |\<in>| Ro \<and> (s,q) |\<in>| B \<and> (s,e,x) |\<in>| H \<and>
          (z=((n,s),q,e,x) \<or> z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P q e x)))"
      by (simp only: rows orig_def fst_conv snd_conv finsert.rep_eq insert_iff)
    obtain m s' q' e' x' where shape: "z=((m,s'),q',e',x')" by (metis prod.collapse)
    have root: "z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P (Schema_Proof c V B) d t) \<longleftrightarrow>
        (m=n \<or> (\<exists>s q e x. (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          m |\<in>| finite_schema_proof_positions P q e x)) \<and> (s',q',e',x') |\<in>| finite_schema_proof_children P m"
      by (simp only: shape finite_schema_flat_discharge_member positions_root)
    show "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K) \<longleftrightarrow>
        z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P (Schema_Proof c V B) d t)"
    proof
      assume "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K)"
      then obtain H s q e x where H: "H |\<in>| Ro" and sq: "(s,q) |\<in>| B" and sex: "(s,e,x) |\<in>| H"
        and row: "z=((n,s),q,e,x) \<or> z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P q e x)"
        unfolding mine by blast
      have child: "(s,q,e,x) |\<in>| finite_schema_proof_children P n" unfolding children_root using sq H sex by blast
      from row show "z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P (Schema_Proof c V B) d t)"
      proof
        assume "z=((n,s),q,e,x)"
        then have "m=n" "s'=s" "q'=q" "e'=e" "x'=x" using shape by simp_all
        then show ?thesis unfolding root using child by simp
      next
        assume "z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P q e x)"
        then have "m |\<in>| finite_schema_proof_positions P q e x" "(s',q',e',x') |\<in>| finite_schema_proof_children P m"
          unfolding shape finite_schema_flat_discharge_member by blast+
        then show ?thesis unfolding root using sq H sex by blast
      qed
    next
      assume "z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P (Schema_Proof c V B) d t)"
      then have pos: "m=n \<or> (\<exists>s q e x. (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          m |\<in>| finite_schema_proof_positions P q e x)"
        and ch: "(s',q',e',x') |\<in>| finite_schema_proof_children P m" unfolding root by blast+
      from pos show "z |\<in>| ffUnion (fimage (\<lambda>(H,Z). ffUnion (fimage (\<lambda>(s,y).
          finsert ((n,s),fst y) (snd (snd (snd y)))) Z)) K)"
      proof
        assume mn: "m=n"
        have "(s',q',e',x') |\<in>| finite_schema_proof_children P n" using ch mn by simp
        then have sq: "(s',q') |\<in>| B" and H: "\<exists>H. H |\<in>| Ro \<and> (s',e',x') |\<in>| H"
          by (simp_all only: children_root)
        have z: "z=((n,s'),q',e',x')" using shape mn by simp
        show ?thesis unfolding mine using sq H z by blast
      next
        assume "\<exists>s q e x. (s,q) |\<in>| B \<and> (\<exists>H. H |\<in>| Ro \<and> (s,e,x) |\<in>| H) \<and>
          m |\<in>| finite_schema_proof_positions P q e x"
        then obtain s q e x H where sq: "(s,q) |\<in>| B" and H: "H |\<in>| Ro" and sex: "(s,e,x) |\<in>| H"
          and pm: "m |\<in>| finite_schema_proof_positions P q e x" by blast
        have "z |\<in>| finite_schema_flat_discharges P (finite_schema_proof_positions P q e x)"
          unfolding shape finite_schema_flat_discharge_member using pm ch by blast
        then show ?thesis unfolding mine using sq H sex by blast
      qed
    qed
  qed
  show ?case by (simp only: unfolded ok paths discharges) (simp only: n_def)
qed

text \<open>The paths, positions, discharges and coordinates of a certificate, read off its premise readings.\<close>

definition finite_certificate_paths where
  "finite_certificate_paths P p d t=fst (snd (snd (finite_certificate_premises P p d t)))"

definition finite_certificate_positions where
  "finite_certificate_positions P p d t=fimage snd (finite_certificate_paths P p d t)"

definition finite_certificate_discharges where
  "finite_certificate_discharges P p d t=snd (snd (snd (finite_certificate_premises P p d t)))"

definition finite_certificate_coordinates where
  "finite_certificate_coordinates P p d t=finite_representative_map (finite_certificate_paths P p d t)"

theorem finite_certificate_premises_checked:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "fst (snd (finite_certificate_premises P p d t))"
    "finite_certificate_paths P p d t=finite_schema_proof_paths P p d t"
    "finite_certificate_positions P p d t=finite_schema_proof_positions P p d t"
    "finite_certificate_discharges P p d t=finite_schema_flat_discharges P (finite_schema_proof_positions P p d t)"
    "finite_certificate_coordinates P p d t=finite_schema_proof_coordinates P (p,d,t)"
  using finite_certificate_premises_exact[OF finite_checked_certificate_formed[OF checked]] checked
  by (simp_all add: finite_certificate_paths_def finite_certificate_positions_def
    finite_certificate_discharges_def finite_certificate_coordinates_def
    finite_schema_proof_paths_projection finite_schema_proof_coordinates_def)

section \<open>The certificate graph at a read program\<close>

text \<open>
  The certificate graph after its program is read: the call term's formation checked once, at the entry,
  and the premise readings computed once, from which the check, the positions, the discharges and the
  coordinates are read; the coordinates are computed once and serve both the placed graph and the
  returned map. Its body is the operation where the term's formation is established.
\<close>

definition finite_certificate_graph_body where
  "finite_certificate_graph_body E P p d t=(case finite_certificate_premises P p d t of (n,checked,X,D) \<Rightarrow>
    if checked then (let M=finite_representative_map X in
      map_option (\<lambda>(F,N,s,H). (F,finite_edge_compose M N,s,H))
        (finite_extend_native_graph E (finite_mapped_graph M (finite_positioned_graph finite_schema_proof_owner
          \<lparr>finite_graph_inferences=fimage (\<lambda>m. (m,finite_schema_proof_kind (fst m))) (fimage snd X),
           finite_graph_discharges=D\<rparr>)) []))
    else None)"

definition finite_certificate_graph where
  "finite_certificate_graph E P p d t=(if finite_term_formed t then finite_certificate_graph_body E P p d t else None)"

lemma finite_certificate_graph_checked:
  "checked_premise (finite_certificate_graph E P p d) finite_term_formed (finite_certificate_graph_body E P p d)
    (\<lambda>_. None)"
  by unfold_locales (simp_all add: finite_certificate_graph_def)

theorem finite_certificate_graph_exact:
  assumes system: "finite_system_formed P"
  shows "finite_certificate_graph E P p d t=(if finite_checks_schema_proof P p d t then
      map_option (\<lambda>(F,N,s,H). (F,finite_edge_compose (finite_schema_proof_coordinates P (p,d,t)) N,s,H))
        (finite_extend_native_graph E (finite_source_coordinate_graph P (p,d,t)) [])
      else None)"
proof (cases "finite_term_formed t")
  case True
  show ?thesis
    by (simp add: finite_certificate_graph_def finite_certificate_graph_body_def True
      finite_certificate_premises_exact[OF system True] finite_schema_proof_coordinates_def
      finite_source_coordinate_graph_def finite_source_proof_graph_def finite_schema_proof_graph_def
      finite_schema_proof_paths_projection Let_def)
next
  case False
  have "\<not>finite_checks_schema_proof P p d t"
  proof
    assume "finite_checks_schema_proof P p d t"
    then have "finite_term_formed t" by (rule finite_checked_certificate_formed(2))
    with False show False by blast
  qed
  then show ?thesis using False by (simp add: finite_certificate_graph_def)
qed

theorem finite_native_certificate_graph_premises:
  "finite_native_certificate_graph E u r p d t=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> finite_certificate_graph E P p d t)"
proof (cases "finite_native_source E u r")
  case None
  then show ?thesis by (simp add: finite_native_certificate_graph_def)
next
  case (Some P)
  have "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using Some by (simp only: finite_native_source_correct)
  then have "schema_system_formed (decode_finite_system P)" by (rule native_package_system_formed)
  then have system: "finite_system_formed P" by (simp only: finite_system_formed_correct)
  show ?thesis using Some by (simp add: finite_native_certificate_graph_def finite_certificate_graph_exact[OF system])
qed

text \<open>
  No recorded state expands @{const finite_native_certificate_graph}: the seed's roots are readers and the
  machinery's constituents stand one definition below its notions, and neither context imports this
  theory. Its code equation is therefore stated through the graph at the read program.
\<close>

declare finite_native_certificate_graph_def [code del]
lemmas finite_native_certificate_graph_premises_code [code] = finite_native_certificate_graph_premises

export_code finite_certificate_premises finite_certificate_graph finite_native_certificate_graph checking SML

end
