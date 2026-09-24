theory Development_Seed_Referenced_Publication
  imports Development_Seed_Publication Represented_Snapshot_Transactions Presented_Publication_Values
    Shared_Term_Words
begin

section \<open>The seed round holds its targets once, where they are made\<close>

text \<open>
  The round is stated once over its representation (\<open>development_seed_round\<close>, in
  \<open>Development_Seed_Publication\<close>), its plain instance the older statement of the round. At the reference
  representation a generation holds
  references into the round's table, the first-occurrence table of the targets the round makes, each
  entered once where it is made: the loci and the payload and cause of every prepared judgment before the
  parallel rows, and a target made inside a row whose judgment was not prepared after the rows, by value.
\<close>






subsection \<open>The reference representation\<close>

text \<open>
  The round's table is the first-occurrence table of the targets it makes, built by
  \<open>keyed_reference_step\<close> at a target's rows key. The loci of every problem and of the selection and the
  payload and cause of every prepared judgment are entered before the parallel rows; a recording made with
  a prepared judgment holds that judgment's references. After the rows, the loci of the made generations are
  looked up and the payload and cause of a generation whose judgment was not prepared are entered by value.
\<close>

type_synonym seed_state = "(compared_artifact_rows\<times>local_address option,nat) rbt\<times>nat\<times>finite_exact_target list"


definition seed_cause :: "finite_exact_artifact\<times>development_policy_judgment \<Rightarrow> finite_exact_artifact" where
  "seed_cause v=snd (snd (snd (snd (snd (snd (snd (snd v)))))))"

lemma seed_payload_generation_using:
  "development_payload_generation_using construct judge t H l rows=
    Option.bind (judge t) (\<lambda>v. construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows)"
  by (simp add: development_payload_generation_using_def seed_cause_def case_prod_unfold)

definition seed_judged_targets :: "seed_judged \<Rightarrow> finite_exact_target list" where
  "seed_judged_targets j=(case j of None \<Rightarrow> [] | Some v \<Rightarrow> [Finite_Whole (fst v),Finite_Whole (seed_cause v)])"

fun seed_prepared_refs :: "nat list \<Rightarrow> (finite_factor_term\<times>seed_judged) list \<Rightarrow>
    (finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list" where
  "seed_prepared_refs ns []=[]"
| "seed_prepared_refs ns ((t,None)#cs)=(t,None,None)#seed_prepared_refs ns cs"
| "seed_prepared_refs ns ((t,Some v)#cs)=(t,Some v,Some (ns!0,ns!1))#seed_prepared_refs (drop 2 ns) cs"

definition seed_loci :: "development_problem list \<Rightarrow> finite_exact_target list" where
  "seed_loci ps=List.map_filter id (development_data_target development_selection_locus#
     concat (map (\<lambda>p. [development_locus_target Development_Problem_Role p,
       development_locus_target Development_Issue_Role p]) ps))"

definition seed_prepared :: "finite_factor_term list \<Rightarrow> (finite_factor_term\<times>seed_judged) list" where
  "seed_prepared keys=Parallel.map (\<lambda>t. (t,development_payload_judgment t)) (remdups keys)"

definition seed_lookup :: "(finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list \<Rightarrow> finite_factor_term \<Rightarrow>
    seed_judged\<times>(nat\<times>nat) option" where
  "seed_lookup cs t=(case map_of cs t of Some v \<Rightarrow> v | None \<Rightarrow> (development_payload_judgment t,None))"

definition seed_made_targets :: "(nat\<times>nat) option seed_made \<Rightarrow> finite_exact_target list" where
  "seed_made_targets m=(case fst m of None \<Rightarrow> [] | Some (B,u,G) \<Rightarrow> generation_locus G#
     (case snd m of Some (Some ab) \<Rightarrow> [] | _ \<Rightarrow> [generation_payload G,generation_cause G]))"

definition seed_made_rep :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made \<Rightarrow> nat generation_structure list \<Rightarrow>
    nat generation_structure option" where
  "seed_made_rep ns m ps=(case fst m of None \<Rightarrow> None | Some (B,u,G) \<Rightarrow> Some (case snd m of
     Some (Some (a,b)) \<Rightarrow> Generation (ns!0) (fset_of_list ps) a b
   | _ \<Rightarrow> Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2)))"

fun seed_consume_list :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made list \<Rightarrow> nat generation_structure option list" where
  "seed_consume_list ns []=[]"
| "seed_consume_list ns (m#ms)=seed_made_rep ns m []#seed_consume_list (drop (length (seed_made_targets m)) ns) ms"

definition seed_row_targets :: "development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow> finite_exact_target list" where
  "seed_row_targets row=(case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow>
     seed_made_targets S@seed_made_targets Q@seed_made_targets G@seed_made_targets H)"

definition seed_row_rep :: "nat generation_structure option list \<Rightarrow> nat list \<Rightarrow>
    development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>
      nat generation_structure option" where
  "seed_row_rep ireps ns row=(case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow> let
     Ir=Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd;
     n1=drop (length (seed_made_targets S)) ns; Sr=seed_made_rep ns S [];
     n2=drop (length (seed_made_targets Q)) n1; Qr=seed_made_rep n1 Q (List.map_filter id [Ir,Sr]);
     n3=drop (length (seed_made_targets G)) n2; Gr=seed_made_rep n2 G (map (\<lambda>x. the Qr) rG);
     Hr=seed_made_rep n3 H (map (\<lambda>x. the Qr) rH)
   in (Ir,Qr,Gr,Hr))"

fun seed_rows_rep :: "nat generation_structure option list \<Rightarrow> nat list \<Rightarrow>
    (development_problem\<times>(nat\<times>nat) option seed_row_made) list \<Rightarrow>
    (nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>
      nat generation_structure option) list" where
  "seed_rows_rep ireps ns []=[]"
| "seed_rows_rep ireps ns (row#rows)=seed_row_rep ireps ns row#
     seed_rows_rep ireps (drop (length (seed_row_targets row)) ns) rows"

definition seed_round_targets :: "(nat\<times>nat) option seed_made_round \<Rightarrow> finite_exact_target list" where
  "seed_round_targets m=(case m of (incs,sel,rows) \<Rightarrow>
     concat (map seed_made_targets incs)@seed_made_targets sel@concat (map seed_row_targets rows))"

definition seed_reps_of :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made_round \<Rightarrow> nat seed_reps" where
  "seed_reps_of ns m=(case m of (incs,sel,rows) \<Rightarrow> let
     ireps=seed_consume_list ns incs;
     n1=drop (length (concat (map seed_made_targets incs))) ns;
     n2=drop (length (seed_made_targets sel)) n1
   in (ireps,seed_made_rep n1 sel [],seed_rows_rep ireps n2 rows))"

definition seed_reference_reps :: "seed_state \<Rightarrow> (nat\<times>nat) option seed_made_round \<Rightarrow>
    nat seed_reps\<times>finite_exact_target list" where
  "seed_reference_reps q0 m=(case keyed_reference_sequence finite_target_key (seed_round_targets m) q0 of (ns,q) \<Rightarrow>
     (seed_reps_of ns m,rev (snd (snd q))))"

definition seed_reference_pub :: "finite_exact_target list \<Rightarrow> nat represented_snapshot \<Rightarrow>
    (nat generation_structure option\<times>nat generation_structure option) list \<Rightarrow> nat represented_transaction_result option list" where
  "seed_reference_pub T S=(if represented_snapshot_loci_formed S
     then represented_locus_publications_body (\<lambda>i. finite_target_formed (T!i)) S else map (\<lambda>q. None))"

definition seed_prepared_state :: "development_seed_decisions option \<Rightarrow>
    (finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list\<times>seed_state" where
  "seed_prepared_state decisions=(let
     cache=seed_prepared (development_seed_family_keys@development_seed_decision_keys decisions);
     entered=keyed_reference_sequence finite_target_key (seed_loci development_seed_problems@concat (map (\<lambda>(t,j). seed_judged_targets j) cache))
       (RBT.empty,0,[])
   in (seed_prepared_refs (drop (length (seed_loci development_seed_problems)) (fst entered)) cache,snd entered))"

definition development_seed_reference_round :: "development_problem fset \<Rightarrow>
    (nat,nat represented_transaction_result) seed_round\<times>finite_exact_target list" where
  "development_seed_reference_round A=(let decisions=development_seed_decisions A; prepared=seed_prepared_state decisions
   in development_seed_round (seed_lookup (fst prepared)) finite_construct_formed_cause_generation
     finite_construct_formed_cause_generation
     (seed_reference_reps (snd prepared)) seed_reference_pub decisions)"

subsection \<open>Every recorded generation is represented\<close>

definition seed_made_valid :: "finite_exact_target list \<Rightarrow> development_generation_row list \<Rightarrow>
    (nat\<times>nat) option seed_made \<Rightarrow> bool" where
  "seed_made_valid T rows m \<longleftrightarrow> (\<forall>B u G. fst m=Some (B,u,G) \<longrightarrow>
     generation_predecessors G=fset_of_list (map snd rows) \<and>
     (\<forall>a b. snd m=Some (Some (a,b)) \<longrightarrow>
       value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)))"

lemma seed_made_valid_preserved:
  assumes valid: "seed_made_valid T rows m"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "seed_made_valid T' rows m"
  using valid kept by (auto simp: seed_made_valid_def)


lemma seed_made_rep_represents:
  assumes valid: "seed_made_valid T rows m"
    and reads: "value_reference_reads T ns (seed_made_targets m)"
    and preds: "list_all2 (table_represented_generation T) ps (map snd rows)"
  shows "rel_option (table_represented_generation T) (seed_made_rep ns m ps) (seed_made_generation m)"
proof (cases "fst m")
  case None
  then show ?thesis by (simp add: seed_made_rep_def seed_made_generation_def)
next
  case (Some x)
  obtain B u G where x: "x=(B,u,G)" by (cases x)
  have made: "fst m=Some (B,u,G)" using Some x by simp
  have gen: "seed_made_generation m=Some G" by (simp add: seed_made_generation_def made)
  have family: "fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)=generation_predecessors G"
    using valid made table_represented_generation_list(1)[OF preds] by (simp add: seed_made_valid_def)
  note inside=table_represented_generation_list(2)[OF preds]
  obtain l Q p c where G: "G=Generation l Q p c" by (cases G)
  have represented: "rel_option (table_represented_generation T) (Some (Generation k (fset_of_list ps) a b)) (Some G)"
    if k: "value_reference_read T k=Some l" and a: "value_reference_read T a=Some p" and b: "value_reference_read T b=Some c"
    for k a b
  proof -
    have bounds: "k<length T" "T!k=l" "a<length T" "T!a=p" "b<length T" "T!b=c"
      using k a b by (auto simp: value_reference_read_def split: if_splits)
    have "G=Generation (T!k) (fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)) (T!a) (T!b)"
      using bounds family by (simp add: G)
    then show ?thesis using table_represented_generation_intro[OF bounds(1,3,5) inside] by simp
  qed
  have three: "value_reference_read T (ns!0)=Some l \<and> value_reference_read T (ns!1)=Some p \<and>
      value_reference_read T (ns!2)=Some c" if targets: "seed_made_targets m=[l,p,c]"
    using reads unfolding targets value_reference_reads_def by (auto simp: less_Suc_eq numeral_eq_Suc)
  show ?thesis
  proof (cases "snd m")
    case (Some k)
    note token=this
    show ?thesis
    proof (cases k)
      case (Some ab)
      obtain a b where ab: "ab=(a,b)" by (cases ab)
      have targets: "seed_made_targets m=[l]" by (simp add: seed_made_targets_def made token Some ab G)
      have locus: "value_reference_read T (ns!0)=Some l"
        using reads by (simp add: targets value_reference_reads_cons)
      have fields: "value_reference_read T a=Some p" "value_reference_read T b=Some c"
        using valid made token Some ab by (simp_all add: seed_made_valid_def G)
      have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) a b)"
        by (simp add: seed_made_rep_def made token Some ab)
      then show ?thesis using represented[OF locus fields] gen by simp
    next
      case None
      have targets: "seed_made_targets m=[l,p,c]" by (simp add: seed_made_targets_def made token None G)
      have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2))"
        by (simp add: seed_made_rep_def made token None)
      then show ?thesis using three[OF targets] represented gen by simp
    qed
  next
    case None
    have targets: "seed_made_targets m=[l,p,c]" by (simp add: seed_made_targets_def made None G)
    have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2))"
      by (simp add: seed_made_rep_def made None)
    then show ?thesis using three[OF targets] represented gen by simp
  qed
qed

lemma seed_made_rep_none: "fst m=None \<Longrightarrow> rel_option (table_represented_generation T) (seed_made_rep ns m ps) (seed_made_generation m)"
  by (simp add: seed_made_rep_def seed_made_generation_def)

subsection \<open>Every recording of the reference round is valid\<close>

definition seed_construct_core :: "development_constructor \<Rightarrow> bool" where
  "seed_construct_core construct \<longleftrightarrow> (\<forall>E l p c rows B u G. construct E l p c rows=Some (B,u,G) \<longrightarrow>
     G=Generation l (fset_of_list (map snd rows)) p c)"

lemma seed_construct_core_formed_cause: "seed_construct_core finite_construct_formed_cause_generation"
  by (auto simp: seed_construct_core_def finite_construct_formed_cause_generation_def finite_generation_record_body_def
    finite_generation_record_core_def split: if_splits)

lemma seed_construct_core_record: "seed_construct_core finite_construct_generation_record"
  unfolding seed_construct_core_def
proof (intro allI impI)
  fix E l p c rows B u G
  assume made: "finite_construct_generation_record E l p c rows=Some (B,u,G)"
  show "G=Generation l (fset_of_list (map snd rows)) p c"
    using finite_construct_generation_record_correct(2)[OF made] by (simp add: finite_generation_record_core_def)
qed

definition seed_lookup_valid :: "finite_exact_target list \<Rightarrow> (finite_factor_term \<Rightarrow> seed_judged\<times>(nat\<times>nat) option) \<Rightarrow> bool" where
  "seed_lookup_valid T L \<longleftrightarrow> (\<forall>t. fst (L t)=development_payload_judgment t) \<and>
     (\<forall>t a b. snd (L t)=Some (a,b) \<longrightarrow> (\<exists>v. fst (L t)=Some v \<and>
       value_reference_read T a=Some (Finite_Whole (fst v)) \<and> value_reference_read T b=Some (Finite_Whole (seed_cause v))))"

lemma seed_lookup_valid_preserved:
  assumes valid: "seed_lookup_valid T L"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "seed_lookup_valid T' L"
  using valid kept unfolding seed_lookup_valid_def by blast

lemma seed_record_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "seed_made_valid T rows (seed_record L construct key H rows)"
proof (cases key)
  case None
  then show ?thesis by (simp add: seed_record_def seed_made_valid_def)
next
  case (Some lt)
  obtain l t where lt: "lt=(l,t)" by (cases lt)
  obtain j k where Lt: "L t=(j,k)" by (cases "L t")
  show ?thesis unfolding seed_made_valid_def
  proof (intro allI impI)
    fix B u G
    assume made: "fst (seed_record L construct key H rows)=Some (B,u,G)"
    then have bound: "Option.bind j (\<lambda>v. construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows)=Some (B,u,G)"
      by (simp add: seed_record_def Some lt Lt seed_payload_generation_using)
    then obtain v where j: "j=Some v"
      and built: "construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows=Some (B,u,G)"
      unfolding bind_eq_Some_conv by blast
    have G: "G=Generation l (fset_of_list (map snd rows)) (Finite_Whole (fst v)) (Finite_Whole (seed_cause v))"
      using core built by (simp add: seed_construct_core_def)
    show "generation_predecessors G=fset_of_list (map snd rows) \<and>
      (\<forall>a b. snd (seed_record L construct key H rows)=Some (Some (a,b)) \<longrightarrow>
        value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G))"
    proof
      show "generation_predecessors G=fset_of_list (map snd rows)" by (simp add: G)
      show "\<forall>a b. snd (seed_record L construct key H rows)=Some (Some (a,b)) \<longrightarrow>
        value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)"
      proof (intro allI impI)
        fix a b
        assume "snd (seed_record L construct key H rows)=Some (Some (a,b))"
        then have "snd (L t)=Some (a,b)" by (simp add: seed_record_def Some lt Lt)
        then obtain w where w: "fst (L t)=Some w" "value_reference_read T a=Some (Finite_Whole (fst w))"
          "value_reference_read T b=Some (Finite_Whole (seed_cause w))"
          using lookup unfolding seed_lookup_valid_def by blast
        have "w=v" using w(1) j Lt by simp
        then show "value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)"
          using w by (simp add: G)
      qed
    qed
  qed
qed

definition seed_row_valid :: "finite_exact_target list \<Rightarrow> development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow> bool" where
  "seed_row_valid T row \<longleftrightarrow> (case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow> seed_made_valid T [] S \<and>
     (\<forall>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<longrightarrow> (\<exists>Ig B1 us Sel u. I=Some Ig \<and> fst S=Some (B1,us,Sel) \<and>
        seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q) \<and>
       seed_made_valid T rG G \<and> (\<forall>x\<in>set rG. snd x=Qg) \<and> seed_made_valid T rH H \<and> (\<forall>x\<in>set rH. snd x=Qg)) \<and>
     (fst Q=None \<longrightarrow> fst G=None \<and> fst H=None))"

lemma seed_row_answer_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "fst Q=Some (B2,uq,Qg) \<Longrightarrow> seed_made_valid T (fst (seed_row_answer L construct r S' Q)) (snd (seed_row_answer L construct r S' Q)) \<and>
      (\<forall>x\<in>set (fst (seed_row_answer L construct r S' Q)). snd x=Qg)"
    and "fst Q=None \<Longrightarrow> fst (snd (seed_row_answer L construct r S' Q))=None"
proof -
  assume issued: "fst Q=Some (B2,uq,Qg)"
  show "seed_made_valid T (fst (seed_row_answer L construct r S' Q)) (snd (seed_row_answer L construct r S' Q)) \<and>
      (\<forall>x\<in>set (fst (seed_row_answer L construct r S' Q)). snd x=Qg)"
  proof (cases "development_answer_key development_seed_state r S'")
    case None
    then show ?thesis using issued by (simp add: seed_row_answer_def seed_made_valid_def)
  next
    case (Some lt)
    obtain l t where lt: "lt=(l,t)" by (cases lt)
    show ?thesis
      using issued Some seed_record_valid[OF core lookup]
      by (simp add: seed_row_answer_def lt development_answer_citations_def)
  qed
next
  assume "fst Q=None"
  then show "fst (snd (seed_row_answer L construct r S' Q))=None" by (simp add: seed_row_answer_def)
qed

lemma seed_row_made_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "seed_row_valid T (seed_row_made L construct xs selected issue)"
proof -
  obtain r reading where issue: "issue=(r,reading)" by (cases issue)
  show ?thesis
  proof (cases "development_seed_incumbent_of xs r")
    case None
    then show ?thesis by (simp add: issue seed_row_made_def seed_row_valid_def seed_made_valid_def)
  next
    case (Some inc)
    note found=this
    obtain B u I where inc: "inc=(B,u,I)" by (cases inc)
    let ?S="seed_row_selection L construct selected B"
    let ?Q="seed_row_issue L construct r reading u I ?S"
    have S: "seed_made_valid T [] ?S" unfolding seed_row_selection_def by (rule seed_record_valid[OF core lookup])
    have Q: "\<exists>Ig B1 us Sel u'. Some I=Some Ig \<and> fst ?S=Some (B1,us,Sel) \<and> seed_made_valid T [((u',[]),Ig),((us,[]),Sel)] ?Q"
      if "fst ?Q=Some q" for q
    proof (cases "fst ?S")
      case None
      then show ?thesis using that by (simp add: seed_row_issue_def)
    next
      case (Some x)
      obtain B1 us Sel where x: "x=(B1,us,Sel)" by (cases x)
      have "seed_made_valid T [((u,[]),I),((us,[]),Sel)] ?Q"
        using Some seed_record_valid[OF core lookup] by (simp add: seed_row_issue_def x)
      then show ?thesis using Some x by blast
    qed
    show ?thesis
      unfolding issue seed_row_made_def seed_row_valid_def prod.case found inc option.case Let_def
      using S Q seed_row_answer_valid[OF core lookup] by (auto simp del: prod.collapse)
  qed
qed

subsection \<open>The prepared references\<close>

lemma seed_prepared_refs_valid:
  "value_reference_reads T ns (concat (map (\<lambda>(t,j). seed_judged_targets j) cs)) \<Longrightarrow> x\<in>set (seed_prepared_refs ns cs) \<Longrightarrow>
    (fst x,fst (snd x))\<in>set cs \<and> (\<forall>a b. snd (snd x)=Some (a,b) \<longrightarrow> (\<exists>v. fst (snd x)=Some v \<and>
      value_reference_read T a=Some (Finite_Whole (fst v)) \<and> value_reference_read T b=Some (Finite_Whole (seed_cause v))))"
proof (induction ns cs rule: seed_prepared_refs.induct)
  case (1 ns)
  then show ?case by simp
next
  case (2 ns t cs)
  then show ?case by (auto simp: seed_judged_targets_def)
next
  case (3 ns t v cs)
  have reads: "value_reference_reads T ns ([Finite_Whole (fst v),Finite_Whole (seed_cause v)]@concat (map (\<lambda>(t,j). seed_judged_targets j) cs))"
    using "3.prems"(1) by (simp add: seed_judged_targets_def)
  have head: "value_reference_reads T ns [Finite_Whole (fst v),Finite_Whole (seed_cause v)]"
    and rest: "value_reference_reads T (drop 2 ns) (concat (map (\<lambda>(t,j). seed_judged_targets j) cs))"
    using reads[unfolded value_reference_reads_append] by (simp_all add: numeral_2_eq_2)
  have h: "value_reference_read T (ns!0)=Some (Finite_Whole (fst v))" "value_reference_read T (ns!1)=Some (Finite_Whole (seed_cause v))"
    using head by (auto simp: value_reference_reads_def less_Suc_eq numeral_eq_Suc)
  show ?case
  proof (cases "x=(t,Some v,Some (ns!0,ns!1))")
    case True
    then show ?thesis using h by simp
  next
    case False
    then have "x\<in>set (seed_prepared_refs (drop 2 ns) cs)" using "3.prems"(2) by simp
    note later="3.IH"[OF rest this]
    then show ?thesis by simp
  qed
qed

lemma seed_prepared_state_valid:
  assumes prepared: "seed_prepared_state decisions=(cs,q0)"
  obtains T0 where "keyed_reference_state finite_target_key q0 T0" "distinct T0" "seed_lookup_valid T0 (seed_lookup cs)"
proof -
  let ?cache="seed_prepared (development_seed_family_keys@development_seed_decision_keys decisions)"
  let ?loci="seed_loci development_seed_problems"
  let ?xs="?loci@concat (map (\<lambda>(t,j). seed_judged_targets j) ?cache)"
  have exact: "fst (keyed_reference_sequence finite_target_key ?xs (RBT.empty,0,[]))=fst (value_reference_sequence ?xs [])"
    "keyed_reference_state finite_target_key (snd (keyed_reference_sequence finite_target_key ?xs (RBT.empty,0,[]))) (snd (value_reference_sequence ?xs []))"
    using keyed_reference_sequence_exact[OF finite_target_key_injective keyed_reference_state_empty] by blast+
  let ?T0="snd (value_reference_sequence ?xs [])"
  have q0: "q0=snd (keyed_reference_sequence finite_target_key ?xs (RBT.empty,0,[]))" and
    cs: "cs=seed_prepared_refs (drop (length ?loci) (fst (value_reference_sequence ?xs []))) ?cache"
    using prepared exact(1) by (simp_all add: seed_prepared_state_def Let_def)
  have reads: "value_reference_reads ?T0 (drop (length ?loci) (fst (value_reference_sequence ?xs []))) (concat (map (\<lambda>(t,j). seed_judged_targets j) ?cache))"
    using value_reference_reads_sequence[of ?xs "[]"] by (simp add: value_reference_reads_append)
  have judged: "(t,j)\<in>set ?cache \<Longrightarrow> j=development_payload_judgment t" for t j
    by (auto simp: seed_prepared_def Parallel.map_def)
  have "seed_lookup_valid ?T0 (seed_lookup cs)"
    unfolding seed_lookup_valid_def
  proof (intro conjI allI impI)
    fix t
    show "fst (seed_lookup cs t)=development_payload_judgment t"
    proof (cases "map_of cs t")
      case None
      then show ?thesis by (simp add: seed_lookup_def)
    next
      case (Some w)
      then have "(t,w)\<in>set cs" by (rule map_of_SomeD)
      then have "(t,fst w)\<in>set ?cache" using seed_prepared_refs_valid[OF reads] by (fastforce simp: cs)
      then show ?thesis using Some judged by (simp add: seed_lookup_def)
    qed
  next
    fix t a b
    assume token: "snd (seed_lookup cs t)=Some (a,b)"
    then obtain w where w: "map_of cs t=Some w" by (cases "map_of cs t") (simp_all add: seed_lookup_def)
    then have member: "(t,w)\<in>set cs" by (rule map_of_SomeD)
    show "\<exists>v. fst (seed_lookup cs t)=Some v \<and> value_reference_read ?T0 a=Some (Finite_Whole (fst v)) \<and>
        value_reference_read ?T0 b=Some (Finite_Whole (seed_cause v))"
      using seed_prepared_refs_valid[OF reads, of "(t,w)"] member token w by (simp add: cs seed_lookup_def)
  qed
  moreover have "distinct ?T0" using value_reference_sequence_distinct[of "[]" ?xs] by simp
  ultimately show ?thesis using that exact(2) q0 by blast
qed


subsection \<open>The represented rows\<close>

definition seed_quad_decode :: "finite_exact_target list \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option" where
  "seed_quad_decode T x=(map_option (map_generation_structure (\<lambda>i. T!i)) (fst x),
     map_option (map_generation_structure (\<lambda>i. T!i)) (fst (snd x)),
     map_option (map_generation_structure (\<lambda>i. T!i)) (fst (snd (snd x))),
     map_option (map_generation_structure (\<lambda>i. T!i)) (snd (snd (snd x))))"

definition seed_quad_rel :: "finite_exact_target list \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option \<Rightarrow> bool" where
  "seed_quad_rel T x y \<longleftrightarrow> rel_option (table_represented_generation T) (fst x) (fst y) \<and>
     rel_option (table_represented_generation T) (fst (snd x)) (fst (snd y)) \<and>
     rel_option (table_represented_generation T) (fst (snd (snd x))) (fst (snd (snd y))) \<and>
     rel_option (table_represented_generation T) (snd (snd (snd x))) (snd (snd (snd y)))"


lemma seed_row_rep_represents:
  assumes valid: "seed_row_valid T (p,I,S,Q,rG,G,rH,H)" and reads: "value_reference_reads T ns (seed_row_targets (p,I,S,Q,rG,G,rH,H))"
    and incumbent: "rel_option (table_represented_generation T)
      (Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd) I"
  shows "seed_quad_rel T (seed_row_rep ireps ns (p,I,S,Q,rG,G,rH,H)) (seed_row_plain_reps (p,I,S,Q,rG,G,rH,H))"
proof -
  let ?Ir="Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd"
  let ?n1="drop (length (seed_made_targets S)) ns"
  let ?n2="drop (length (seed_made_targets Q)) ?n1"
  let ?n3="drop (length (seed_made_targets G)) ?n2"
  let ?Sr="seed_made_rep ns S []"
  let ?Qr="seed_made_rep ?n1 Q (List.map_filter id [?Ir,?Sr])"
  have parts: "value_reference_reads T ns (seed_made_targets S)" "value_reference_reads T ?n1 (seed_made_targets Q)"
    "value_reference_reads T ?n2 (seed_made_targets G)" "value_reference_reads T ?n3 (seed_made_targets H)"
    using reads by (simp_all add: seed_row_targets_def value_reference_reads_append)
  have SV: "seed_made_valid T [] S"
    and QV: "\<And>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<Longrightarrow> (\<exists>Ig B1 us Sel u. I=Some Ig \<and> fst S=Some (B1,us,Sel) \<and>
        seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q) \<and>
       seed_made_valid T rG G \<and> (\<forall>x\<in>set rG. snd x=Qg) \<and> seed_made_valid T rH H \<and> (\<forall>x\<in>set rH. snd x=Qg)"
    and QN: "fst Q=None \<Longrightarrow> fst G=None \<and> fst H=None"
    using valid by (simp_all add: seed_row_valid_def)
  have Sr: "rel_option (table_represented_generation T) ?Sr (seed_made_generation S)"
    by (rule seed_made_rep_represents[OF SV parts(1)]) simp
  have Qr: "rel_option (table_represented_generation T) ?Qr (seed_made_generation Q)"
  proof (cases "fst Q")
    case None
    then show ?thesis by (rule seed_made_rep_none)
  next
    case (Some q)
    obtain B2 uq Qg where q: "q=(B2,uq,Qg)" by (cases q)
    obtain Ig B1 us Sel u where Ig: "I=Some Ig" and S1: "fst S=Some (B1,us,Sel)"
      and QV1: "seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q"
      using QV[of B2 uq Qg] Some q by blast
    obtain gI where gI: "?Ir=Some gI" "table_represented_generation T gI Ig"
      using incumbent Ig by (cases ?Ir) simp_all
    have "seed_made_generation S=Some Sel" by (simp add: seed_made_generation_def S1)
    then obtain gS where gS: "?Sr=Some gS" "table_represented_generation T gS Sel"
      using Sr by (cases ?Sr) simp_all
    have preds: "list_all2 (table_represented_generation T) (List.map_filter id [?Ir,?Sr]) (map snd [((u,[]),Ig),((us,[]),Sel)])"
      using gI gS by (simp add: List.map_filter_def)
    show ?thesis by (rule seed_made_rep_represents[OF QV1 parts(2) preds])
  qed
  have answer: "rel_option (table_represented_generation T) (seed_made_rep n A (map (\<lambda>x. the ?Qr) rA)) (seed_made_generation A)"
    if reads_A: "value_reference_reads T n (seed_made_targets A)"
      and valid_A: "\<And>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<Longrightarrow> seed_made_valid T rA A \<and> (\<forall>x\<in>set rA. snd x=Qg)"
      and none_A: "fst Q=None \<Longrightarrow> fst A=None"
    for n A rA
  proof (cases "fst Q")
    case None
    then show ?thesis using none_A by (simp add: seed_made_rep_none)
  next
    case (Some q)
    obtain B2 uq Qg where q: "q=(B2,uq,Qg)" by (cases q)
    have VA: "seed_made_valid T rA A" and cited: "\<forall>x\<in>set rA. snd x=Qg" using valid_A[of B2 uq Qg] Some q by simp_all
    have "seed_made_generation Q=Some Qg" by (simp add: seed_made_generation_def Some q)
    then obtain gQ where gQ: "?Qr=Some gQ" "table_represented_generation T gQ Qg" using Qr by (cases ?Qr) simp_all
    have preds: "list_all2 (table_represented_generation T) (map (\<lambda>x. the ?Qr) rA) (map snd rA)"
      using gQ cited by (simp add: list_all2_conv_all_nth)
    show ?thesis by (rule seed_made_rep_represents[OF VA reads_A preds])
  qed
  have Gr: "rel_option (table_represented_generation T) (seed_made_rep ?n2 G (map (\<lambda>x. the ?Qr) rG)) (seed_made_generation G)"
    by (rule answer[OF parts(3)]) (use QV QN in simp_all)
  have Hr: "rel_option (table_represented_generation T) (seed_made_rep ?n3 H (map (\<lambda>x. the ?Qr) rH)) (seed_made_generation H)"
    by (rule answer[OF parts(4)]) (use QV QN in simp_all)
  show ?thesis
    using incumbent Qr Gr Hr by (simp add: seed_row_rep_def seed_row_plain_reps_def seed_quad_rel_def Let_def add.assoc)
qed

lemma seed_consume_list_represents:
  "value_reference_reads T ns (concat (map seed_made_targets ms)) \<Longrightarrow> \<forall>m\<in>set ms. seed_made_valid T [] m \<Longrightarrow>
    list_all2 (rel_option (table_represented_generation T)) (seed_consume_list ns ms) (map seed_made_generation ms)"
proof (induction ms arbitrary: ns)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  have reads: "value_reference_reads T ns (seed_made_targets m)"
    "value_reference_reads T (drop (length (seed_made_targets m)) ns) (concat (map seed_made_targets ms))"
    using Cons.prems(1) by (simp_all add: value_reference_reads_append)
  have head: "rel_option (table_represented_generation T) (seed_made_rep ns m []) (seed_made_generation m)"
    using Cons.prems(2) by (intro seed_made_rep_represents[OF _ reads(1)]) simp_all
  show ?case using head Cons.IH[OF reads(2)] Cons.prems(2) by simp
qed

lemma seed_rows_rep_represents:
  "value_reference_reads T ns (concat (map seed_row_targets rows)) \<Longrightarrow> \<forall>row\<in>set rows. seed_row_valid T row \<Longrightarrow>
    \<forall>row\<in>set rows. rel_option (table_represented_generation T)
      (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ireps)) snd) (fst (snd row)) \<Longrightarrow>
    list_all2 (seed_quad_rel T) (seed_rows_rep ireps ns rows) (map seed_row_plain_reps rows)"
proof (induction rows arbitrary: ns)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  have reads: "value_reference_reads T ns (seed_row_targets row)"
    "value_reference_reads T (drop (length (seed_row_targets row)) ns) (concat (map seed_row_targets rows))"
    using Cons.prems(1) by (simp_all add: value_reference_reads_append)
  obtain p I S Q rG G rH H where row: "row=(p,I,S,Q,rG,G,rH,H)" by (metis prod.collapse)
  have head: "seed_quad_rel T (seed_row_rep ireps ns row) (seed_row_plain_reps row)"
    using Cons.prems(2,3) reads(1) by (simp add: row seed_row_rep_represents)
  show ?case using head Cons.IH[OF reads(2)] Cons.prems(2,3) by simp
qed


lemma seed_incumbent_find:
  "map_option (\<lambda>(B,u,G). G) (Option.bind (find (\<lambda>(p,x). p=a) (zip ps (map fst incs))) snd)=
    Option.bind (find (\<lambda>(q,z). q=a) (zip ps incs)) (\<lambda>(q,z). seed_made_generation z)"
proof (induction ps arbitrary: incs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases incs) (simp_all add: seed_made_generation_def)
qed

lemma seed_row_made_fields:
  shows "fst (seed_row_made L construct xs selected (r,reading))=fst r"
    and "fst (snd (seed_row_made L construct xs selected (r,reading)))=
      map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)"
proof -
  show "fst (seed_row_made L construct xs selected (r,reading))=fst r" by (simp add: seed_row_made_def)
  show "fst (snd (seed_row_made L construct xs selected (r,reading)))=
      map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)"
    by (cases "development_seed_incumbent_of xs r") (auto simp: seed_row_made_def Let_def)
qed


subsection \<open>The reference round decodes to the round\<close>

definition seed_round_decode :: "finite_exact_target list \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow>
    development_seed_publication" where
  "seed_round_decode T v=(case v of (S0,Sel,rows,results) \<Rightarrow>
     (map_option (decode_represented_snapshot (\<lambda>i. T!i)) S0,map_option (map_generation_structure (\<lambda>i. T!i)) Sel,
      map (\<lambda>(Q,G,H,rs,e). (map_option (map_generation_structure (\<lambda>i. T!i)) Q,
        map_option (map_generation_structure (\<lambda>i. T!i)) G,map_option (map_generation_structure (\<lambda>i. T!i)) H,
        map (map_option (decode_represented_result (\<lambda>i. T!i))) rs,e)) rows,
      map (map_option (decode_represented_result (\<lambda>i. T!i))) results))"


lemma seed_reference_pub_decoded:
  assumes distinct: "distinct T" and S: "represented_snapshot_targets S\<subseteq>{..<length T}"
    and ps: "represented_publications_targets ps\<subseteq>{..<length T}"
  shows "map (map_option (decode_represented_result (\<lambda>i. T!i))) (seed_reference_pub T S ps)=
    (if finite_snapshot_loci_formed (decode_represented_snapshot (\<lambda>i. T!i) S)
     then finite_locus_publications_body (decode_represented_snapshot (\<lambda>i. T!i) S) else map (\<lambda>q. None))
      (decode_represented_publications (\<lambda>i. T!i) ps)"
proof -
  have inj: "inj_on (\<lambda>i. T!i) {..<length T}" using distinct by (simp add: inj_on_nth)
  show ?thesis
    using represented_snapshot_loci_formed_decoded[OF inj S] represented_locus_publications_body_decoded[OF inj S ps]
    by (simp add: seed_reference_pub_def decode_represented_publications_def)
qed

lemma seed_list_targets:
  assumes rel: "list_all2 (rel_option (table_represented_generation T)) xs ys" and member: "Some g\<in>set xs"
  shows "set_generation_structure g\<subseteq>{..<length T}"
proof -
  obtain i where i: "i<length xs" "xs!i=Some g" using member in_set_conv_nth[of "Some g" xs] by blast
  have "rel_option (table_represented_generation T) (xs!i) (ys!i)" using rel i(1) by (simp add: list_all2_conv_all_nth)
  then show ?thesis using table_represented_generation_option(2) i(2) by fastforce
qed

lemma seed_snapshot_targets:
  assumes rel: "list_all2 (rel_option (table_represented_generation T)) xs ys" and listed: "those xs=Some gs"
  shows "represented_snapshot_targets (fset_of_list gs)\<subseteq>{..<length T}"
proof
  fix x
  assume "x\<in>represented_snapshot_targets (fset_of_list gs)"
  then obtain G where G: "G\<in>set gs" "x\<in>set_generation_structure G"
    by (auto simp: represented_snapshot_targets_def fset_of_list_elem)
  show "x\<in>{..<length T}" using seed_list_targets[OF rel those_member[OF listed G(1)]] G(2) by blast
qed

lemma seed_quad_targets:
  assumes rows: "list_all2 (seed_quad_rel T) rows rows'" and member: "x\<in>set rows"
  shows "\<forall>g\<in>set_option (fst x)\<union>set_option (fst (snd x))\<union>set_option (fst (snd (snd x)))\<union>set_option (snd (snd (snd x))).
    set_generation_structure g\<subseteq>{..<length T}"
proof -
  obtain i where i: "i<length rows" "rows!i=x" using member in_set_conv_nth[of x rows] by blast
  have "seed_quad_rel T x (rows'!i)" using rows i by (auto simp: list_all2_conv_all_nth)
  then show ?thesis unfolding seed_quad_rel_def using table_represented_generation_option(2) by blast
qed


theorem seed_round_assemble_decoded:
  assumes distinct: "distinct T"
    and ireps: "list_all2 (rel_option (table_represented_generation T)) ireps Is"
    and sel: "rel_option (table_represented_generation T) sel Sel"
    and rows: "list_all2 (seed_quad_rel T) rows rows'"
  shows "seed_round_decode T (seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub d)=
    seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) d"
proof -
  let ?dec="\<lambda>i::nat. T!i"
  let ?K="{..<length T}"
  let ?D="map_option (map_generation_structure ?dec)"
  let ?P="\<lambda>S. if finite_snapshot_loci_formed S then finite_locus_publications_body S else map (\<lambda>q. None)"
  let ?pubR="case map_option fset_of_list (those ireps) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> seed_reference_pub T S"
  let ?pubP="case map_option fset_of_list (those Is) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> ?P S"
  have inj: "inj_on ?dec ?K" using distinct by (simp add: inj_on_nth)
  have Is: "map ?D ireps=Is"
    using ireps by (induction rule: list_all2_induct) (simp_all add: table_represented_generation_option(1))
  have Sel: "?D sel=Sel" and Seltargets: "\<And>g. g\<in>set_option sel \<Longrightarrow> set_generation_structure g\<subseteq>?K"
    using table_represented_generation_option[OF sel] by simp_all
  have quad: "y=seed_quad_decode T x" if related: "seed_quad_rel T x y" for x y
  proof -
    have r: "rel_option (table_represented_generation T) (fst x) (fst y)" "rel_option (table_represented_generation T) (fst (snd x)) (fst (snd y))"
      "rel_option (table_represented_generation T) (fst (snd (snd x))) (fst (snd (snd y)))"
      "rel_option (table_represented_generation T) (snd (snd (snd x))) (snd (snd (snd y)))"
      using related by (simp_all add: seed_quad_rel_def)
    show ?thesis using table_represented_generation_option(1)[OF r(1)] table_represented_generation_option(1)[OF r(2)] table_represented_generation_option(1)[OF r(3)]
      table_represented_generation_option(1)[OF r(4)] by (simp add: seed_quad_decode_def prod_eq_iff)
  qed
  have rows': "rows'=map (seed_quad_decode T) rows"
    using rows by (induction rule: list_all2_induct) (simp_all add: quad)
  note Rtargets=seed_quad_targets[OF rows]
  have publish: "map (map_option (decode_represented_result ?dec)) (?pubR ps)=?pubP (decode_represented_publications ?dec ps)"
    if ps: "represented_publications_targets ps\<subseteq>?K" for ps
  proof (cases "those ireps")
    case None
    then show ?thesis by (simp add: Is[symmetric] those_map_option)
  next
    case (Some gs)
    note S=seed_snapshot_targets[OF ireps Some]
    have decoded: "decode_represented_snapshot ?dec (fset_of_list gs)=fset_of_list (map (map_generation_structure ?dec) gs)"
      by (simp add: decode_represented_snapshot_def fset_of_list_map)
    show ?thesis
      using seed_reference_pub_decoded[OF distinct S ps] Some
      by (simp add: Is[symmetric] those_map_option decoded)
  qed
  note targets_list=represented_publications_targets_bound
  have equal: "(map_option generation_payload (?D G)=map_option generation_payload (?D H)) \<longleftrightarrow>
      (map_option generation_payload G=map_option generation_payload H)"
    if G: "\<And>g. g\<in>set_option G \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and H: "\<And>g. g\<in>set_option H \<Longrightarrow> set_generation_structure g\<subseteq>?K" for G H
  proof (cases G)
    case None
    then show ?thesis by (cases H) simp_all
  next
    case (Some g)
    show ?thesis
    proof (cases H)
      case None
      then show ?thesis using Some by simp
    next
      case (Some h)
      have "generation_payload g\<in>?K" using G \<open>G=Some g\<close> generation_structure.set_sel by fastforce
      moreover have "generation_payload h\<in>?K" using H Some generation_structure.set_sel by fastforce
      ultimately show ?thesis using \<open>G=Some g\<close> Some inj by (simp add: generation_structure.map_sel inj_on_eq_iff)
    qed
  qed
  have row: "(\<lambda>(Q,G,H,rs,e). (?D Q,?D G,?D H,map (map_option (decode_represented_result ?dec)) rs,e))
      ((\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) x)=
    (\<lambda>(I,Q,G,H). (Q,G,H,?pubP [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (seed_quad_decode T x)"
    if x: "x\<in>set rows" for x
  proof -
    obtain I Q G H where shape: "x=(I,Q,G,H)" by (metis prod.collapse)
    have tI: "\<And>g. g\<in>set_option I \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tQ: "\<And>g. g\<in>set_option Q \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tG: "\<And>g. g\<in>set_option G \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tH: "\<And>g. g\<in>set_option H \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      using Rtargets[OF x] by (auto simp: shape)
    have pub: "map (map_option (decode_represented_result ?dec)) (?pubR [(None,Q),(I,G),(I,H)])=
        ?pubP [(None,?D Q),(?D I,?D G),(?D I,?D H)]"
      using publish[OF targets_list] tI tQ tG tH by (simp add: decode_represented_publications_def)
    show ?thesis using pub equal[OF tG tH] by (simp add: shape seed_quad_decode_def)
  qed
  have rowsmap: "map (\<lambda>(Q,G,H,rs,e). (?D Q,?D G,?D H,map (map_option (decode_represented_result ?dec)) rs,e))
      (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows)=
    map (\<lambda>(I,Q,G,H). (Q,G,H,?pubP [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (map (seed_quad_decode T) rows)"
    using row by simp
  have round_targets: "represented_publications_targets ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@
      map (\<lambda>(I,Q,G,H). (I,G)) rows)\<subseteq>?K"
    by (rule targets_list) (use Seltargets Rtargets in fastforce)
  have round_decoded: "decode_represented_publications ?dec ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@
      map (\<lambda>(I,Q,G,H). (I,G)) rows)=
    (None,Sel)#map (\<lambda>(I,Q,G,H). (None,Q)) (map (seed_quad_decode T) rows)@
      map (\<lambda>(I,Q,G,H). (I,G)) (map (seed_quad_decode T) rows)"
    by (simp add: decode_represented_publications_def Sel[symmetric] seed_quad_decode_def case_prod_unfold)
  have snapshot: "map_option (decode_represented_snapshot ?dec) (map_option fset_of_list (those ireps))=
      map_option fset_of_list (those Is)"
    by (cases "those ireps") (simp_all add: Is[symmetric] those_map_option decode_represented_snapshot_def fset_of_list_map)
  show ?thesis
  proof (cases d)
    case None
    show ?thesis
      by (simp only: seed_round_assemble_def seed_round_row_def seed_round_decode_def prod.case Let_def Parallel.map_def None option.case
        snapshot Sel rowsmap rows' list.map(1))
  next
    case (Some x)
    show ?thesis
      by (simp only: seed_round_assemble_def seed_round_row_def seed_round_decode_def prod.case Let_def Parallel.map_def Some option.case
        snapshot Sel rowsmap rows' publish[OF round_targets] round_decoded)
  qed
qed

lemma seed_plain_reps_parts:
  "seed_plain_reps (incs,sel,rows)=((map seed_made_generation incs,seed_made_generation sel,map seed_row_plain_reps rows),())"
  by (simp add: seed_plain_reps_def seed_row_plain_reps_def)

lemma seed_reference_round_represented:
  obtains ireps sel rows T Is Sel rows' where
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (table_represented_generation T)) ireps Is" "rel_option (table_represented_generation T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    "seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) (development_seed_decisions A)=development_seed_publication A"
proof -
  let ?d="development_seed_decisions A"
  obtain cs q0 where prepared: "seed_prepared_state ?d=(cs,q0)" by (cases "seed_prepared_state ?d")
  obtain T0 where rep0: "keyed_reference_state finite_target_key q0 T0" and dist0: "distinct T0"
    and lookup0: "seed_lookup_valid T0 (seed_lookup cs)"
    using seed_prepared_state_valid[OF prepared] by blast
  let ?L="seed_lookup cs"
  let ?m="seed_made_round_of ?L finite_construct_formed_cause_generation finite_construct_formed_cause_generation ?d"
  obtain incs sel rows where m: "?m=(incs,sel,rows)" by (metis prod.collapse)
  let ?ts="seed_round_targets ?m"
  obtain ns q where seq: "keyed_reference_sequence finite_target_key ?ts q0=(ns,q)" by (cases "keyed_reference_sequence finite_target_key ?ts q0")
  have exact: "ns=fst (value_reference_sequence ?ts T0)"
    "keyed_reference_state finite_target_key q (snd (value_reference_sequence ?ts T0))"
    using keyed_reference_sequence_exact[OF finite_target_key_injective rep0, of ?ts] seq by simp_all
  define T where "T=snd (value_reference_sequence ?ts T0)"
  have Tq: "rev (snd (snd q))=T" using keyed_reference_state_table[OF exact(2)] by (simp add: T_def)
  have distinct: "distinct T" using value_reference_sequence_distinct[OF dist0] by (simp add: T_def)
  have kept: "value_reference_read T0 i=Some y \<Longrightarrow> value_reference_read T i=Some y" for i y
    using value_reference_sequence_preserves by (simp add: T_def)
  have reads: "value_reference_reads T ns ?ts" using value_reference_reads_sequence[of ?ts T0] exact(1) by (simp add: T_def)
  have lookup: "seed_lookup_valid T ?L" by (rule seed_lookup_valid_preserved[OF lookup0 kept])
  have judged: "\<And>t. fst (?L t)=development_payload_judgment t" using lookup by (simp add: seed_lookup_valid_def)
  let ?inc="\<lambda>p. seed_record ?L finite_construct_formed_cause_generation (development_incumbent_key development_seed_state p)
    (finite_enumerated_environment [] []) []"
  let ?xs="zip development_seed_problems (map fst incs)"
  have incs: "incs=map ?inc development_seed_problems"
    using m by (simp add: seed_made_round_of_def Let_def Parallel.map_def split: option.splits prod.splits)
  have made_rows: "\<exists>selected issues. rows=map (seed_row_made ?L finite_construct_formed_cause_generation ?xs selected) issues"
    using m by (auto simp: seed_made_round_of_def Let_def Parallel.map_def incs split: option.splits prod.splits)
  have made_sel: "sel=(None,None) \<or> (\<exists>selected. sel=seed_row_selection ?L finite_construct_generation_record selected
      (finite_enumerated_environment [] []))"
    using m by (auto simp: seed_made_round_of_def Let_def split: option.splits prod.splits)
  have V_incs: "\<forall>m\<in>set incs. seed_made_valid T [] m"
    using seed_record_valid[OF seed_construct_core_formed_cause lookup] by (simp add: incs)
  have V_sel: "seed_made_valid T [] sel"
    using made_sel seed_record_valid[OF seed_construct_core_record lookup]
    by (auto simp: seed_made_valid_def seed_row_selection_def)
  have V_rows: "\<forall>row\<in>set rows. seed_row_valid T row"
    using made_rows seed_row_made_valid[OF seed_construct_core_formed_cause lookup] by auto
  have split: "value_reference_reads T ns (concat (map seed_made_targets incs))"
    "value_reference_reads T (drop (length (concat (map seed_made_targets incs))) ns) (seed_made_targets sel)"
    "value_reference_reads T (drop (length (seed_made_targets sel)) (drop (length (concat (map seed_made_targets incs))) ns))
      (concat (map seed_row_targets rows))"
    using reads by (simp_all add: m seed_round_targets_def value_reference_reads_append)
  let ?ireps="seed_consume_list ns incs"
  have R_incs: "list_all2 (rel_option (table_represented_generation T)) ?ireps (map seed_made_generation incs)"
    by (rule seed_consume_list_represents[OF split(1) V_incs])
  have R_sel: "rel_option (table_represented_generation T) (seed_made_rep (drop (length (concat (map seed_made_targets incs))) ns) sel [])
      (seed_made_generation sel)"
    by (rule seed_made_rep_represents[OF V_sel split(2)]) simp
  have lengths: "length development_seed_problems=length incs" by (simp add: incs)
  have incumbents: "\<forall>row\<in>set rows. rel_option (table_represented_generation T)
      (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ?ireps)) snd) (fst (snd row))"
  proof
    fix row
    assume "row\<in>set rows"
    then obtain selected r reading where row: "row=seed_row_made ?L finite_construct_formed_cause_generation ?xs selected (r,reading)"
      using made_rows by fastforce
    have "rel_option (table_represented_generation T) (Option.bind (find (\<lambda>(q,g). q=fst r) (zip development_seed_problems ?ireps)) snd)
        (Option.bind (find (\<lambda>(q,z). q=fst r) (zip development_seed_problems incs)) (\<lambda>(q,z). seed_made_generation z))"
      by (rule find_zip_rel_option[OF R_incs lengths])
    then show "rel_option (table_represented_generation T)
        (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ?ireps)) snd) (fst (snd row))"
      by (simp add: row seed_row_made_fields development_seed_incumbent_of_def seed_incumbent_find)
  qed
  have R_rows: "list_all2 (seed_quad_rel T)
      (seed_rows_rep ?ireps (drop (length (seed_made_targets sel)) (drop (length (concat (map seed_made_targets incs))) ns)) rows)
      (map seed_row_plain_reps rows)"
    by (rule seed_rows_rep_represents[OF split(3) V_rows incumbents])
  have round: "development_seed_reference_round A=
      (seed_round_assemble ((seed_reps_of ns ?m),T) seed_reference_pub ?d,T)"
    by (simp add: development_seed_reference_round_def development_seed_round_def prepared seed_reference_reps_def seq Tq
      Let_def)
  have plain: "seed_round_assemble (seed_plain_reps ?m) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
        else map (\<lambda>q. None)) ?d=development_seed_publication A"
    by (simp only: seed_round_assemble_plain[OF judged] development_seed_publication_formed_causes
      parallel_computed_function_exact Let_def)
  show ?thesis
    using that[OF round[unfolded m seed_reps_of_def Let_def prod.case] distinct R_incs R_sel R_rows
      plain[unfolded m seed_plain_reps_parts]] .
qed


subsection \<open>Every target of the reference round is in its table\<close>


lemma seed_reference_pub_within:
  assumes S: "represented_snapshot_targets S\<subseteq>K" and ps: "represented_publications_targets ps\<subseteq>K"
  shows "\<forall>r\<in>set (seed_reference_pub T S ps). \<forall>x\<in>set_option r. held_result_targets (represented_result_held x)\<subseteq>K"
  using represented_publications_within[OF S ps]
  by (simp add: seed_reference_pub_def represented_locus_publications_body_def)

definition seed_round_within :: "nat set \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow> bool" where
  "seed_round_within K v \<longleftrightarrow> (case v of (S0,Sel,rows,results) \<Rightarrow>
     (\<forall>S\<in>set_option S0. represented_snapshot_targets S\<subseteq>K) \<and> (\<forall>G\<in>set_option Sel. set_generation_structure G\<subseteq>K) \<and>
     (\<forall>x\<in>set rows. (\<forall>X\<in>set_option (fst x)\<union>set_option (fst (snd x))\<union>set_option (fst (snd (snd x))).
         set_generation_structure X\<subseteq>K) \<and>
       (\<forall>r\<in>set (fst (snd (snd (snd x)))). \<forall>y\<in>set_option r. held_result_targets (represented_result_held y)\<subseteq>K)) \<and>
     (\<forall>r\<in>set results. \<forall>y\<in>set_option r. held_result_targets (represented_result_held y)\<subseteq>K))"


theorem development_seed_reference_round_decoded:
  "seed_round_decode (snd (development_seed_reference_round A)) (fst (development_seed_reference_round A))=
    development_seed_publication A"
proof -
  obtain ireps sel rows T Is Sel rows' where parts:
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (table_represented_generation T)) ireps Is" "rel_option (table_represented_generation T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    "seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) (development_seed_decisions A)=development_seed_publication A"
    by (rule seed_reference_round_represented)
  show ?thesis using seed_round_assemble_decoded[OF parts(2-5)] parts(1,6) by simp
qed

lemma seed_round_assemble_within:
  assumes ireps: "list_all2 (rel_option (table_represented_generation T)) ireps Is" and sel: "rel_option (table_represented_generation T) sel Sel"
    and rows: "list_all2 (seed_quad_rel T) rows rows'"
  shows "seed_round_within {..<length T} (seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub d)"
proof -
  let ?K="{..<length T}"
  let ?pubR="case map_option fset_of_list (those ireps) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> seed_reference_pub T S"
  have publish: "\<forall>r\<in>set (?pubR ps). \<forall>y\<in>set_option r. held_result_targets (represented_result_held y)\<subseteq>?K"
    if ps: "represented_publications_targets ps\<subseteq>?K" for ps
  proof (cases "those ireps")
    case None
    then show ?thesis by simp
  next
    case (Some gs)
    then show ?thesis using seed_reference_pub_within[OF seed_snapshot_targets[OF ireps Some] ps] by simp
  qed
  have S0: "\<forall>S\<in>set_option (map_option fset_of_list (those ireps)). represented_snapshot_targets S\<subseteq>?K"
    using seed_snapshot_targets[OF ireps] by auto
  have Sel: "\<forall>G\<in>set_option sel. set_generation_structure G\<subseteq>?K" using table_represented_generation_option(2)[OF sel] by blast
  have rows_within: "\<forall>y\<in>set (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows).
      (\<forall>X\<in>set_option (fst y)\<union>set_option (fst (snd y))\<union>set_option (fst (snd (snd y))). set_generation_structure X\<subseteq>?K) \<and>
      (\<forall>r\<in>set (fst (snd (snd (snd y)))). \<forall>z\<in>set_option r. held_result_targets (represented_result_held z)\<subseteq>?K)"
  proof
    fix y
    assume "y\<in>set (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows)"
    then obtain x where x: "x\<in>set rows" and y: "y=(\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) x" by auto
    obtain I Q G H where shape: "x=(I,Q,G,H)" by (metis prod.collapse)
    have inside: "\<forall>g\<in>set_option I\<union>set_option Q\<union>set_option G\<union>set_option H. set_generation_structure g\<subseteq>?K"
      using seed_quad_targets[OF rows x] by (simp add: shape)
    have "represented_publications_targets [(None,Q),(I,G),(I,H)]\<subseteq>?K"
      by (rule represented_publications_targets_bound) (use inside in auto)
    then show "(\<forall>X\<in>set_option (fst y)\<union>set_option (fst (snd y))\<union>set_option (fst (snd (snd y))). set_generation_structure X\<subseteq>?K) \<and>
      (\<forall>r\<in>set (fst (snd (snd (snd y)))). \<forall>z\<in>set_option r. held_result_targets (represented_result_held z)\<subseteq>?K)"
      using publish inside by (simp add: y shape)
  qed
  have round_pub: "represented_publications_targets ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@map (\<lambda>(I,Q,G,H). (I,G)) rows)\<subseteq>?K"
    by (rule represented_publications_targets_bound) (use Sel seed_quad_targets[OF rows] in fastforce)
  show ?thesis
    unfolding seed_round_assemble_def seed_round_row_def seed_round_within_def Let_def Parallel.map_def prod.case
    using S0 Sel rows_within publish[OF round_pub] by (cases d) simp_all
qed

lemma development_seed_reference_round_within:
  "distinct (snd (development_seed_reference_round A)) \<and>
    seed_round_within {..<length (snd (development_seed_reference_round A))} (fst (development_seed_reference_round A))"
proof -
  obtain ireps sel rows T Is Sel rows' where parts:
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (table_represented_generation T)) ireps Is" "rel_option (table_represented_generation T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    by (rule seed_reference_round_represented)
  show ?thesis using seed_round_assemble_within[OF parts(3-5)] parts(1,2) by simp
qed

section \<open>The round's shared presentation and its word\<close>

text \<open>
  The round's table holds target leaves only, each once: a formed table of distinct leaf shapes with no pairs,
  keyed by the injective \<open>finite_target_key\<close>. Presented through the publication notions' presenters at the
  table's presentation, with the reference constructor as the target presenter, the round is a canonical shared
  term, every target leaf a reference, and it decodes to the presentation of the round. The word read off it is
  the word of the report.
\<close>


definition seed_round_presented :: "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> ('t,'t represented_transaction_result) seed_round \<Rightarrow> 'p" where
  "seed_round_presented P f=presented_pair_value P (presented_option P (presented_snapshot_value P f))
     (presented_pair_value P (presented_option P (presented_generation_value P f))
       (presented_pair_value P (presented_sequence P
         (presented_pair_value P (presented_option P (presented_generation_value P f))
           (presented_pair_value P (presented_option P (presented_generation_value P f))
             (presented_pair_value P (presented_option P (presented_generation_value P f))
               (presented_pair_value P (presented_sequence P (presented_option P (\<lambda>r. presented_result_value P f (represented_result_held r))))
                 (presented_boolean P))))))
         (presented_sequence P (presented_option P (\<lambda>r. presented_result_value P f (represented_result_held r))))))"


definition seed_round_data :: "finite_exact_target list \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow> finite_factor_term" where
  "seed_round_data T=finite_pair_presentation
     (finite_option_presentation (\<lambda>S. finite_snapshot_value (decode_represented_snapshot (\<lambda>i. T!i) S)))
     (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
       (finite_pair_presentation (finite_sequence_presentation
         (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
           (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
             (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
               (finite_pair_presentation (finite_sequence_presentation (finite_option_presentation
                   (\<lambda>r. finite_transaction_result_value (decode_represented_result (\<lambda>i. T!i) r))))
                 finite_boolean_data)))))
         (finite_sequence_presentation (finite_option_presentation
           (\<lambda>r. finite_transaction_result_value (decode_represented_result (\<lambda>i. T!i) r))))))"


lemma seed_round_data_decode: "seed_round_data T v=development_seed_publication_data (seed_round_decode T v)"
  by (cases v) (simp add: seed_round_data_def development_seed_publication_data_def seed_round_decode_def
    finite_pair_presentation_def[abs_def] finite_option_presentation_map finite_sequence_presentation_map case_prod_unfold)

theorem seed_round_presented_decode:
  assumes terms: "presented_terms P D" and targets: "presented_targets P D f (\<lambda>i. T!i) {..<length T}"
    and within: "seed_round_within {..<length T} v"
  shows "seed_round_presented P f v\<in>D \<and>
    presented_decode P (seed_round_presented P f v)=development_seed_publication_data (seed_round_decode T v)"
proof -
  note gen=presenter_decodes_generation[OF terms targets]
  note res=presenter_decodes_result[OF terms targets]
  note snap=presenter_decodes_snapshot[OF terms targets]
  note opt=presenter_decodes_option[OF terms] and seq=presenter_decodes_sequence[OF terms] and pair=presenter_decodes_pair[OF terms]
  note whole=pair[OF opt[OF snap] pair[OF opt[OF gen] pair[OF seq[OF pair[OF opt[OF gen] pair[OF opt[OF gen]
    pair[OF opt[OF gen] pair[OF seq[OF opt[OF res]] presenter_decodes_boolean[OF terms]]]]]] seq[OF opt[OF res]]]]]
  obtain S0 Sel rows results where v: "v=(S0,Sel,rows,results)" by (metis prod.collapse)
  have "seed_round_presented P f v\<in>D \<and> presented_decode P (seed_round_presented P f v)=seed_round_data T v"
    unfolding seed_round_presented_def seed_round_data_def
    by (rule whole[unfolded presenter_decodes_def, rule_format]) (use within in \<open>auto simp: v seed_round_within_def\<close>)
  then show ?thesis by (simp add: seed_round_data_decode)
qed

definition development_seed_publication_word_fold :: "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> development_problem fset \<Rightarrow> 's \<Rightarrow> 's" where
  "development_seed_publication_word_fold f A z=finite_term_shared_word_fold f (development_seed_publication_value A) z"

theorem development_seed_publication_word_fold_code [code]:
  "development_seed_publication_word_fold f A z=(case development_seed_reference_round A of (v,T) \<Rightarrow>
     shared_term_word_fold f (target_leaf_shapes T) (seed_round_presented (target_leaf_presentation T) Shared_Reference v) z)"
proof -
  obtain v T where round: "development_seed_reference_round A=(v,T)" by (cases "development_seed_reference_round A")
  have distinct: "distinct T" and within: "seed_round_within {..<length T} v"
    using development_seed_reference_round_within[of A] by (simp_all add: round)
  have decoded: "seed_round_decode T v=development_seed_publication A"
    using development_seed_reference_round_decoded[of A] by (simp add: round)
  let ?P="table_presentation (target_leaf_shapes T)"
  have formed: "table_formed (target_leaf_shapes T)" by (rule target_leaf_shapes_formed[OF distinct])
  have terms: "presented_terms ?P {s. shared_canonical (target_leaf_shapes T) s}" by (rule table_presentation_terms[OF formed])
  have presented: "seed_round_presented ?P Shared_Reference v\<in>{s. shared_canonical (target_leaf_shapes T) s} \<and>
      presented_decode ?P (seed_round_presented ?P Shared_Reference v)=development_seed_publication_value A"
    using seed_round_presented_decode[OF terms target_leaf_presented_targets within] decoded
    by (simp add: development_seed_publication_value_def)
  obtain t where t: "shared_decode (target_leaf_shapes T) (seed_round_presented ?P Shared_Reference v)=Some t"
    using canonical_decodes[OF formed] presented by blast
  have "t=development_seed_publication_value A" using presented t by (simp add: table_presentation_def)
  then show ?thesis
    using t by (simp add: round development_seed_publication_word_fold_def target_leaf_presentation_exact
      shared_term_word_fold_exact)
qed

end
