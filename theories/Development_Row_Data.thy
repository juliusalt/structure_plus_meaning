theory Development_Row_Data
imports Development_Loci Development_Requests
begin

section \<open>A row is presented through the generic presentations of its parts\<close>

text \<open>
  The development's notions are rows at loci: a locus is a path, a problem's body is its origin citation,
  its authority citation and its contract term carried inert, a request's body is its support and its
  context, two families of citations, and an issue's body is the family of decompositions that applied.
  Their executable presentations are composed here from the generic ones and from the path store's own,
  and each states injectivity and formation and nothing else, so that any other member of the class may
  replace it. No presenter carries a tag, a position in a name table, or a field the locus already says:
  the kind and the role are prefixes of the locus, the subject is its key, and the contract term's
  presentation is supplied, as the store's presentation relation takes its inert presentation.

  These presenters stand below the loop line, beside the loci and the requests, so that every presenter
  that carries a problem or a request can import them; their decoding into the store's bodies stands with
  the store (@{text Development_Row_Presentations}).
\<close>

section \<open>A citation and a family of citations\<close>

definition development_citation_data :: "bool list option \<Rightarrow> finite_factor_term" where
  "development_citation_data=finite_store_option finite_path"

definition development_citations_data :: "bool list list \<Rightarrow> finite_factor_term" where
  "development_citations_data=finite_sequence_presentation finite_path"

lemma development_citation_data_injective [intro]: "inj development_citation_data"
  unfolding development_citation_data_def by (rule finite_store_option_injective[OF finite_path_injective])

lemma development_citations_data_injective [intro]: "inj development_citations_data"
  unfolding development_citations_data_def by (rule finite_sequence_presentation_injective[OF finite_path_injective])

lemma development_citation_data_formed [simp]: "finite_term_formed (development_citation_data l)"
  unfolding development_citation_data_def by (rule finite_store_option_formed) simp

lemma development_citations_data_formed [simp]: "finite_term_formed (development_citations_data ls)"
  by (simp add: development_citations_data_def finite_sequence_presentation_def finite_data_list_formed list_all_iff)

section \<open>The bodies of a problem, a request and an issue\<close>

type_synonym development_problem_row = "bool list option\<times>bool list option\<times>isabelle_term"
type_synonym development_request_row = "bool list list\<times>bool list list"
type_synonym development_issue_row = "bool list list list"

definition development_problem_body_data ::
    "(isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow> development_problem_row \<Rightarrow> finite_factor_term" where
  "development_problem_body_data inert=finite_pair_presentation development_citation_data
    (finite_pair_presentation development_citation_data inert)"

definition development_request_body_data :: "development_request_row \<Rightarrow> finite_factor_term" where
  "development_request_body_data=finite_pair_presentation development_citations_data development_citations_data"

definition development_issue_body_data :: "development_issue_row \<Rightarrow> finite_factor_term" where
  "development_issue_body_data=finite_sequence_presentation development_citations_data"

text \<open>
  The contract term is carried inert, and its presentation need be injective only on the terms carried,
  as the store's relation asks of it.
\<close>

lemma development_problem_body_data_injective [intro]:
  assumes "inj_on inert A"
  shows "inj_on (development_problem_body_data inert) {b. snd (snd b)\<in>A}"
proof (rule inj_onI)
  fix b c assume b: "b\<in>{b. snd (snd b)\<in>A}" and c: "c\<in>{b. snd (snd b)\<in>A}"
    and same: "development_problem_body_data inert b=development_problem_body_data inert c"
  obtain x1 x2 x3 where B: "b=(x1,x2,x3)" by (cases b) auto
  obtain y1 y2 y3 where C: "c=(y1,y2,y3)" by (cases c) auto
  have e: "development_citation_data x1=development_citation_data y1 \<and>
      development_citation_data x2=development_citation_data y2 \<and> inert x3=inert y3"
    using same by (simp add: B C development_problem_body_data_def)
  have "x1=y1" by (rule injD[OF development_citation_data_injective]) (use e in simp)
  moreover have "x2=y2" by (rule injD[OF development_citation_data_injective]) (use e in simp)
  moreover have "x3=y3" by (rule inj_onD[OF assms]) (use e b c B C in simp)+
  ultimately show "b=c" by (simp add: B C)
qed

lemma development_request_body_data_injective [intro]: "inj development_request_body_data"
  unfolding development_request_body_data_def
  by (intro finite_pair_presentation_injective development_citations_data_injective)

lemma development_issue_body_data_injective [intro]: "inj development_issue_body_data"
  unfolding development_issue_body_data_def
  by (rule finite_sequence_presentation_injective[OF development_citations_data_injective])

lemma development_problem_body_data_formed:
  assumes "finite_term_formed (inert t)"
  shows "finite_term_formed (development_problem_body_data inert (x,y,t))"
  using assms by (simp add: development_problem_body_data_def)

lemma development_request_body_data_formed [simp]: "finite_term_formed (development_request_body_data z)"
  by (cases z) (simp add: development_request_body_data_def)

lemma development_issue_body_data_formed [simp]: "finite_term_formed (development_issue_body_data hs)"
  by (simp add: development_issue_body_data_def finite_sequence_presentation_def finite_data_list_formed list_all_iff)

section \<open>A problem outside the store is its row in the context that holds it\<close>

text \<open>
  Outside the store, in a report, a record or a verdict word, a problem is the same row the problem role
  holds at its locus, presented in the context that holds it: the context supplies the row's two
  citations. The presenter takes exactly the four parameters the store's presentation relation takes of a
  problem: the key of the state's constants, the inert presentation of the contract term (its local
  presentation in the state's names), and the context's origin and authority citations. Nothing new is
  presented, and no other parameter is taken.

  The presentation is partial, and its partiality is the relation's premise: one subject constant, so that
  the problem has a locus; an authority other than truth, which has no counterpart among citations; the
  origin absent exactly for a residual, the grant absent exactly for a generated problem. A problem outside
  the premise has no row: a problem with no locus is outside it, and so is a problem whose context gives no
  citation for an origin that needs one. The absence is the premise's case, never a shape presented; an
  omitted origin or authority is not mapped onto the absent citation.
\<close>

definition development_row_premise ::
    "(development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem \<Rightarrow> bool" where
  "development_row_premise origin grant p \<longleftrightarrow> development_subject_constant p\<noteq>None \<and>
    problem_authority p\<noteq>Development_Truth \<and>
    (origin p=None \<longleftrightarrow> problem_origin p=Development_Residual) \<and>
    (grant p=None \<longleftrightarrow> problem_authority p=Development_Generated)"

lemma development_row_premise_subject:
  assumes "development_row_premise origin grant p"
  obtains c where "problem_subject p={|c|}"
  using assms development_subject_constant_exact[of p]
  by (cases "development_subject_constant p") (auto simp: development_row_premise_def)

lemma development_row_premise_no_locus:
  assumes "development_problem_locus_at key r p=None"
  shows "\<not> development_row_premise origin grant p"
  using assms development_problem_locus_at_absent[of key r p] development_subject_constant_absent[of p]
  by (simp add: development_row_premise_def)

definition development_problem_row_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem \<Rightarrow> finite_factor_term option" where
  "development_problem_row_data key inert origin grant p=(if development_row_premise origin grant p then
    Some (finite_store_row (development_problem_body_data inert)
      (development_located_at key Development_Problem_Role p,
        origin p,grant p,development_contract_term (problem_contract p))) else None)"

lemma development_problem_row_data_outside:
  "\<not> development_row_premise origin grant p \<Longrightarrow> development_problem_row_data key inert origin grant p=None"
  by (simp add: development_problem_row_data_def)

corollary development_problem_row_data_no_locus:
  "development_problem_locus_at key r p=None \<Longrightarrow> development_problem_row_data key inert origin grant p=None"
  by (rule development_problem_row_data_outside[OF development_row_premise_no_locus])

lemma development_problem_row_data_inside:
  "development_row_premise origin grant p \<Longrightarrow> development_problem_row_data key inert origin grant p=
    Some (finite_store_row (development_problem_body_data inert)
      (development_located_at key Development_Problem_Role p,
        origin p,grant p,development_contract_term (problem_contract p)))"
  by (simp add: development_problem_row_data_def)

lemma development_problem_row_data_formed:
  assumes row: "development_problem_row_data key inert origin grant p=Some x"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "finite_term_formed x"
  using row by (auto simp: development_problem_row_data_def split: if_splits
    intro!: finite_store_row_formed development_problem_body_data_formed inert)

text \<open>
  Two problems whose loci are distinct have distinct rows, whatever their bodies: the row carries its
  locus. The contract therefore holds on every set of problems whose problem loci are distinct, which is
  what the store's relation asks of the problems it holds.
\<close>

theorem development_problem_row_data_injective:
  assumes loci: "inj_on (development_located_at key Development_Problem_Role) P"
    and p: "p\<in>P" and q: "q\<in>P"
    and first: "development_problem_row_data key inert origin grant p=Some x"
    and second: "development_problem_row_data key inert origin grant q=Some x"
  shows "p=q"
proof -
  have "finite_path (development_located_at key Development_Problem_Role p)=
      finite_path (development_located_at key Development_Problem_Role q)"
    using first second by (auto simp: development_problem_row_data_def finite_store_row_def
      finite_pair_presentation_def split: if_splits)
  then have "development_located_at key Development_Problem_Role p=
      development_located_at key Development_Problem_Role q"
    by (rule injD[OF finite_path_injective])
  then show ?thesis by (rule inj_onD[OF loci _ p q])
qed

section \<open>A request outside the store is its problem's row with its body as the request carries it\<close>

text \<open>
  A request is presented in the same context as its problem: its problem's row, its support as the family
  of its constants' keys, and its context carried as its entities, because a report does not hold the
  state's entity rows a citation would reach. The request's own locus is its problem's locus under the
  request role, and its constant term is its problem's contract term, carried once in the row; neither is
  presented again. A request whose problem is outside the premise has no presentation.
\<close>

definition development_request_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_request \<Rightarrow> finite_factor_term option" where
  "development_request_data key inert origin grant r=(case r of (p,s,S,E) \<Rightarrow>
    map_option (\<lambda>x. Finite_Pair x (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))) (development_problem_row_data key inert origin grant p))"

lemma development_request_data_problem:
  "development_request_data key inert origin grant (p,s,S,E)=None \<longleftrightarrow>
    development_problem_row_data key inert origin grant p=None"
  by (simp add: development_request_data_def)

lemma development_request_data_formed:
  assumes row: "development_request_data key inert origin grant r=Some x"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "finite_term_formed x"
proof -
  obtain p s S E where r: "r=(p,s,S,E)" by (cases r) auto
  obtain y where y: "development_problem_row_data key inert origin grant p=Some y"
    and xy: "x=Finite_Pair y (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))"
    using row by (auto simp: r development_request_data_def)
  have "finite_term_formed y" by (rule development_problem_row_data_formed[OF y inert])
  moreover have "finite_term_formed (isabelle_entities_data E)"
    by (auto simp: isabelle_entities_data_def finite_collection_presentation_def finite_data_list_formed
      list_all_iff ordered_finite_terms_set)
  ultimately show ?thesis by (simp add: xy)
qed

text \<open>
  The presentation is injective on every family of requests whose problems have distinct loci, whose
  support constants are keyed injectively, and whose constant term is their problem's contract term: the
  conditions the store's relation asks of the requests it holds.
\<close>

theorem development_request_data_injective:
  assumes loci: "inj_on (development_located_at key Development_Problem_Role) (fst ` R)"
    and keys: "inj_on key (\<Union>r\<in>R. fset (fst (snd (snd r))))"
    and terms: "\<And>r. r\<in>R \<Longrightarrow> development_contract_term (problem_contract (fst r))=fst (snd r)"
    and r: "r\<in>R" and r': "r'\<in>R"
    and first: "development_request_data key inert origin grant r=Some x"
    and second: "development_request_data key inert origin grant r'=Some x"
  shows "r=r'"
proof -
  obtain p s S E where R1: "r=(p,s,S,E)" by (cases r) auto
  obtain p' s' S' E' where R2: "r'=(p',s',S',E')" by (cases r') auto
  obtain y where y: "development_problem_row_data key inert origin grant p=Some y"
    and xy: "x=Finite_Pair y (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))"
    using first by (auto simp: R1 development_request_data_def)
  obtain y' where y': "development_problem_row_data key inert origin grant p'=Some y'"
    and xy': "x=Finite_Pair y' (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S'),E'))"
    using second by (auto simp: R2 development_request_data_def)
  have yy: "y=y'" and cit: "development_citations_data (map key (sorted_list_of_fset S))=
      development_citations_data (map key (sorted_list_of_fset S'))"
    and ent: "isabelle_entities_data E=isabelle_entities_data E'"
    using xy xy' by simp_all
  have pp: "p=p'"
    by (rule development_problem_row_data_injective[OF loci _ _ y y'[folded yy]])
      (use r r' R1 R2 in force)+
  have ss: "s=s'" using terms[OF r] terms[OF r'] pp by (simp add: R1 R2)
  have mapped: "map key (sorted_list_of_fset S)=map key (sorted_list_of_fset S')"
    by (rule injD[OF development_citations_data_injective cit])
  have inside: "set (sorted_list_of_fset S) \<union> set (sorted_list_of_fset S')\<subseteq>(\<Union>r\<in>R. fset (fst (snd (snd r))))"
    using r r' by (auto simp: R1 R2)
  have "sorted_list_of_fset S=sorted_list_of_fset S'"
    using mapped inj_on_map_eq_map[OF inj_on_subset[OF keys inside]] by simp
  then have "fset S=fset S'" by (metis sorted_list_of_fset_simps(1))
  then have SS: "S=S'" by (simp add: fset_inject)
  have EE: "E=E'" by (rule injD[OF isabelle_collections_injective(1) ent])
  show ?thesis by (simp only: R1 R2 pp ss SS EE)
qed

text \<open>A request is presented in the context that carries it exactly where its problem is.\<close>

lemma development_request_data_premise:
  "development_request_data key inert origin grant r\<noteq>None \<longleftrightarrow> development_row_premise origin grant (fst r)"
  by (cases r) (simp add: development_request_data_def development_problem_row_data_def)

text \<open>
  A row presented in context decodes to a formed value whenever the inert presentation is formed: the
  store's formedness premise for the rows a context presents.
\<close>

lemma development_problem_row_data_term_formed:
  assumes row: "development_problem_row_data key inert origin grant p=Some x"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "term_formed (decode_finite_term x)"
  using development_problem_row_data_formed[OF row inert] by (simp add: finite_term_formed_correct)

lemma development_request_data_term_formed:
  assumes row: "development_request_data key inert origin grant r=Some x"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "term_formed (decode_finite_term x)"
  using development_request_data_formed[OF row inert] by (simp add: finite_term_formed_correct)

section \<open>The contexts that supply a row's citations\<close>

text \<open>
  A report presents the problems of a context, and the context supplies each row's citations: it cites
  what posed a problem, or it has no citation to give, and never invents one. The premise reads a
  citation only through its absence, so two contexts absent at the same problem give the premise there
  alike. The contexts are a residual record, which cites nothing; a repair, whose definition problems cite
  the repaired problem (@{text Development_Refinement_Repair}); a loop, whose demanded problems cite the
  head of the history's first repair row that holds them (@{text Development_Repair_Rows}); and a
  request, presented in the context that carries it.
\<close>

lemma development_row_premise_origin_cong:
  assumes "origin p=None \<longleftrightarrow> origin' p=None"
  shows "development_row_premise origin grant p \<longleftrightarrow> development_row_premise origin' grant p"
  using assms by (simp add: development_row_premise_def)

text \<open>
  A problem of a constant carries the origin and authority its constructor was given and the constant
  as its one subject, so a context meets the premise on it exactly where it cites according to them.
\<close>

lemma development_constant_problem_fields:
  assumes "development_constant_problem reading kind C r a c=Some p"
  shows "problem_subject p={|c|}" "problem_origin p=r" "problem_authority p=a"
  using assms by (auto simp: development_constant_problem_def)

lemma development_constant_problem_premise:
  assumes problem: "development_constant_problem reading kind C r a c=Some p"
    and authority: "a\<noteq>Development_Truth"
    and origin: "origin p=None \<longleftrightarrow> r=Development_Residual"
    and grant: "grant p=None \<longleftrightarrow> a=Development_Generated"
  shows "development_row_premise origin grant p"
proof -
  have subject: "problem_subject p={|c|}" and fields: "problem_origin p=r" "problem_authority p=a"
    by (rule development_constant_problem_fields[OF problem])+
  have "development_subject_constant p=Some c" using subject by (simp only: development_subject_constant_exact)
  then show ?thesis using fields authority origin grant by (simp add: development_row_premise_def)
qed

subsection \<open>A residual record cites nothing\<close>

text \<open>
  The seed, the machinery and a demanded state pose residual problems of generated authority, each about
  one constant; their record cites nothing, and the premise holds of each problem their constructors make.
\<close>

lemma development_row_premise_residual_record:
  "development_row_premise (\<lambda>_. None) (\<lambda>_. None) p \<longleftrightarrow> development_subject_constant p\<noteq>None \<and>
    problem_origin p=Development_Residual \<and> problem_authority p=Development_Generated"
  by (auto simp: development_row_premise_def)

corollary development_constant_problem_residual_record:
  assumes "development_constant_problem reading kind C Development_Residual Development_Generated c=Some p"
  shows "development_row_premise (\<lambda>_. None) (\<lambda>_. None) p"
  by (rule development_constant_problem_premise[OF assms]) simp_all

corollary development_constant_problems_residual_record:
  assumes "p\<in>set (development_constant_problems reading kind C Development_Residual Development_Generated cs)"
  shows "development_row_premise (\<lambda>_. None) (\<lambda>_. None) p"
  using assms development_constant_problem_residual_record unfolding development_constant_problems_exact by blast

corollary development_constant_request_residual_record:
  assumes request: "development_constant_request reading kind C Development_Residual Development_Generated c=Some r"
  shows "development_row_premise (\<lambda>_. None) (\<lambda>_. None) (fst r)"
proof -
  obtain p s S E where R: "r=(p,s,S,E)" by (cases r) auto
  show ?thesis
    using development_constant_problem_residual_record[OF development_constant_request_fields(1)[OF request[unfolded R]]]
    by (simp add: R)
qed

corollary development_refinement_request_residual_record:
  assumes "development_refinement_request C Development_Residual Development_Generated c=Some r"
  shows "development_row_premise (\<lambda>_. None) (\<lambda>_. None) (fst r)"
  by (rule development_constant_request_residual_record[OF assms[unfolded development_refinement_request_def]])

section \<open>The problems, the assessment and the requests of a report, in its context\<close>

text \<open>
  A report presents the problems of its context with the context's four parameters; a state's key and
  inert presentation are the state presenter's (@{text Development_State_Presenter}). Its presentations are
  exact on every set of problems inside the premise whose problem loci are distinct: the domain the store's
  relation holds.
\<close>

definition development_row_domain ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> development_problem set \<Rightarrow> bool" where
  "development_row_domain key origin grant P \<longleftrightarrow> inj_on (development_located_at key Development_Problem_Role) P \<and>
    (\<forall>p\<in>P. development_row_premise origin grant p)"

lemma development_row_domain_mono:
  assumes domain: "development_row_domain key origin grant P" and inside: "Q\<subseteq>P"
  shows "development_row_domain key origin grant Q"
proof -
  have injective: "inj_on (development_located_at key Development_Problem_Role) P"
    and premise: "\<forall>p\<in>P. development_row_premise origin grant p"
    using domain by (simp_all add: development_row_domain_def)
  have "inj_on (development_located_at key Development_Problem_Role) Q" by (rule inj_on_subset[OF injective inside])
  then show ?thesis using premise inside by (auto simp: development_row_domain_def)
qed

theorem development_problem_row_data_presented:
  assumes domain: "development_row_domain key origin grant P"
  shows "finite_presented_on (development_problem_row_data key inert origin grant) P"
proof (rule finite_presented_onI)
  fix p assume "p\<in>P"
  then show "development_problem_row_data key inert origin grant p\<noteq>None"
    using domain by (simp add: development_row_domain_def development_problem_row_data_def)
next
  fix p q t assume p: "p\<in>P" and q: "q\<in>P"
    and fp: "development_problem_row_data key inert origin grant p=Some t"
    and fq: "development_problem_row_data key inert origin grant q=Some t"
  have loci: "inj_on (development_located_at key Development_Problem_Role) P"
    using domain by (simp add: development_row_domain_def)
  show "p=q" by (rule development_problem_row_data_injective[OF loci p q fp fq])
qed

definition development_problems_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem list \<Rightarrow> finite_factor_term option" where
  "development_problems_data key inert origin grant=
    finite_partial_sequence (development_problem_row_data key inert origin grant)"

corollary development_problems_data_presented [intro]:
  "development_row_domain key origin grant P \<Longrightarrow>
    finite_presented_on (development_problems_data key inert origin grant) (lists P)"
  unfolding development_problems_data_def
  by (intro finite_partial_sequence_presented development_problem_row_data_presented)

definition development_problem_assessment_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem_assessment \<Rightarrow> finite_factor_term option" where
  "development_problem_assessment_data key inert origin grant=
    finite_partial_pair (development_problems_data key inert origin grant)
      (finite_partial_pair (development_problems_data key inert origin grant)
        (finite_partial_pair (development_problems_data key inert origin grant)
          (finite_partial_pair (development_problems_data key inert origin grant) (Some \<circ> isabelle_positions_data))))"

corollary development_problem_assessment_data_presented [intro]:
  "development_row_domain key origin grant P \<Longrightarrow>
    finite_presented_on (development_problem_assessment_data key inert origin grant)
      (lists P\<times>lists P\<times>lists P\<times>lists P\<times>UNIV)"
  unfolding development_problem_assessment_data_def
  by (intro finite_partial_pair_presented development_problems_data_presented finite_presented_total
    isabelle_collections_injective(2))

text \<open>
  A request is presented where its problem is, and its presentations are exact on every family of
  requests whose problems form a domain, whose support constants are keyed injectively and whose
  constant term is their problem's contract term.
\<close>

definition development_request_domain ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> development_request set \<Rightarrow> bool" where
  "development_request_domain key origin grant R \<longleftrightarrow> development_row_domain key origin grant (fst ` R) \<and>
    inj_on key (\<Union>r\<in>R. fset (fst (snd (snd r)))) \<and>
    (\<forall>r\<in>R. development_contract_term (problem_contract (fst r))=fst (snd r))"

theorem development_request_data_presented:
  assumes domain: "development_request_domain key origin grant R"
  shows "finite_presented_on (development_request_data key inert origin grant) R"
proof (rule finite_presented_onI)
  fix r assume r: "r\<in>R"
  have premise: "\<forall>p\<in>fst ` R. development_row_premise origin grant p"
    using domain by (simp add: development_request_domain_def development_row_domain_def)
  have "development_row_premise origin grant (fst r)" by (rule bspec[OF premise imageI[OF r]])
  then show "development_request_data key inert origin grant r\<noteq>None"
    by (simp only: development_request_data_premise)
next
  fix r r' t assume r: "r\<in>R" and r': "r'\<in>R"
    and first: "development_request_data key inert origin grant r=Some t"
    and second: "development_request_data key inert origin grant r'=Some t"
  have loci: "inj_on (development_located_at key Development_Problem_Role) (fst ` R)"
    and keys: "inj_on key (\<Union>r\<in>R. fset (fst (snd (snd r))))"
    and terms: "\<And>r. r\<in>R \<Longrightarrow> development_contract_term (problem_contract (fst r))=fst (snd r)"
    using domain by (simp_all add: development_request_domain_def development_row_domain_def)
  show "r=r'" by (rule development_request_data_injective[OF loci keys terms r r' first second])
qed

definition development_requests_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_request list \<Rightarrow> finite_factor_term option" where
  "development_requests_data key inert origin grant=
    finite_partial_sequence (development_request_data key inert origin grant)"

corollary development_requests_data_presented [intro]:
  "development_request_domain key origin grant R \<Longrightarrow>
    finite_presented_on (development_requests_data key inert origin grant) (lists R)"
  unfolding development_requests_data_def
  by (intro finite_partial_sequence_presented development_request_data_presented)

subsection \<open>The problems and the requests one constant construction poses form a domain\<close>

text \<open>
  A construction that poses one problem of each constant, in a context meeting the premise on what it poses,
  poses problems at distinct loci: two of them at one locus concern one constant, the key being injective,
  and are the one problem it poses of that constant. Every set of its problems is therefore a domain of the
  context, and every set of its requests a request domain, a request's constant term being its problem's
  contract term. A report whose problems and requests are such lies in its presentation's domain.
\<close>

theorem development_constant_problems_domain:
  assumes injective: "inj key" and authority: "a\<noteq>Development_Truth"
    and origin: "\<And>p. origin p=None \<longleftrightarrow> r=Development_Residual"
    and grant: "\<And>p. grant p=None \<longleftrightarrow> a=Development_Generated"
    and problems: "\<And>p. p\<in>P \<Longrightarrow> \<exists>c. development_constant_problem reading kind C r a c=Some p"
  shows "development_row_domain key origin grant P"
proof -
  have premise: "\<forall>p\<in>P. development_row_premise origin grant p"
  proof
    fix p assume "p\<in>P"
    then obtain c where "development_constant_problem reading kind C r a c=Some p" using problems by blast
    then show "development_row_premise origin grant p"
      by (rule development_constant_problem_premise[OF _ authority origin grant])
  qed
  have loci: "inj_on (development_located_at key Development_Problem_Role) P"
  proof (rule inj_onI)
    fix p q assume p: "p\<in>P" and q: "q\<in>P"
      and same: "development_located_at key Development_Problem_Role p=development_located_at key Development_Problem_Role q"
    obtain c where c: "development_constant_problem reading kind C r a c=Some p" using problems[OF p] by blast
    obtain d where d: "development_constant_problem reading kind C r a d=Some q" using problems[OF q] by blast
    have "development_locus key Development_Problem_Role (problem_contract p) c=
        development_locus key Development_Problem_Role (problem_contract q) d"
      using same development_located_at_subject[OF development_constant_problem_fields(1)[OF c]]
        development_located_at_subject[OF development_constant_problem_fields(1)[OF d]] by simp
    then have "key c=key d" by (rule development_locus_key_determines)
    then have "c=d" by (rule injD[OF injective])
    then show "p=q" using c d by simp
  qed
  show ?thesis using premise loci by (simp add: development_row_domain_def)
qed

corollary development_constant_problems_list_domain:
  assumes injective: "inj key" and authority: "a\<noteq>Development_Truth"
    and origin: "\<And>p. origin p=None \<longleftrightarrow> r=Development_Residual"
    and grant: "\<And>p. grant p=None \<longleftrightarrow> a=Development_Generated"
  shows "development_row_domain key origin grant (set (development_constant_problems reading kind C r a cs))"
  by (rule development_constant_problems_domain[OF injective authority origin grant,
    where reading=reading and kind=kind and C=C]) (auto simp: development_constant_problems_exact)

theorem development_constant_requests_domain:
  assumes injective: "inj key" and authority: "a\<noteq>Development_Truth"
    and origin: "\<And>p. origin p=None \<longleftrightarrow> r=Development_Residual"
    and grant: "\<And>p. grant p=None \<longleftrightarrow> a=Development_Generated"
    and terms: "\<And>s. development_contract_term (kind s)=s"
    and requests: "\<And>q. q\<in>R \<Longrightarrow> \<exists>c. development_constant_request reading kind C r a c=Some q"
  shows "development_request_domain key origin grant R"
proof -
  have fields: "\<exists>c. development_constant_problem reading kind C r a c=Some (fst q) \<and>
      development_contract_term (problem_contract (fst q))=fst (snd q)" if q: "q\<in>R" for q
  proof -
    obtain c where c: "development_constant_request reading kind C r a c=Some q" using requests[OF q] by blast
    obtain p s S E where Q: "q=(p,s,S,E)" by (cases q) auto
    show ?thesis using development_constant_request_fields(1,2)[OF c[unfolded Q]] terms by (auto simp: Q)
  qed
  have "development_row_domain key origin grant (fst ` R)"
    by (rule development_constant_problems_domain[OF injective authority origin grant,
      where reading=reading and kind=kind and C=C]) (use fields in blast)
  moreover have "inj_on key (\<Union>q\<in>R. fset (fst (snd (snd q))))" by (rule inj_on_subset[OF injective]) simp
  moreover have "\<forall>q\<in>R. development_contract_term (problem_contract (fst q))=fst (snd q)" using fields by blast
  ultimately show ?thesis by (simp add: development_request_domain_def)
qed

section \<open>A set of problems is the table of their rows\<close>

text \<open>
  A set of problems, such as the problems a loop has answered, is a table: the store of their rows, each
  at its problem locus. Its word is a function of the rows alone, the store of any listing of them.
\<close>

definition development_problems_table ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_problem fset \<Rightarrow> finite_factor_term option" where
  "development_problems_table key inert origin grant A=(if fBall A (development_row_premise origin grant)
    then Some (finite_rows_table (fimage (the \<circ> development_problem_row_data key inert origin grant) A))
    else None)"

lemma development_problem_row_read:
  assumes "development_row_premise origin grant p"
  shows "finite_row_read (the (development_problem_row_data key inert origin grant p))=
    (development_located_at key Development_Problem_Role p,
      development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))"
  using assms by (simp add: development_problem_row_data_inside)

lemma development_row_domain_inside:
  assumes domain: "development_row_domain key origin grant P" and inside: "fset A\<subseteq>P"
  shows "\<And>p. p\<in>fset A \<Longrightarrow> development_row_premise origin grant p"
    and "inj_on (development_located_at key Development_Problem_Role) (fset A)"
proof -
  have premise: "\<forall>p\<in>P. development_row_premise origin grant p"
    and loci: "inj_on (development_located_at key Development_Problem_Role) P"
    using domain by (simp_all add: development_row_domain_def)
  show "development_row_premise origin grant p" if "p\<in>fset A" for p
    by (rule bspec[OF premise rev_subsetD[OF that inside]])
  show "inj_on (development_located_at key Development_Problem_Role) (fset A)" by (rule inj_on_subset[OF loci inside])
qed

lemma development_problem_rows_read:
  assumes premise: "\<And>p. p\<in>fset A \<Longrightarrow> development_row_premise origin grant p"
  shows "finite_row_read ` fset (fimage (the \<circ> development_problem_row_data key inert origin grant) A)=
    (\<lambda>p. (development_located_at key Development_Problem_Role p,
      development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))) ` fset A"
proof -
  have "finite_row_read ` fset (fimage (the \<circ> development_problem_row_data key inert origin grant) A)=
      (finite_row_read \<circ> (the \<circ> development_problem_row_data key inert origin grant)) ` fset A"
    by (simp add: fimage.rep_eq image_comp)
  also have "\<dots>=(\<lambda>p. (development_located_at key Development_Problem_Role p,
      development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))) ` fset A"
    by (rule image_cong[OF refl]) (simp add: development_problem_row_read[OF premise])
  finally show ?thesis .
qed

lemma development_problem_rows_single_valued:
  assumes domain: "development_row_domain key origin grant P" and inside: "fset A\<subseteq>P"
  shows "single_valued (finite_row_read ` fset (fimage (the \<circ> development_problem_row_data key inert origin grant) A))"
proof -
  have rows: "finite_row_read ` fset (fimage (the \<circ> development_problem_row_data key inert origin grant) A)=
    (\<lambda>p. (development_located_at key Development_Problem_Role p,
      development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))) ` fset A"
    by (rule development_problem_rows_read[OF development_row_domain_inside(1)[OF domain inside]])
  have diagonal: "single_valued ((\<lambda>p. (p,p)) ` fset A)" by (auto simp: single_valued_def)
  have "single_valued ((\<lambda>(a,b). (development_located_at key Development_Problem_Role a,
      development_problem_body_data inert (origin b,grant b,development_contract_term (problem_contract b)))) `
      (\<lambda>p. (p,p)) ` fset A)"
    by (rule single_valued_pair_image[OF diagonal])
      (simp add: rel_dom_image image_image development_row_domain_inside(2)[OF domain inside])
  then show ?thesis unfolding rows by (simp add: image_image)
qed

theorem development_problems_table_listing:
  assumes domain: "development_row_domain key origin grant P" and inside: "fset A\<subseteq>P"
    and listing: "set rows=(\<lambda>p. (development_located_at key Development_Problem_Role p,
      development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))) ` fset A"
  shows "development_problems_table key inert origin grant A=Some (finite_listing_store id rows)"
proof -
  note premise=development_row_domain_inside(1)[OF domain inside]
  have read: "set rows=finite_row_read ` fset (fimage (the \<circ> development_problem_row_data key inert origin grant) A)"
    by (simp only: listing development_problem_rows_read[OF premise])
  have "finite_rows_table (fimage (the \<circ> development_problem_row_data key inert origin grant) A)=
      finite_listing_store id rows"
    by (rule finite_rows_table_listing[OF read])
      (use development_problem_rows_single_valued[OF domain inside, of inert] read in simp)
  moreover have "fBall A (development_row_premise origin grant)" by (rule fBallI) (rule premise)
  ultimately show ?thesis by (simp add: development_problems_table_def)
qed

theorem development_problems_table_presented [intro]:
  assumes domain: "development_row_domain key origin grant P"
  shows "finite_presented_on (development_problems_table key inert origin grant) {A. fset A\<subseteq>P}"
proof (rule finite_presented_onI)
  fix A assume A: "A\<in>{A. fset A\<subseteq>P}"
  have inside: "fset A\<subseteq>P" using A by simp
  have "fBall A (development_row_premise origin grant)"
    by (rule fBallI) (rule development_row_domain_inside(1)[OF domain inside])
  then show "development_problems_table key inert origin grant A\<noteq>None"
    by (simp add: development_problems_table_def)
next
  fix A B t assume A: "A\<in>{A. fset A\<subseteq>P}" and B: "B\<in>{A. fset A\<subseteq>P}"
    and first: "development_problems_table key inert origin grant A=Some t"
    and second: "development_problems_table key inert origin grant B=Some t"
  let ?row="the \<circ> development_problem_row_data key inert origin grant"
  have premise: "\<And>p. p\<in>P \<Longrightarrow> development_row_premise origin grant p"
    using domain by (simp add: development_row_domain_def)
  have shape: "\<exists>l v. t=Finite_Pair (finite_path l) v" if t: "t\<in>fset (fimage ?row A) \<union> fset (fimage ?row B)" for t
  proof -
    obtain p where p: "p\<in>fset A \<union> fset B" "t=?row p"
      using t unfolding fimage.rep_eq image_Un[symmetric] by (rule imageE) (rule that)
    have AB: "fset A \<union> fset B\<subseteq>P" using A B by simp
    have pP: "p\<in>P" by (rule rev_subsetD[OF p(1) AB])
    have "t=Finite_Pair (finite_path (development_located_at key Development_Problem_Role p))
        (development_problem_body_data inert (origin p,grant p,development_contract_term (problem_contract p)))"
      using p(2) development_problem_row_data_inside[OF premise[OF pP], of key inert]
      by (simp add: finite_store_row_def finite_pair_presentation_def)
    then show ?thesis by blast
  qed
  have svA: "single_valued (finite_row_read ` fset (fimage ?row A))"
    by (rule development_problem_rows_single_valued[OF domain]) (use A in simp)
  have svB: "single_valued (finite_row_read ` fset (fimage ?row B))"
    by (rule development_problem_rows_single_valued[OF domain]) (use B in simp)
  have same: "finite_rows_table (fimage ?row A)=finite_rows_table (fimage ?row B)"
    using first second by (auto simp: development_problems_table_def split: if_splits)
  have images: "fimage ?row A=fimage ?row B" by (rule finite_rows_table_identifies[OF shape svA svB same])
  have img: "?row ` fset A=?row ` fset B" using arg_cong[OF images, of fset] by (simp only: fimage.rep_eq)
  have "fset A=fset B"
    by (rule inj_on_image_eq_iff[THEN iffD1, OF finite_presented_on_the[OF development_problem_row_data_presented[OF domain]]
      _ _ img]) (use A B in simp_all)
  then show "A=B" by (simp add: fset_inject)
qed

end
