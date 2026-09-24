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

section \<open>A partial presentation presents its domain exactly\<close>

text \<open>
  A presentation in context is partial: a value outside its premise has no presentation, and a report
  carrying one is not a presentation of it. A partial presentation presents a domain exactly when every
  value of the domain has a presentation and distinct values have distinct presentations. The generic
  presentations compose as the total ones do: a pair presents the product of its parts' domains, a
  sequence the lists over its element's domain, an optional value the options over it and a collection
  the finite sets inside it; a total presentation is partial nowhere.
\<close>

definition finite_presented_on :: "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "finite_presented_on f A \<longleftrightarrow> (\<forall>x\<in>A. f x\<noteq>None) \<and> inj_on f A"

lemma finite_presented_onI:
  assumes some: "\<And>x. x\<in>A \<Longrightarrow> f x\<noteq>None"
    and exact: "\<And>x y t. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> f x=Some t \<Longrightarrow> f y=Some t \<Longrightarrow> x=y"
  shows "finite_presented_on f A"
  unfolding finite_presented_on_def
proof (intro conjI ballI inj_onI)
  fix x assume "x\<in>A" then show "f x\<noteq>None" by (rule some)
next
  fix x y assume x: "x\<in>A" and y: "y\<in>A" and same: "f x=f y"
  obtain t where t: "f x=Some t" using some[OF x] by blast
  show "x=y" by (rule exact[OF x y t]) (use same t in simp)
qed

lemma finite_presented_on_some:
  assumes "finite_presented_on f A" "x\<in>A"
  obtains t where "f x=Some t"
  using assms by (auto simp: finite_presented_on_def)

lemma finite_presented_on_eq:
  assumes presented: "finite_presented_on f A" and x: "x\<in>A" and y: "y\<in>A" and same: "f x=f y"
  shows "x=y"
proof -
  have "inj_on f A" using presented by (simp add: finite_presented_on_def)
  then show ?thesis by (rule inj_onD[OF _ same x y])
qed

lemma finite_presented_on_mono:
  assumes presented: "finite_presented_on f A" and inside: "B\<subseteq>A"
  shows "finite_presented_on f B"
proof -
  have injective: "inj_on f A" and some: "\<forall>x\<in>A. f x\<noteq>None"
    using presented by (simp_all add: finite_presented_on_def)
  have "inj_on f B" by (rule inj_on_subset[OF injective inside])
  then show ?thesis using some inside by (auto simp: finite_presented_on_def)
qed

lemma finite_presented_total [intro]:
  assumes injective: "inj g"
  shows "finite_presented_on (Some \<circ> g) A"
proof (rule finite_presented_onI)
  fix x show "(Some \<circ> g) x\<noteq>None" by simp
next
  fix x y t assume "(Some \<circ> g) x=Some t" "(Some \<circ> g) y=Some t"
  then have "g x=g y" by simp
  then show "x=y" by (rule injD[OF injective])
qed

lemma finite_presented_on_comp:
  assumes presented: "finite_presented_on f A" and injective: "inj_on h B" and inside: "h ` B\<subseteq>A"
  shows "finite_presented_on (f \<circ> h) B"
proof (rule finite_presented_onI)
  fix x assume "x\<in>B"
  then have "h x\<in>A" using inside by blast
  then show "(f \<circ> h) x\<noteq>None" using presented by (auto simp: finite_presented_on_def)
next
  fix x y t assume x: "x\<in>B" and y: "y\<in>B" and fx: "(f \<circ> h) x=Some t" and fy: "(f \<circ> h) y=Some t"
  have "h x=h y"
    by (rule finite_presented_on_eq[OF presented]) (use x y fx fy inside in \<open>auto simp: image_subset_iff\<close>)
  then show "x=y" by (rule inj_onD[OF injective _ x y])
qed

definition finite_partial_pair ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> ('b \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a\<times>'b \<Rightarrow>
      finite_factor_term option" where
  "finite_partial_pair f g z=(case f (fst z) of None \<Rightarrow> None | Some x \<Rightarrow> map_option (Finite_Pair x) (g (snd z)))"

lemma finite_partial_pair_presented [intro]:
  assumes first: "finite_presented_on f A" and second: "finite_presented_on g B"
  shows "finite_presented_on (finite_partial_pair f g) (A\<times>B)"
proof (rule finite_presented_onI)
  fix z assume "z\<in>A\<times>B"
  then obtain a b where z: "z=(a,b)" "a\<in>A" "b\<in>B" by blast
  obtain x where x: "f a=Some x" by (rule finite_presented_on_some[OF first z(2)])
  obtain y where y: "g b=Some y" by (rule finite_presented_on_some[OF second z(3)])
  show "finite_partial_pair f g z\<noteq>None" by (simp add: finite_partial_pair_def z(1) x y)
next
  fix z w t assume z: "z\<in>A\<times>B" and w: "w\<in>A\<times>B"
    and fz: "finite_partial_pair f g z=Some t" and fw: "finite_partial_pair f g w=Some t"
  obtain a b where Z: "z=(a,b)" "a\<in>A" "b\<in>B" using z by blast
  obtain a' b' where W: "w=(a',b')" "a'\<in>A" "b'\<in>B" using w by blast
  obtain x y where x: "f a=Some x" and y: "g b=Some y" and t: "t=Finite_Pair x y"
    using fz by (auto simp: finite_partial_pair_def Z(1) split: option.splits)
  obtain x' y' where x': "f a'=Some x'" and y': "g b'=Some y'" and t': "t=Finite_Pair x' y'"
    using fw by (auto simp: finite_partial_pair_def W(1) split: option.splits)
  have "a=a'" by (rule finite_presented_on_eq[OF first Z(2) W(2)]) (use x x' t t' in simp)
  moreover have "b=b'" by (rule finite_presented_on_eq[OF second Z(3) W(3)]) (use y y' t t' in simp)
  ultimately show "z=w" by (simp add: Z(1) W(1))
qed

definition finite_partial_sequence ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a list \<Rightarrow> finite_factor_term option" where
  "finite_partial_sequence f xs=map_option finite_data_list (those (map f xs))"

lemma those_map_present:
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> f x\<noteq>None"
  shows "those (map f xs)=Some (map (the \<circ> f) xs)"
  using assms by (induction xs) (auto split: option.splits)

lemma finite_partial_sequence_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_sequence f) (lists A)"
proof (rule finite_presented_onI)
  fix xs assume "xs\<in>lists A"
  then have "\<And>x. x\<in>set xs \<Longrightarrow> f x\<noteq>None" using presented by (auto simp: finite_presented_on_def)
  then show "finite_partial_sequence f xs\<noteq>None" by (simp add: finite_partial_sequence_def those_map_present)
next
  fix xs ys t assume xs: "xs\<in>lists A" and ys: "ys\<in>lists A"
    and first: "finite_partial_sequence f xs=Some t" and second: "finite_partial_sequence f ys=Some t"
  have some: "\<And>x. x\<in>set xs \<union> set ys \<Longrightarrow> f x\<noteq>None"
    using presented xs ys by (auto simp: finite_presented_on_def)
  have sx: "those (map f xs)=Some (map (the \<circ> f) xs)" by (rule those_map_present) (use some in blast)
  have sy: "those (map f ys)=Some (map (the \<circ> f) ys)" by (rule those_map_present) (use some in blast)
  have "finite_data_list (map (the \<circ> f) xs)=finite_data_list (map (the \<circ> f) ys)"
    using first second by (simp add: finite_partial_sequence_def sx sy)
  then have maps: "map (the \<circ> f) xs=map (the \<circ> f) ys" by (simp add: finite_data_list_injective)
  have "inj_on (the \<circ> f) (set xs \<union> set ys)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>set xs \<union> set ys" and y: "y\<in>set xs \<union> set ys" and same: "(the \<circ> f) x=(the \<circ> f) y"
    have fxy: "f x=f y" using same some[OF x] some[OF y] by (cases "f x"; cases "f y") auto
    show "x=y" by (rule finite_presented_on_eq[OF presented _ _ fxy]) (use x y xs ys in auto)
  qed
  then show "xs=ys" using maps by (simp add: inj_on_map_eq_map)
qed

definition finite_partial_option ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a option \<Rightarrow> finite_factor_term option" where
  "finite_partial_option f x=finite_partial_sequence f (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"

lemma finite_partial_option_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_option f) {x. set_option x\<subseteq>A}"
proof -
  have eq: "finite_partial_option f=finite_partial_sequence f \<circ> (\<lambda>x. case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"
    by (simp add: fun_eq_iff finite_partial_option_def)
  show ?thesis unfolding eq
    by (rule finite_presented_on_comp[OF finite_partial_sequence_presented[OF presented]])
      (auto simp: inj_on_def split: option.splits)
qed


definition finite_partial_collection ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a fset \<Rightarrow> finite_factor_term option" where
  "finite_partial_collection f X=(if fBall X (\<lambda>x. f x\<noteq>None)
    then Some (finite_collection_presentation (the \<circ> f) X) else None)"

lemma finite_presented_on_the:
  assumes presented: "finite_presented_on f A"
  shows "inj_on (the \<circ> f) A"
proof (rule inj_onI)
  fix x y assume x: "x\<in>A" and y: "y\<in>A" and same: "(the \<circ> f) x=(the \<circ> f) y"
  have "f x\<noteq>None" "f y\<noteq>None" using presented x y by (auto simp: finite_presented_on_def)
  then have "f x=f y" using same by (cases "f x"; cases "f y") auto
  then show "x=y" by (rule finite_presented_on_eq[OF presented x y])
qed

lemma finite_partial_collection_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_collection f) {X. fset X\<subseteq>A}"
proof (rule finite_presented_onI)
  fix X assume X: "X\<in>{X. fset X\<subseteq>A}"
  have some: "\<forall>x\<in>A. f x\<noteq>None" using presented by (simp add: finite_presented_on_def)
  have inside: "fset X\<subseteq>A" using X by simp
  have "fBall X (\<lambda>x. f x\<noteq>None)"
  proof (rule fBallI)
    fix x assume "x\<in>fset X"
    then have "x\<in>A" using inside by (rule rev_subsetD)
    then show "f x\<noteq>None" by (rule bspec[OF some])
  qed
  then show "finite_partial_collection f X\<noteq>None" by (simp add: finite_partial_collection_def)
next
  fix X Y t assume X: "X\<in>{X. fset X\<subseteq>A}" and Y: "Y\<in>{X. fset X\<subseteq>A}"
    and first: "finite_partial_collection f X=Some t" and second: "finite_partial_collection f Y=Some t"
  have tX: "finite_collection_presentation (the \<circ> f) X=t"
    using first by (simp add: finite_partial_collection_def split: if_splits)
  have tY: "finite_collection_presentation (the \<circ> f) Y=t"
    using second by (simp add: finite_partial_collection_def split: if_splits)
  have "finite_data_list (ordered_finite_terms (fimage (the \<circ> f) X))=
      finite_data_list (ordered_finite_terms (fimage (the \<circ> f) Y))"
    using tX tY by (simp only: finite_collection_presentation_def)
  then have terms: "ordered_finite_terms (fimage (the \<circ> f) X)=ordered_finite_terms (fimage (the \<circ> f) Y)"
    by (simp only: finite_data_list_injective)
  have images: "(the \<circ> f) ` fset X=(the \<circ> f) ` fset Y"
    using arg_cong[OF terms, of set] by (simp add: ordered_finite_terms_set fimage.rep_eq)
  have "fset X=fset Y"
    by (rule inj_on_image_eq_iff[THEN iffD1, OF finite_presented_on_the[OF presented] _ _ images]) (use X Y in simp_all)
  then show "X=Y" by (simp add: fset_inject)
qed

section \<open>A table of rows is the store of any listing of them\<close>

text \<open>
  A row presented as a term is the pair of its path and its value, read back by its path's own reader. A
  finite set of presented rows is presented as the path store of the rows read from it; over rows whose
  paths are distinct, that store is the store of every listing of those rows
  (@{thm [source] path_store_rows}), so its word is a function of the rows and of no listing, and equal
  words identify the rows (@{thm [source] finite_listing_store_identifies}).
\<close>

definition finite_row_read :: "finite_factor_term \<Rightarrow> bool list\<times>finite_factor_term" where
  "finite_row_read t=(case t of Finite_Pair l v \<Rightarrow> (finite_path_bits l,v) | _ \<Rightarrow> ([],t))"

lemma finite_row_read_row [simp]: "finite_row_read (finite_store_row val (l,v))=(l,val v)"
  by (simp add: finite_row_read_def finite_store_row_def finite_pair_presentation_def)

definition finite_rows_table :: "finite_factor_term fset \<Rightarrow> finite_factor_term" where
  "finite_rows_table T=finite_listing_store id (map finite_row_read (ordered_finite_terms T))"

theorem finite_rows_table_listing:
  assumes rows: "set rows=finite_row_read ` fset T" and sv: "single_valued (set rows)"
  shows "finite_rows_table T=finite_listing_store id rows"
  unfolding finite_rows_table_def finite_listing_store_def
  by (rule arg_cong[where f="finite_store id"], rule path_store_rows)
    (use rows sv in \<open>simp_all add: ordered_finite_terms_set\<close>)

theorem finite_rows_table_identifies:
  assumes shape: "\<And>t. t\<in>fset T \<union> fset T' \<Longrightarrow> \<exists>l v. t=Finite_Pair (finite_path l) v"
    and sv: "single_valued (finite_row_read ` fset T)" and sv': "single_valued (finite_row_read ` fset T')"
    and same: "finite_rows_table T=finite_rows_table T'"
  shows "T=T'"
proof -
  have "set (map finite_row_read (ordered_finite_terms T))=set (map finite_row_read (ordered_finite_terms T'))"
    by (rule finite_listing_store_identifies[OF _ _ _ same[unfolded finite_rows_table_def]])
      (use sv sv' in \<open>simp_all add: ordered_finite_terms_set\<close>)
  then have images: "finite_row_read ` fset T=finite_row_read ` fset T'" by (simp add: ordered_finite_terms_set)
  have "inj_on finite_row_read (fset T \<union> fset T')"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>fset T \<union> fset T'" and y: "y\<in>fset T \<union> fset T'"
      and read: "finite_row_read x=finite_row_read y"
    obtain l v where "x=Finite_Pair (finite_path l) v" using shape[OF x] by blast
    moreover obtain l' v' where "y=Finite_Pair (finite_path l') v'" using shape[OF y] by blast
    ultimately show "x=y" using read by (simp add: finite_row_read_def)
  qed
  then have "fset T=fset T'"
    by (rule inj_on_image_eq_iff[THEN iffD1, OF _ _ _ images]) auto
  then show ?thesis by (simp add: fset_inject)
qed

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

lemma single_valued_keyed_image:
  assumes injective: "inj_on k Q"
  shows "single_valued ((\<lambda>x. (k x,b x)) ` Q)"
  unfolding single_valued_def
proof (intro allI impI)
  fix l v w assume v: "(l,v)\<in>(\<lambda>x. (k x,b x)) ` Q" and w: "(l,w)\<in>(\<lambda>x. (k x,b x)) ` Q"
  obtain x where x: "x\<in>Q" "(l,v)=(k x,b x)" using v by (rule imageE) simp
  obtain y where y: "y\<in>Q" "(l,w)=(k y,b y)" using w by (rule imageE) simp
  have "k x=k y" using x(2) y(2) by simp
  then have "x=y" by (rule inj_onD[OF injective _ x(1) y(1)])
  then show "v=w" using x(2) y(2) by simp
qed

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
  show ?thesis unfolding rows
    by (rule single_valued_keyed_image[OF development_row_domain_inside(2)[OF domain inside]])
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
