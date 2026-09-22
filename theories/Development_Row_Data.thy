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

definition development_request_row_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_request \<Rightarrow> finite_factor_term option" where
  "development_request_row_data key inert origin grant r=(case r of (p,s,S,E) \<Rightarrow>
    map_option (\<lambda>x. Finite_Pair x (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))) (development_problem_row_data key inert origin grant p))"

lemma development_request_row_data_problem:
  "development_request_row_data key inert origin grant (p,s,S,E)=None \<longleftrightarrow>
    development_problem_row_data key inert origin grant p=None"
  by (simp add: development_request_row_data_def)

lemma development_request_row_data_formed:
  assumes row: "development_request_row_data key inert origin grant r=Some x"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "finite_term_formed x"
proof -
  obtain p s S E where r: "r=(p,s,S,E)" by (cases r) auto
  obtain y where y: "development_problem_row_data key inert origin grant p=Some y"
    and xy: "x=Finite_Pair y (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))"
    using row by (auto simp: r development_request_row_data_def)
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

theorem development_request_row_data_injective:
  assumes loci: "inj_on (development_located_at key Development_Problem_Role) (fst ` R)"
    and keys: "inj_on key (\<Union>r\<in>R. fset (fst (snd (snd r))))"
    and terms: "\<And>r. r\<in>R \<Longrightarrow> development_contract_term (problem_contract (fst r))=fst (snd r)"
    and r: "r\<in>R" and r': "r'\<in>R"
    and first: "development_request_row_data key inert origin grant r=Some x"
    and second: "development_request_row_data key inert origin grant r'=Some x"
  shows "r=r'"
proof -
  obtain p s S E where R1: "r=(p,s,S,E)" by (cases r) auto
  obtain p' s' S' E' where R2: "r'=(p',s',S',E')" by (cases r') auto
  obtain y where y: "development_problem_row_data key inert origin grant p=Some y"
    and xy: "x=Finite_Pair y (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S),E))"
    using first by (auto simp: R1 development_request_row_data_def)
  obtain y' where y': "development_problem_row_data key inert origin grant p'=Some y'"
    and xy': "x=Finite_Pair y' (finite_pair_presentation development_citations_data isabelle_entities_data
      (map key (sorted_list_of_fset S'),E'))"
    using second by (auto simp: R2 development_request_row_data_def)
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
  show ?thesis using pp ss SS EE by (simp add: R1 R2)
qed

end
