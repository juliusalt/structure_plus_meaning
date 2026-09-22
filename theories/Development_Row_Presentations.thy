theory Development_Row_Presentations
imports Development_Rows
begin

section \<open>A row is presented through the generic presentations of its parts\<close>

text \<open>
  The development's notions are rows at loci (the relation @{const development_rows_present}): a locus is a path, a problem's
  body is its origin citation, its authority citation and its contract term carried inert, a request's
  body is its support and its context, two families of citations, and an issue's body is the family of
  decompositions that applied. Their executable presentations are composed here from the generic ones and
  from the path store's own, and each states injectivity and nothing else, so that any other member of the
  class may replace it. No presenter carries a tag, a position in a name table, or a field the locus
  already says: the kind and the role are prefixes of the locus, the subject is its key, and the contract
  term's presentation is supplied, as the relation takes its inert presentation.

  The shape followed is the readiness line's: a row is the pair of its locus and its body
  (@{const finite_readiness_row}), and a table is the path store of its rows
  (@{const finite_readiness_table}).
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

lemma decode_development_citation_data [simp]:
  "decode_finite_term (development_citation_data l)=development_row_citation l"
  by (cases l) (simp_all add: development_citation_data_def finite_store_option_def)

lemma decode_development_citations_data [simp]:
  "decode_finite_term (development_citations_data ls)=development_row_family ls"
  by (simp add: development_citations_data_def finite_sequence_presentation_def development_row_family_def comp_def)

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
  as the relation asks of it (@{text development_rows_inert_injective}).
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

text \<open>
  Each body presents exactly the body of the relation: a problem's with the contract term its locus
  leaves (@{const development_contract_term}), a request's and an issue's as they are.
\<close>

lemma decode_development_problem_body_data:
  "decode_finite_term (development_problem_body_data inert (x,y,development_contract_term k))=
    development_problem_body (decode_finite_term \<circ> inert) x y k"
  by (simp add: development_problem_body_data_def development_problem_body_def)

lemma decode_development_request_body_data:
  "decode_finite_term (development_request_body_data (S,E))=development_request_body S E"
  by (simp add: development_request_body_data_def development_request_body_def)

lemma decode_development_issue_body_data:
  "decode_finite_term (development_issue_body_data hs)=readiness_decompositions hs"
  by (simp add: development_issue_body_data_def finite_sequence_presentation_def
    readiness_decompositions_family comp_def)

section \<open>A row is its locus with its body, and a table is the store of its rows\<close>

text \<open>
  A development row and a development table are the store's row and listing presentations with the
  presentation of the body: their injectivity, formation and decoding are the store's
  (@{thm [source] finite_store_row_injective}, @{thm [source] finite_listing_store_exact},
  @{thm [source] finite_listing_store_formed}, @{thm [source] decode_finite_listing_store}). Over
  single-valued listings, the locus's own "at most one row", a table presents exactly the rows it holds.
\<close>

abbreviation development_row_data ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> bool list\<times>'v \<Rightarrow> finite_factor_term" where
  "development_row_data \<equiv> finite_store_row"

abbreviation development_table_data ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> (bool list\<times>'v) list \<Rightarrow> finite_factor_term" where
  "development_table_data \<equiv> finite_listing_store"

end
