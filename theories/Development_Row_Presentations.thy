theory Development_Row_Presentations
imports Development_Rows Development_Row_Data
begin

section \<open>The presenters of a row decode into the store's bodies\<close>

text \<open>
  The presenters of @{text Development_Row_Data} present exactly the bodies of the store's relation
  (@{const development_rows_present}). A row is the path store's row presentation, the pair of its locus
  and its body (@{const finite_store_row}), and a table is the path store of its rows
  (@{const finite_listing_store}).
\<close>

lemma decode_development_citation_data [simp]:
  "decode_finite_term (development_citation_data l)=development_row_citation l"
  by (cases l) (simp_all add: development_citation_data_def finite_store_option_def)

lemma decode_development_citations_data [simp]:
  "decode_finite_term (development_citations_data ls)=development_row_family ls"
  by (simp add: development_citations_data_def finite_sequence_presentation_def development_row_family_def comp_def)

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

section \<open>The row of a problem or a request in context is the store's row\<close>

text \<open>
  Every problem a store holds is inside the premise of its presentation in context, so a report that
  presents the problems of a store with the store's own parameters presents them injectively, and its
  rows decode to the rows the store holds; so do the requests.
\<close>

lemma development_problems_present_premise:
  assumes present: "development_problems_present key inert origin grant ps rows" and p: "p\<in>set ps"
  shows "development_row_premise origin grant p"
  using present p by (simp add: development_problems_present_def)

theorem development_problem_row_data_present_injective:
  assumes present: "development_problems_present key (decode_finite_term \<circ> inert) origin grant ps rows"
  shows "inj_on (development_problem_row_data key inert origin grant) (set ps)"
proof (rule inj_onI)
  fix p q assume p: "p\<in>set ps" and q: "q\<in>set ps"
    and same: "development_problem_row_data key inert origin grant p=development_problem_row_data key inert origin grant q"
  have loci: "inj_on (development_located_at key Development_Problem_Role) (set ps)"
    using present by (simp add: development_problems_present_def)
  have row: "development_problem_row_data key inert origin grant p=
      Some (finite_store_row (development_problem_body_data inert)
        (development_located_at key Development_Problem_Role p,
          origin p,grant p,development_contract_term (problem_contract p)))"
    by (rule development_problem_row_data_inside[OF development_problems_present_premise[OF present p]])
  show "p=q" by (rule development_problem_row_data_injective[OF loci p q row]) (use same row in simp)
qed

theorem development_problem_row_data_present_decode:
  assumes present: "development_problems_present key (decode_finite_term \<circ> inert) origin grant ps rows"
    and p: "p\<in>set ps"
  obtains x where "development_problem_row_data key inert origin grant p=Some x"
    "decode_finite_term x=Pair_Term (path_term (development_located_at key Development_Problem_Role p))
      (development_problem_body (decode_finite_term \<circ> inert) (origin p) (grant p) (problem_contract p))"
    "(development_located_at key Development_Problem_Role p,
      development_problem_body (decode_finite_term \<circ> inert) (origin p) (grant p) (problem_contract p))\<in>set rows"
proof -
  have row: "development_problem_row_data key inert origin grant p=
      Some (finite_store_row (development_problem_body_data inert)
        (development_located_at key Development_Problem_Role p,
          origin p,grant p,development_contract_term (problem_contract p)))"
    by (rule development_problem_row_data_inside[OF development_problems_present_premise[OF present p]])
  show ?thesis
    by (rule that[OF row]) (use present p in \<open>simp_all add: decode_finite_store_row
      decode_development_problem_body_data development_problems_present_def\<close>)
qed

theorem development_request_data_present_injective:
  assumes present: "development_rows_present key ekey (decode_finite_term \<circ> inert) origin grant
      supported scope decs ps rs iss rows"
  shows "inj_on (development_request_data key inert origin grant) (set rs)"
proof (rule inj_onI)
  fix r r' assume r: "r\<in>set rs" and r': "r'\<in>set rs"
    and same: "development_request_data key inert origin grant r=development_request_data key inert origin grant r'"
  have problems: "development_problems_present key (decode_finite_term \<circ> inert) origin grant ps rows"
    and requests: "development_requests_present key ekey supported scope ps rs rows"
    using development_rows_parts[OF present] by simp_all
  have inside: "fst ` set rs\<subseteq>set ps" using requests by (auto simp: development_requests_present_def)
  have loci: "inj_on (development_located_at key Development_Problem_Role) (fst ` set rs)"
    by (rule inj_on_subset[OF development_rows_problem_loci[OF present] inside])
  have keys: "inj_on key (\<Union>r\<in>set rs. fset (fst (snd (snd r))))"
    by (rule inj_on_subset[OF development_rows_key_injective[OF present]])
      (auto simp: development_row_constants_def)
  have terms: "\<And>r. r\<in>set rs \<Longrightarrow> development_contract_term (problem_contract (fst r))=fst (snd r)"
    using requests by (simp add: development_requests_present_def)
  obtain p s S E where R: "r=(p,s,S,E)" by (cases r) auto
  have "fst r\<in>set ps" using inside r by auto
  then have "development_row_premise origin grant p"
    using development_problems_present_premise[OF problems] by (simp add: R)
  then obtain x where "development_request_data key inert origin grant r=Some x"
    by (simp add: R development_request_data_def development_problem_row_data_inside)
  then show "r=r'"
    using development_request_data_injective[OF loci keys terms r r'] same by simp
qed

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
