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

section \<open>The two generic presentations of the path store are injective\<close>

lemma finite_store_option_injective [intro]:
  assumes injective: "inj f"
  shows "inj (finite_store_option f)"
proof (rule injI)
  fix x y assume "finite_store_option f x=finite_store_option f y"
  then show "x=y" using injective by (cases x; cases y) (auto simp: finite_store_option_def dest: injD)
qed

lemma finite_store_injective [intro]:
  assumes injective: "inj f"
  shows "inj (finite_store f)"
proof (rule injI)
  fix S T show "finite_store f S=finite_store f T \<Longrightarrow> S=T"
  proof (induction S arbitrary: T)
    case Empty_Store
    then show ?case by (cases T) simp_all
  next
    case (Store_Node v l r)
    from Store_Node.prems obtain v' l' r' where T: "T=Store_Node v' l' r'"
      and head: "finite_store_option f v=finite_store_option f v'"
      and left: "finite_store f l=finite_store f l'" and right: "finite_store f r=finite_store f r'"
      by (cases T) simp_all
    have "v=v'" by (rule injD[OF finite_store_option_injective[OF injective] head])
    moreover have "l=l'" by (rule Store_Node.IH(1)[OF left])
    moreover have "r=r'" by (rule Store_Node.IH(2)[OF right])
    ultimately show ?case by (simp add: T)
  qed
qed

lemma finite_path_formed [simp]: "finite_term_formed (finite_path bs)"
  by (induction bs) (simp_all add: finite_path_def finite_bit_def octets_formed_def)

lemma finite_store_option_formed:
  assumes "\<And>x. finite_term_formed (f x)"
  shows "finite_term_formed (finite_store_option f v)"
  using assms by (cases v) (simp_all add: finite_store_option_def octets_formed_def)

lemma finite_store_formed:
  assumes "\<And>x. finite_term_formed (f x)"
  shows "finite_term_formed (finite_store f T)"
  by (induction T) (simp_all add: octets_formed_def finite_store_option_formed[OF assms])

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

lemma development_problem_body_data_injective [intro]:
  assumes "inj inert"
  shows "inj (development_problem_body_data inert)"
  unfolding development_problem_body_data_def
  by (intro finite_pair_presentation_injective development_citation_data_injective assms)

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

definition development_row_data ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> bool list\<times>'v \<Rightarrow> finite_factor_term" where
  "development_row_data body=finite_pair_presentation finite_path body"

definition development_table_data ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> (bool list\<times>'v) list \<Rightarrow> finite_factor_term" where
  "development_table_data body rows=finite_store body (path_store rows)"

lemma development_row_data_injective [intro]:
  assumes "inj body"
  shows "inj (development_row_data body)"
  unfolding development_row_data_def by (intro finite_pair_presentation_injective finite_path_injective assms)

lemma development_row_data_formed:
  assumes "finite_term_formed (body v)"
  shows "finite_term_formed (development_row_data body (l,v))"
  using assms by (simp add: development_row_data_def)

lemma development_table_data_formed:
  assumes "\<And>v. finite_term_formed (body v)"
  shows "finite_term_formed (development_table_data body rows)"
  unfolding development_table_data_def by (rule finite_store_formed[OF assms])

text \<open>
  A table presents the rows it holds, not the order they were listed in: two single-valued listings, which
  is the locus's own "at most one row", with equal presentations hold the same rows.
\<close>

theorem development_table_data_injective:
  assumes body: "inj body" and sv: "single_valued (set rows)" and sv': "single_valued (set rows')"
    and same: "development_table_data body rows=development_table_data body rows'"
  shows "set rows=set rows'"
proof -
  have T: "path_store rows=path_store rows'"
    using injD[OF finite_store_injective[OF body]] same by (simp add: development_table_data_def)
  have pairs: "(q,v)\<in>set rows \<longleftrightarrow> (q,v)\<in>set rows'" for q v
  proof -
    have "(q,v)\<in>set rows \<longleftrightarrow> store_lookup (path_store rows) q=Some v"
      by (rule path_store_lookup[OF sv, symmetric])
    also have "\<dots> \<longleftrightarrow> store_lookup (path_store rows') q=Some v" by (simp only: T)
    also have "\<dots> \<longleftrightarrow> (q,v)\<in>set rows'" by (rule path_store_lookup[OF sv'])
    finally show ?thesis .
  qed
  show ?thesis by (rule set_eqI) (metis pairs surj_pair)
qed

lemma decode_development_row_data:
  "decode_finite_term (development_row_data body (l,v))=Pair_Term (path_term l) (decode_finite_term (body v))"
  by (simp add: development_row_data_def)

lemma decode_development_table_data:
  "decode_finite_term (development_table_data body rows)=store_term (decode_finite_term \<circ> body) (path_store rows)"
  by (simp add: development_table_data_def decode_finite_store)

end
