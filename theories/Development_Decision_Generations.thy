theory Development_Decision_Generations
  imports Development_Certified_Generations
begin

section \<open>A decision is admitted as a generation at the locus of its kind\<close>

text \<open>
  The history of the first loop retains the evidence of each decision: the executed selection packet
  with the problems it admitted, and every issued request with the library reading it rested on. Each
  decision is also admitted as a generation at the locus of its kind, as an answer is: its payload is the
  decision presented with the names it uses, and its cause is a certified call of the policy that lists
  that payload. A decision generation is constructed from the decision the loop made, the problems the
  native selection admitted and the requests issued as leaves, so the certificate is exact while the
  rule that admits is the constructor's contract, as an answer's acceptance by its checked context is.
  No schedule is recorded beside the selection: the admitted problems are the group of independent work
  (\<open>development_selected_independent\<close>), so a schedule would restate the selection's payload.
\<close>

section \<open>Decisions are presented with the names they use\<close>

definition development_loci_data :: "finite_factor_term fset \<Rightarrow> finite_factor_term" where
  "development_loci_data=finite_collection_presentation id"

lemma development_loci_data_injective [intro]: "inj development_loci_data"
  unfolding development_loci_data_def by (intro finite_collection_presentation_injective) simp

text \<open>
  A selection presents the loci of the problems it admitted, each cited by its locus: a problem stands at
  its locus whatever its origin, so problems of one kind about one constant are one admitted problem.
\<close>

definition development_selection_payload :: "String.literal list \<Rightarrow> development_problem list \<Rightarrow> finite_factor_term" where
  "development_selection_payload names xs=development_loci_data
     (fset_of_list (map (development_problem_citation Development_Problem_Role) xs))"

text \<open>
  An issue presents the locus of its problem, the names of the support its answer may use and the library
  reading it rested on, every subproblem of that reading by its locus. The request's context is the refined
  entities with the declarations of the support, read from the state the request was made in, so it is not
  presented again.
\<close>

definition development_support_names :: "String.literal list \<Rightarrow> nat fset \<Rightarrow> String.literal fset" where
  "development_support_names names support=
     fset_of_list (List.map_filter (isabelle_name_at names) (sorted_list_of_fset support))"

definition development_reading_data ::
    "String.literal list \<Rightarrow> (nat\<times>development_problem) fset fset \<Rightarrow> finite_factor_term" where
  "development_reading_data names=finite_collection_presentation (finite_collection_presentation
     (finite_pair_presentation isabelle_position_data (development_problem_citation Development_Problem_Role)))"

definition development_issue_payload ::
    "String.literal list \<Rightarrow> development_request \<Rightarrow> (nat\<times>development_problem) fset fset \<Rightarrow> finite_factor_term" where
  "development_issue_payload names r reading=Finite_Pair (development_problem_citation Development_Problem_Role (fst r))
     (Finite_Pair (finite_collection_presentation isabelle_name_data (development_support_names names (fst (snd (snd r)))))
       (development_reading_data names reading))"

section \<open>A selection and an issue are recorded at their loci\<close>

definition development_selection_generation_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_problem list \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_selection_generation_using construct judge names xs H rows=
     Option.bind (development_data_target development_selection_locus)
       (\<lambda>l. development_payload_generation_using construct judge (development_selection_payload names xs) H l rows)"

definition development_issue_generation_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_request \<Rightarrow>
      (nat\<times>development_problem) fset fset \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
      development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_issue_generation_using construct judge names r reading H rows=
     Option.bind (development_locus_target Development_Issue_Role (fst r))
       (\<lambda>l. development_payload_generation_using construct judge (development_issue_payload names r reading) H l rows)"

definition development_selection_generation_with ::
    "development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_problem list \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_selection_generation_with=development_selection_generation_using finite_construct_generation_record"

definition development_issue_generation_with ::
    "development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_request \<Rightarrow> (nat\<times>development_problem) fset fset \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_issue_generation_with=development_issue_generation_using finite_construct_generation_record"

lemma development_selection_generation_with_unfold:
  "development_selection_generation_with judge names xs H rows=Option.bind (development_data_target development_selection_locus)
     (\<lambda>l. development_payload_generation_with judge (development_selection_payload names xs) H l rows)"
  by (simp only: development_selection_generation_with_def development_selection_generation_using_def
    development_payload_generation_using_original)

lemma development_issue_generation_with_unfold:
  "development_issue_generation_with judge names r reading H rows=
     Option.bind (development_locus_target Development_Issue_Role (fst r))
       (\<lambda>l. development_payload_generation_with judge (development_issue_payload names r reading) H l rows)"
  by (simp only: development_issue_generation_with_def development_issue_generation_using_def
    development_payload_generation_using_original)

lemma development_decision_generations_known:
  assumes formed: "finite_environment_formed H"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) rows"
  shows "development_selection_generation_using finite_construct_known_original_generation judge names xs H rows=
      development_selection_generation_with judge names xs H rows"
    "development_issue_generation_using finite_construct_known_original_generation judge names r reading H rows=
      development_issue_generation_with judge names r reading H rows"
  by (simp_all only: development_selection_generation_using_def development_selection_generation_with_unfold
    development_issue_generation_using_def development_issue_generation_with_unfold
    development_payload_generation_using_known[OF formed rows])

lemma development_selection_generation_recorded:
  assumes built: "development_selection_generation_with judge names xs H rows=Some (B,u,G)"
  shows "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
proof -
  obtain l where generated: "development_payload_generation_with judge (development_selection_payload names xs) H l rows=
      Some (B,u,G)"
    using built by (auto simp: development_selection_generation_with_unfold bind_eq_Some_conv)
  show "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    by (rule development_payload_generation_recorded[OF generated])+
qed

lemma development_issue_generation_recorded:
  assumes built: "development_issue_generation_with judge names r reading H rows=Some (B,u,G)"
  shows "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
proof -
  obtain l where generated: "development_payload_generation_with judge (development_issue_payload names r reading) H l rows=
      Some (B,u,G)"
    using built by (auto simp: development_issue_generation_with_unfold bind_eq_Some_conv)
  show "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    by (rule development_payload_generation_recorded[OF generated])+
qed

lemma development_selection_generation_fields:
  assumes built: "development_selection_generation_with judge names xs H rows=Some (B,u,G)"
  shows "development_data_target development_selection_locus=Some (generation_locus G)"
    "finite_generation_formed G" "generation_predecessors G=fset_of_list (map snd rows)"
proof -
  obtain l where locus: "development_data_target development_selection_locus=Some l"
    and generated: "development_payload_generation_with judge (development_selection_payload names xs) H l rows=Some (B,u,G)"
    using built by (auto simp: development_selection_generation_with_unfold bind_eq_Some_conv)
  note fields=development_payload_generation_fields[OF generated]
  show "development_data_target development_selection_locus=Some (generation_locus G)"
    using locus fields(1) by simp
  show "finite_generation_formed G" by (rule fields(2))
  show "generation_predecessors G=fset_of_list (map snd rows)" by (rule fields(3))
qed

lemma development_issue_generation_fields:
  assumes built: "development_issue_generation_with judge names r reading H rows=Some (B,u,G)"
  shows "development_locus_target Development_Issue_Role (fst r)=Some (generation_locus G)"
    "finite_generation_formed G" "generation_predecessors G=fset_of_list (map snd rows)"
proof -
  obtain l where locus: "development_locus_target Development_Issue_Role (fst r)=Some l"
    and generated: "development_payload_generation_with judge (development_issue_payload names r reading) H l rows=Some (B,u,G)"
    using built by (auto simp: development_issue_generation_with_unfold bind_eq_Some_conv)
  note fields=development_payload_generation_fields[OF generated]
  show "development_locus_target Development_Issue_Role (fst r)=Some (generation_locus G)"
    using locus fields(1) by simp
  show "finite_generation_formed G" by (rule fields(2))
  show "generation_predecessors G=fset_of_list (map snd rows)" by (rule fields(3))
qed

text \<open>
  With the judgment itself as judge, the cause of a recorded selection or issue is a certified call of the
  policy that lists exactly its payload: the contract of any recorded payload, instantiated.
\<close>

theorem development_selection_generation_certified:
  assumes built: "development_selection_generation_with development_payload_judgment names xs H rows=Some (B,u,G)"
  obtains R d K pu E root where "development_data_target development_selection_locus=Some (generation_locus G)"
    "development_data_target (development_selection_payload names xs)=Some (generation_payload G)"
    "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_predecessors G=fset_of_list (map snd rows)"
proof -
  obtain l where locus: "development_data_target development_selection_locus=Some l"
    and generated: "development_payload_generation_with development_payload_judgment
      (development_selection_payload names xs) H l rows=Some (B,u,G)"
    using built by (auto simp: development_selection_generation_with_unfold bind_eq_Some_conv)
  obtain R d K pu E root where target: "development_data_target (development_selection_payload names xs)=Some (generation_payload G)"
    and whole: "generation_payload G=Finite_Whole R"
    and policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and cause: "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    and fields: "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
    by (rule development_payload_generation_certified[OF generated]) blast
  have "development_data_target development_selection_locus=Some (generation_locus G)"
    using locus fields(1) by simp
  then show thesis by (rule that[OF _ target whole policy cause fields(2)])
qed

theorem development_issue_generation_certified:
  assumes built: "development_issue_generation_with development_payload_judgment names r reading H rows=Some (B,u,G)"
  obtains R d K pu E root where "development_locus_target Development_Issue_Role (fst r)=Some (generation_locus G)"
    "development_data_target (development_issue_payload names r reading)=Some (generation_payload G)"
    "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_predecessors G=fset_of_list (map snd rows)"
proof -
  obtain l where locus: "development_locus_target Development_Issue_Role (fst r)=Some l"
    and generated: "development_payload_generation_with development_payload_judgment
      (development_issue_payload names r reading) H l rows=Some (B,u,G)"
    using built by (auto simp: development_issue_generation_with_unfold bind_eq_Some_conv)
  obtain R d K pu E root where target: "development_data_target (development_issue_payload names r reading)=Some (generation_payload G)"
    and whole: "generation_payload G=Finite_Whole R"
    and policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and cause: "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    and fields: "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
    by (rule development_payload_generation_certified[OF generated]) blast
  have "development_locus_target Development_Issue_Role (fst r)=Some (generation_locus G)"
    using locus fields(1) by simp
  then show thesis by (rule that[OF _ target whole policy cause fields(2)])
qed

section \<open>The decisions of a round are the ones the loop made\<close>

text \<open>
  A round of the loop selects the next problems by the native question on their readiness and issues
  every selected leaf of the library. The decisions it records are exactly those: every selected problem
  is ready, and every issued request is the request of a selected problem that is a leaf of the library,
  with the library reading it rested on. A decision generation is recorded only for these.
\<close>

definition development_loop_decisions ::
    "development_dependencies \<Rightarrow> (development_problem \<Rightarrow> development_request option) \<Rightarrow> development_loop \<Rightarrow>
      (development_loop\<times>development_problem list\<times>(development_request\<times>(nat\<times>development_problem) fset fset) list) option" where
  "development_loop_decisions L request_of loop=(case development_loop_selection loop of
     None \<Rightarrow> None
   | Some (selected,xs) \<Rightarrow> (case development_loop_issue L request_of selected xs of (issued_loop,issued,unissued) \<Rightarrow>
       Some (issued_loop,xs,map (\<lambda>r. (r,development_library_reading L (fst r))) issued)))"

theorem development_loop_decisions_made:
  assumes decided: "development_loop_decisions L request_of (S,ps,D,answered,history)=Some (loop',xs,issues)"
  shows "\<And>p. p\<in>set xs \<Longrightarrow> p\<in>set ps \<and> development_ready D answered p"
    and "\<And>r reading. (r,reading)\<in>set issues \<Longrightarrow> fst r\<in>set xs \<and> development_issuable D L answered (fst r) \<and>
      reading=development_library_reading L (fst r) \<and> reading={||} \<and> request_of (fst r)=Some r"
proof -
  obtain selected ys where selection: "development_loop_selection (S,ps,D,answered,history)=Some (selected,ys)"
    using decided by (auto simp: development_loop_decisions_def split: option.splits)
  obtain issued_loop issued unissued where issuing: "development_loop_issue L request_of selected ys=(issued_loop,issued,unissued)"
    by (cases "development_loop_issue L request_of selected ys") auto
  have fields: "xs=ys" "issues=map (\<lambda>r. (r,development_library_reading L (fst r))) issued"
    using decided by (simp_all add: development_loop_decisions_def selection issuing)
  obtain Q where state: "selected=(S,ps,D,answered,history@[Development_Selection_Record (native_development_packet Q) ys])"
    using selection by (auto simp: development_loop_selection_def Let_def split: option.splits)
  show "p\<in>set ps \<and> development_ready D answered p" if member: "p\<in>set xs" for p
    using development_loop_selection_ready(1)[OF selection] member by (simp add: fields(1))
  show "fst r\<in>set xs \<and> development_issuable D L answered (fst r) \<and>
      reading=development_library_reading L (fst r) \<and> reading={||} \<and> request_of (fst r)=Some r"
    if member: "(r,reading)\<in>set issues" for r reading
  proof -
    have issued: "r\<in>set issued" and read: "reading=development_library_reading L (fst r)"
      using member by (auto simp: fields(2))
    note leaf=development_loop_issue_leaf[OF issuing[unfolded state] issued]
    show ?thesis using leaf read by (simp add: fields(1))
  qed
qed

section \<open>An answer cites the issue it answers\<close>

text \<open>
  An issue is recorded in the environment of the incumbent its request was made against and cites that
  incumbent and, when a selection admitted the problem, the selection recorded beside it; a request made
  on demand has no selection. The row an answer to the request cites is then the issue alone: the incumbent
  is already its predecessor.
\<close>

definition development_recorded_issue_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_problem list option \<Rightarrow>
      development_request \<Rightarrow> (nat\<times>development_problem) fset fset \<Rightarrow>
      local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation \<Rightarrow>
      (local_address option finite_artifact_environment\<times>development_generation_row list\<times>finite_generation) option" where
  "development_recorded_issue_using construct judge names selection r reading incumbent=(case incumbent of (B,u,I) \<Rightarrow>
     Option.bind (case selection of
         None \<Rightarrow> Some (B,[])
       | Some xs \<Rightarrow> map_option (\<lambda>(B1,us,S). (B1,[((us,[]),S)]))
           (development_selection_generation_using construct judge names xs B []))
       (\<lambda>(B1,cited). map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q))
          (development_issue_generation_using construct judge names r reading B1 (((u,[]),I)#cited))))"

definition development_recorded_issue_with ::
    "development_payload_judge \<Rightarrow> String.literal list \<Rightarrow> development_problem list option \<Rightarrow> development_request \<Rightarrow>
      (nat\<times>development_problem) fset fset \<Rightarrow>
      local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation \<Rightarrow>
      (local_address option finite_artifact_environment\<times>development_generation_row list\<times>finite_generation) option" where
  "development_recorded_issue_with=development_recorded_issue_using finite_construct_generation_record"

lemma development_recorded_issue_with_unfold:
  "development_recorded_issue_with judge names selection r reading incumbent=(case incumbent of (B,u,I) \<Rightarrow>
     Option.bind (case selection of
         None \<Rightarrow> Some (B,[])
       | Some xs \<Rightarrow> map_option (\<lambda>(B1,us,S). (B1,[((us,[]),S)])) (development_selection_generation_with judge names xs B []))
       (\<lambda>(B1,cited). map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q))
          (development_issue_generation_with judge names r reading B1 (((u,[]),I)#cited))))"
  by (simp only: development_recorded_issue_with_def development_recorded_issue_using_def
    development_selection_generation_with_def development_issue_generation_with_def)

lemma development_recorded_issue_fields:
  assumes recorded: "development_recorded_issue_with judge names selection r reading (B,u,I)=Some (B2,rows,Q)"
  obtains B1 cited uq where "development_issue_generation_with judge names r reading B1 (((u,[]),I)#cited)=Some (B2,uq,Q)"
    "rows=[((uq,[]),Q)]"
    "development_locus_target Development_Issue_Role (fst r)=Some (generation_locus Q)"
    "finite_generation_formed Q" "I |\<in>| generation_predecessors Q"
proof -
  obtain B1 cited where cited: "(case selection of None \<Rightarrow> Some (B,[])
       | Some xs \<Rightarrow> map_option (\<lambda>(B1,us,S). (B1,[((us,[]),S)])) (development_selection_generation_with judge names xs B []))=
      Some (B1,cited)"
    and issued: "map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q))
      (development_issue_generation_with judge names r reading B1 (((u,[]),I)#cited))=Some (B2,rows,Q)"
    using recorded by (auto simp: development_recorded_issue_with_unfold bind_eq_Some_conv)
  obtain uq where built: "development_issue_generation_with judge names r reading B1 (((u,[]),I)#cited)=Some (B2,uq,Q)"
    and rows: "rows=[((uq,[]),Q)]"
    using issued by auto
  note fields=development_issue_generation_fields[OF built]
  have "I |\<in>| generation_predecessors Q" using fields(3) by simp
  then show thesis by (rule that[OF built rows fields(1,2)])
qed

lemma development_recorded_issue_recorded:
  assumes recorded: "development_recorded_issue_with judge names selection r reading (B,u,I)=Some (B2,rows,Q)"
  shows "finite_environment_formed B2" "list_all (\<lambda>(d,G). finite_check_generation G B2 (fst d) (snd d)) rows"
proof -
  obtain B1 cited uq where issued: "development_issue_generation_with judge names r reading B1 (((u,[]),I)#cited)=
      Some (B2,uq,Q)" and rows: "rows=[((uq,[]),Q)]"
    by (rule development_recorded_issue_fields[OF recorded]) blast
  note fields=development_issue_generation_recorded[OF issued]
  show "finite_environment_formed B2" by (rule fields(1))
  show "list_all (\<lambda>(d,G). finite_check_generation G B2 (fst d) (snd d)) rows"
    using fields(3) by (simp add: rows)
qed

text \<open>
  The issue is recorded in the environment its incumbent was recorded in, which is formed and reads the
  incumbent back at its site; the selection it cites is recorded there first, which keeps both. Every
  reading the issue cites is therefore known, and it is recorded with the known constructor.
\<close>

lemma development_recorded_issue_using_known:
  assumes formed: "finite_environment_formed B" and incumbent: "finite_check_generation I B u []"
  shows "development_recorded_issue_using finite_construct_known_original_generation judge names selection r reading (B,u,I)=
    development_recorded_issue_with judge names selection r reading (B,u,I)"
proof (cases selection)
  case None
  have issued: "development_issue_generation_using finite_construct_known_original_generation judge names r reading B
      [((u,[]),I)]=development_issue_generation_with judge names r reading B [((u,[]),I)]"
    by (rule development_decision_generations_known(2)[OF formed]) (simp add: incumbent)
  show ?thesis by (simp add: None issued development_recorded_issue_using_def development_recorded_issue_with_unfold)
next
  case (Some xs)
  note chosen=this
  have selected: "development_selection_generation_using finite_construct_known_original_generation judge names xs B []=
      development_selection_generation_with judge names xs B []"
    by (rule development_decision_generations_known(1)[OF formed]) simp
  show ?thesis
  proof (cases "development_selection_generation_with judge names xs B []")
    case None
    then show ?thesis
      by (simp add: chosen selected development_recorded_issue_using_def development_recorded_issue_with_unfold)
  next
    case (Some result)
    obtain B1 us S where built: "development_selection_generation_with judge names xs B []=Some (B1,us,S)"
      using Some by (cases result) auto
    note recorded=development_selection_generation_recorded[OF built]
    have carried: "finite_check_generation I B1 u []"
      by (rule finite_check_generation_included[OF incumbent recorded(2) recorded(1)])
    have issued: "development_issue_generation_using finite_construct_known_original_generation judge names r reading B1
        [((u,[]),I),((us,[]),S)]=development_issue_generation_with judge names r reading B1 [((u,[]),I),((us,[]),S)]"
      by (rule development_decision_generations_known(2)[OF recorded(1)]) (simp add: carried recorded(3))
    show ?thesis
      by (simp add: chosen selected built issued development_recorded_issue_using_def
        development_recorded_issue_with_unfold)
  qed
qed

end
