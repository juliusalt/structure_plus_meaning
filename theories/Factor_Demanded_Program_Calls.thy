theory Factor_Demanded_Program_Calls
  imports Finite_Demanded_Closures Factor_Finite_Program_Evaluation Factor_Finite_Term_Demands
begin

section \<open>Requested calls demand the calls their applications premise\<close>

text \<open>
  Evaluating a program over a demand answers exactly the demanded calls that hold, whichever
  ready demand is chosen (`finite_program_evaluation_exact`): a demand is ready when every
  application of a demanded call premises only demanded calls. The term demand of a request pairs
  every definition of the program with every component of the requested arguments, so it asks
  every definition about every component, although the requested calls need only the calls their
  own applications premise. Read from the requested calls, applications at a call and their premise
  calls are the rows and successors of the frontier traversal of `Finite_Demanded_Closures`, its
  third instance after package and proof-graph readings. The term demand bounds the traversal: an
  application is read only at a call inside it, so the traversal terminates for every program. A
  premise call outside it is demanded but never read. Where the term demand is ready no such call
  exists and the demanded calls are ready too (`finite_program_demanded_calls_ready`); wherever the
  demanded calls are ready they answer every request by its positive meaning, whether the term
  demand was ready or not.
\<close>

definition finite_application_premise_calls ::
    "('d\<times>'c\<times>finite_factor_term\<times>('a\<times>finite_factor_term) fset\<times>('s\<times>('d\<times>finite_factor_term)) fset) \<Rightarrow>
      ('d\<times>finite_factor_term) fset" where
  "finite_application_premise_calls a=(case a of (d,c,t,V,H) \<Rightarrow> fimage snd H)"

definition finite_call_applications_within where
  "finite_call_applications_within P U q=(if q |\<in>| U then finite_program_applications P {|q|} else {||})"

lemma finite_call_applications_within_universe:
  "finite_call_applications_within P U q\<noteq>{||} \<Longrightarrow> q |\<in>| U"
  by (auto simp: finite_call_applications_within_def split: if_splits)

definition finite_program_demanded_calls where
  "finite_program_demanded_calls P T R=fst (the (finite_demanded_readings
    (finite_call_applications_within P (finite_program_term_demand P T))
    finite_application_premise_calls R))"

theorem finite_program_demanded_calls_rooted:
  "finite_program_demanded_calls P T R=finite_rooted_sites
    (finite_call_applications_within P (finite_program_term_demand P T))
    finite_application_premise_calls (finite_program_term_demand P T) R"
  by (simp only: finite_program_demanded_calls_def
    finite_demanded_readings_exact[OF finite_call_applications_within_universe] fst_conv option.sel)

lemma finite_program_demanded_calls_requests: "R |\<subseteq>| finite_program_demanded_calls P T R"
  by (simp only: finite_program_demanded_calls_rooted finite_rooted_sites_roots)

text \<open>
  A requested call is demanded, so evaluating over the demanded calls answers it by its positive
  meaning whenever the evaluation is available, exactly as over the term demand; the demand is the
  least one the requests need, and nothing else about the answer depends on which demand is read.
\<close>

section \<open>Where the term demand is ready, so are the demanded calls\<close>

lemma finite_program_applications_call:
  assumes member: "q |\<in>| D"
  shows "finite_program_applications P {|q|} |\<subseteq>| finite_program_applications P D"
proof (rule fsubsetI)
  fix x assume read: "x |\<in>| finite_program_applications P {|q|}"
  obtain d c t V H where shape: "x=(d,c,t,V,H)" by (cases x) auto
  show "x |\<in>| finite_program_applications P D"
    using read member by (auto simp: shape finite_program_application_member)
qed

lemma finite_program_demanded_calls_within:
  assumes closed: "finite_program_demand_closed P (finite_program_term_demand P T)"
    and requests: "R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_demanded_calls P T R |\<subseteq>| finite_program_term_demand P T"
proof -
  let ?U="finite_program_term_demand P T"
  have step: "e |\<in>| ?U"
    if site: "d |\<in>| ?U"
      and edge: "(d,e) |\<in>| finite_row_edges (finite_call_applications_within P ?U) finite_application_premise_calls ?U"
    for d e
  proof -
    obtain x where read: "x |\<in>| finite_call_applications_within P ?U d"
      and premise: "e |\<in>| finite_application_premise_calls x"
      using edge by (auto simp: finite_row_edges_member)
    obtain d0 c t V H where shape: "x=(d0,c,t,V,H)" by (cases x) auto
    have application: "x |\<in>| finite_program_applications P ?U"
      using read finite_program_applications_call[OF site]
      by (auto simp: finite_call_applications_within_def split: if_splits)
    have rule: "((d0,t),H) |\<in>| finite_program_rule_table P ?U"
      unfolding finite_program_rule_table_def
      using application by (force simp: shape)
    have "fimage snd H |\<subseteq>| ?U"
      using fbspec[OF closed[unfolded finite_program_demand_closed_def] rule] by simp
    then show ?thesis using premise by (auto simp: shape finite_application_premise_calls_def)
  qed
  show ?thesis
    unfolding finite_program_demanded_calls_rooted
    by (rule finite_rooted_sites_least[OF requests step])
qed

lemma finite_program_demanded_calls_closed:
  assumes closed: "finite_program_demand_closed P (finite_program_term_demand P T)"
    and requests: "R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_demand_closed P (finite_program_demanded_calls P T R)"
proof -
  let ?U="finite_program_term_demand P T"
  let ?D="finite_program_demanded_calls P T R"
  have within: "?D |\<subseteq>| ?U" by (rule finite_program_demanded_calls_within[OF closed requests])
  have demanded_premises: "fimage snd H |\<subseteq>| ?D" if member: "(d,c,t,V,H) |\<in>| finite_program_applications P ?D" for d c t V H
  proof (rule fsubsetI)
    fix e assume called: "e |\<in>| fimage snd H"
    have site: "(d,t) |\<in>| ?D" using member by (simp add: finite_program_application_member)
    have inside: "(d,t) |\<in>| ?U" using within site by blast
    have read: "(d,c,t,V,H) |\<in>| finite_call_applications_within P ?U (d,t)"
      using member inside by (auto simp: finite_call_applications_within_def finite_program_application_member)
    have edge: "((d,t),e) |\<in>| finite_row_edges (finite_call_applications_within P ?U) finite_application_premise_calls ?U"
      unfolding finite_row_edges_member
      by (rule exI[of _ "(d,c,t,V,H)"])
        (use called in \<open>simp add: inside read finite_application_premise_calls_def fimage.rep_eq\<close>)
    show "e |\<in>| ?D"
      using finite_rooted_sites_step[OF site[unfolded finite_program_demanded_calls_rooted] edge]
      by (simp only: finite_program_demanded_calls_rooted)
  qed
  show ?thesis
    unfolding finite_program_demand_closed_def finite_program_rule_table_def
    using demanded_premises by force
qed

lemma finite_program_demanded_calls_covered:
  assumes covered: "finite_program_head_covered P (finite_program_term_demand P T)"
    and within: "finite_program_demanded_calls P T R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_head_covered P (finite_program_demanded_calls P T R)"
  using covered within unfolding finite_program_head_covered_def by fastforce

theorem finite_program_demanded_calls_ready:
  assumes ready: "finite_program_evaluation_ready P (finite_program_term_demand P T)"
    and requests: "R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_evaluation_ready P (finite_program_demanded_calls P T R)"
proof -
  have closed: "finite_program_demand_closed P (finite_program_term_demand P T)"
    and covered: "finite_program_head_covered P (finite_program_term_demand P T)"
    and formed: "finite_system_formed P"
    using ready by (simp_all add: finite_program_evaluation_ready_def)
  show ?thesis
    unfolding finite_program_evaluation_ready_def
    using formed finite_program_demanded_calls_closed[OF closed requests]
      finite_program_demanded_calls_covered[OF covered finite_program_demanded_calls_within[OF closed requests]]
    by blast
qed

text \<open>
  Whenever the term demand of the requests is ready, so are the calls they demand, and both evaluations
  answer every request by its positive meaning: a reading that answered over the term demand answers the
  same over the demanded calls, and only the calls it evaluates, their answers and their certificates
  shrink to what the requests need.
\<close>

section \<open>The term demand is asked through the components of the requests\<close>

lemma finite_program_term_demand_member:
  "q |\<in>| finite_program_term_demand P T \<longleftrightarrow>
    fst q |\<in>| finite_system_definitions P \<and> snd q |\<in>| ffUnion (fimage finite_term_components T)"
proof (cases q)
  case (Pair d t)
  show ?thesis
    unfolding Pair finite_program_term_demand_def finite_union_image_member finite_image_member fst_conv snd_conv
    by blast
qed

fun finite_term_contains :: "finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_term_contains (Finite_Pair x y) t \<longleftrightarrow>
    t=Finite_Pair x y \<or> finite_term_contains x t \<or> finite_term_contains y t"
| "finite_term_contains (Finite_Target a) t \<longleftrightarrow> t=Finite_Target a"
| "finite_term_contains (Finite_Payload b) t \<longleftrightarrow> t=Finite_Payload b"

lemma finite_term_contains_components: "finite_term_contains s t \<longleftrightarrow> t |\<in>| finite_term_components s"
  by (induction s) auto

lemma finite_program_demanded_calls_contained_code [code]:
  "finite_program_demanded_calls P T R=(let D=finite_system_definitions P in
    fst (the (finite_demanded_readings
      (\<lambda>q. if fst q |\<in>| D \<and> fBex T (\<lambda>s. finite_term_contains s (snd q))
        then finite_program_applications P {|q|} else {||})
      finite_application_premise_calls R)))"
proof -
  have read: "finite_call_applications_within P (finite_program_term_demand P T)=
      (\<lambda>q. if fst q |\<in>| finite_system_definitions P \<and> fBex T (\<lambda>s. finite_term_contains s (snd q))
        then finite_program_applications P {|q|} else {||})"
    by (rule ext) (simp only: finite_call_applications_within_def finite_program_term_demand_member
      finite_union_image_member finite_term_contains_components Bex_def)
  show ?thesis by (simp only: finite_program_demanded_calls_def read Let_def)
qed

text \<open>
  A call is tested against the term demand by looking for its argument inside the requested
  arguments, so the components of a large argument are never listed; a stage whose requests read
  one large term, as a scope review does, searches it once for each call it reads.
\<close>

section \<open>A request demands the calls its applications premise, wherever they lead\<close>

text \<open>
  A requested call demands the calls its applications premise, and those demand theirs. Read at
  every demanded call, this is the frontier traversal of \<open>Finite_Demanded_Closures\<close> without a
  universe, and whenever it returns, the calls it read are closed under the program's applications
  (\<open>finite_program_call_closure_closed\<close>), so evaluating over them answers every request by its
  positive meaning. The term demand is not needed to bound it: a program whose premises call only on
  components of the requested arguments stays inside the term demand, and there the traversal is the
  one bounded by it (\<open>finite_program_call_closure_term\<close>); a program whose premises pair components
  into new arguments, as every definition that carries a context through a recursion does, is
  followed to exactly the calls it demands. A program whose demanded calls are infinite never
  returns; the closure is then the requests alone, and no evaluation over it is available.
\<close>

definition finite_program_call_readings where
  "finite_program_call_readings P R=finite_demanded_readings (\<lambda>q. finite_program_applications P {|q|})
    finite_application_premise_calls R"

definition finite_program_call_closure where
  "finite_program_call_closure P R=(case finite_program_call_readings P R of None \<Rightarrow> R | Some (S,A) \<Rightarrow> S)"

lemma finite_program_call_closure_requests: "R |\<subseteq>| finite_program_call_closure P R"
proof (cases "finite_program_call_readings P R")
  case None
  then show ?thesis by (simp add: finite_program_call_closure_def)
next
  case (Some r)
  obtain S A where r: "r=(S,A)" by (cases r)
  have "R |\<subseteq>| S"
    by (rule finite_demanded_readings_closed(1)[OF Some[unfolded finite_program_call_readings_def r]])
  then show ?thesis by (simp add: finite_program_call_closure_def Some r)
qed

theorem finite_program_call_closure_closed:
  assumes available: "finite_program_call_readings P R=Some (S,A)"
  shows "finite_program_demand_closed P (finite_program_call_closure P R)"
proof -
  have D: "finite_program_call_closure P R=S" by (simp add: finite_program_call_closure_def available)
  have closed: "e |\<in>| S"
    if "q |\<in>| S" "x |\<in>| finite_program_applications P {|q|}" "e |\<in>| finite_application_premise_calls x" for q x e
    by (rule finite_demanded_readings_closed(2)[OF available[unfolded finite_program_call_readings_def] that])
  have demanded_premises: "fimage snd H |\<subseteq>| S"
    if member: "(d,c,t,V,H) |\<in>| finite_program_applications P S" for d c t V H
  proof (rule fsubsetI)
    fix e assume called: "e |\<in>| fimage snd H"
    have site: "(d,t) |\<in>| S" using member by (simp add: finite_program_application_member)
    have read: "(d,c,t,V,H) |\<in>| finite_program_applications P {|(d,t)|}"
      using member by (simp add: finite_program_application_member)
    show "e |\<in>| S"
      by (rule closed[OF site read]) (use called in \<open>simp add: finite_application_premise_calls_def\<close>)
  qed
  show ?thesis
    unfolding D finite_program_demand_closed_def finite_program_rule_table_def
    using demanded_premises by force
qed

theorem finite_program_call_closure_term:
  assumes closed: "finite_program_demand_closed P (finite_program_term_demand P T)"
    and requests: "R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_call_closure P R=finite_program_demanded_calls P T R"
proof -
  let ?U="finite_program_term_demand P T"
  have universe: "e |\<in>| ?U"
    if site: "d |\<in>| ?U" and read: "x |\<in>| finite_program_applications P {|d|}"
      and premise: "e |\<in>| finite_application_premise_calls x" for d x e
  proof -
    obtain d0 c t V H where shape: "x=(d0,c,t,V,H)" by (cases x) auto
    have application: "x |\<in>| finite_program_applications P ?U"
      using read finite_program_applications_call[OF site] by blast
    have rule: "((d0,t),H) |\<in>| finite_program_rule_table P ?U"
      unfolding finite_program_rule_table_def using application by (force simp: shape)
    have "fimage snd H |\<subseteq>| ?U"
      using fbspec[OF closed[unfolded finite_program_demand_closed_def] rule] by simp
    then show ?thesis using premise by (auto simp: shape finite_application_premise_calls_def)
  qed
  have read: "(\<lambda>q. if q |\<in>| ?U then finite_program_applications P {|q|} else {||})=
      finite_call_applications_within P ?U"
    by (rule ext) (simp only: finite_call_applications_within_def)
  have readings: "finite_program_call_readings P R=
      finite_demanded_readings (finite_call_applications_within P ?U) finite_application_premise_calls R"
    unfolding finite_program_call_readings_def read[symmetric]
    by (rule finite_demanded_readings_within[OF requests universe])
  show ?thesis
    by (simp add: finite_program_call_closure_def readings finite_program_demanded_calls_def
      finite_demanded_readings_exact[OF finite_call_applications_within_universe])
qed

theorem finite_program_call_closure_ready:
  assumes ready: "finite_program_evaluation_ready P (finite_program_term_demand P T)"
    and requests: "R |\<subseteq>| finite_program_term_demand P T"
  shows "finite_program_evaluation_ready P (finite_program_call_closure P R)"
proof -
  have closed: "finite_program_demand_closed P (finite_program_term_demand P T)"
    using ready by (simp add: finite_program_evaluation_ready_def)
  show ?thesis
    unfolding finite_program_call_closure_term[OF closed requests]
    by (rule finite_program_demanded_calls_ready[OF ready requests])
qed

theorem finite_program_call_closure_available_ready:
  assumes formed: "finite_system_formed P"
    and covered: "finite_program_head_covered P (finite_program_call_closure P R)"
    and available: "finite_program_call_readings P R=Some (S,A)"
  shows "finite_program_evaluation_ready P (finite_program_call_closure P R)"
  unfolding finite_program_evaluation_ready_def
  using formed covered finite_program_call_closure_closed[OF available] by blast

text \<open>
  Wherever the term demand of the requested arguments is ready, the calls the requests demand are
  the ones the bounded traversal read, so every evaluation that was available over them is available
  and unchanged; wherever the traversal returns on a program whose clauses bind every variable in
  their heads, the evaluation over what it read is available, including where the term demand was
  never closed.
\<close>

end
