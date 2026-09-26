theory Factor_Resolution_Carriers
  imports Factor_Resolution_Socket_Discharges Factor_Substitution Presentation_Function_Witnesses
begin

text \<open>
  Carriers (R5d of DECISIONS.md "The native evaluator constructs the missing witnesses by resolution", its addition
  "The given's remaining producers: views, carriers and narrowed sockets", (b)). A carrier is declared at a site with
  a view Pair pi po, pi its carried inputs and fixed parts, po its outputs, and a correspondence on each; its
  obligation (@{text carrier_discharged}): every answer (x,y) and every x' corresponding to x give an answer (x',y')
  with y' corresponding to y, so the output's class is the image of the input's. A consumer is the carrier with no
  output (@{text consumer_discharged_carrier}); a presented function witness discharges a carrier along its direction
  (@{text function_witness_carrier}), a presented function contract through its witness
  (@{text function_contract_carrier}); a witness read against its direction discharges one along the input's
  presentation, where every presentation of the image is reached from a presentation of the subject
  (@{text witness_along_carrier}), and a presented relation contract one by its preimage
  (@{text relation_contract_carrier_preimage}). The search reads no carrier: carriers discharge a socket's
  clause-level obligation, the socket's class carried along the clause's acyclic dataflow to the head's output
  (@{text socket_discharged_carried}).
\<close>

section \<open>The carrier's obligation\<close>

definition carrier_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> 'v resolution_view \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
      (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "carrier_discharged M d V cin cout \<longleftrightarrow> (\<forall>a x y x'. (d,a) \<in> M \<longrightarrow> resolution_view_term V a = Some (x,y) \<longrightarrow>
    cin x x' \<longrightarrow> (\<exists>b y'. (d,b) \<in> M \<and> resolution_view_term V b = Some (x',y') \<and> cout y y'))"

text \<open>
  A carrier discharged at two correspondences is discharged at a finer input correspondence and a coarser output
  one: an instance states its carrier at the correspondences its classes give.
\<close>

lemma carrier_discharged_mono:
  assumes "carrier_discharged M d V cin cout" "\<And>x x'. cin' x x' \<Longrightarrow> cin x x'"
    "\<And>y y'. cout y y' \<Longrightarrow> cout' y y'"
  shows "carrier_discharged M d V cin' cout'"
  using assms unfolding carrier_discharged_def by blast

lemma resolution_view_term_injective:
  assumes "view_formed V" "resolution_view_term V t = Some z" "resolution_view_term V t' = Some z"
  shows "t = t'"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  show ?thesis using resolution_view_injective[of p pi po t z t'] assms V by blast
qed

subsection \<open>A consumer is a carrier with no output\<close>

text \<open>
  The consumer's view carries the whole of its view's parts as input and gives the empty payload: two presentations
  of the output it holds, at one fixed part, correspond as inputs exactly where the second is the output of a term
  its view reads.
\<close>

definition consumer_carrier_view :: "'v resolution_view \<Rightarrow> 'v resolution_view" where
  "consumer_carrier_view V = (fst V,Finite_Pattern_Pair (fst (snd V)) (snd (snd V)),Finite_Pattern_Payload [])"

lemma consumer_carrier_view_term:
  "resolution_view_term (consumer_carrier_view V) t =
    map_option (\<lambda>z. (Pair_Term (fst z) (snd z),Payload_Term [])) (resolution_view_term V t)"
  by (cases V rule: prod_cases3) (simp add: consumer_carrier_view_def resolution_view_term_def split: option.split)

lemma consumer_carrier_view_formed: "view_formed (consumer_carrier_view V) \<longleftrightarrow> view_formed V"
  by (cases V rule: prod_cases3) (simp add: consumer_carrier_view_def view_formed_def)

definition consumer_input ::
    "'v resolution_view \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "consumer_input V corr x x' \<longleftrightarrow> (\<exists>u v v' b. x = Pair_Term u v \<and> x' = Pair_Term u v' \<and> corr v v' \<and>
    resolution_view_term V b = Some (u,v'))"

lemma carrier_consumer_step:
  assumes formed: "view_formed V"
    and carrier: "carrier_discharged M e (consumer_carrier_view V) (consumer_input V corr) (=)"
    and a: "resolution_view_term V a = Some (u,v)" and b: "resolution_view_term V b = Some (u,v')"
    and c: "corr v v'" and holds: "(e,a) \<in> M"
  shows "(e,b) \<in> M"
proof -
  have ca: "resolution_view_term (consumer_carrier_view V) a = Some (Pair_Term u v,Payload_Term [])"
    using a by (simp add: consumer_carrier_view_term)
  have ci: "consumer_input V corr (Pair_Term u v) (Pair_Term u v')"
    using b c by (auto simp: consumer_input_def)
  obtain b' y' where bM: "(e,b') \<in> M"
      and vb': "resolution_view_term (consumer_carrier_view V) b' = Some (Pair_Term u v',y')"
    using carrier holds ca ci unfolding carrier_discharged_def by blast
  have "resolution_view_term V b' = Some (u,v')" using vb' by (auto simp: consumer_carrier_view_term)
  then have "b' = b" using b by (rule resolution_view_term_injective[OF formed])
  then show ?thesis using bM by simp
qed

theorem consumer_discharged_carrier:
  assumes formed: "view_formed V" and sym: "symp corr"
  shows "consumer_discharged M e V corr \<longleftrightarrow>
    carrier_discharged M e (consumer_carrier_view V) (consumer_input V corr) (=)"
proof
  assume c: "consumer_discharged M e V corr"
  show "carrier_discharged M e (consumer_carrier_view V) (consumer_input V corr) (=)"
    unfolding carrier_discharged_def
  proof (intro allI impI)
    fix a x y x' assume holds: "(e,a) \<in> M" and va: "resolution_view_term (consumer_carrier_view V) a = Some (x,y)"
      and ci: "consumer_input V corr x x'"
    obtain u v where a: "resolution_view_term V a = Some (u,v)" and x: "x = Pair_Term u v"
        and y: "y = Payload_Term []"
      using va by (auto simp: consumer_carrier_view_term)
    obtain v' b where x': "x' = Pair_Term u v'" and cv: "corr v v'" and b: "resolution_view_term V b = Some (u,v')"
      using ci x by (auto simp: consumer_input_def)
    have "(e,b) \<in> M" using c a b cv holds unfolding consumer_discharged_def by blast
    moreover have "resolution_view_term (consumer_carrier_view V) b = Some (x',y)" using b x' y
      by (simp add: consumer_carrier_view_term)
    ultimately show "\<exists>b y'. (e,b) \<in> M \<and> resolution_view_term (consumer_carrier_view V) b = Some (x',y') \<and> y = y'"
      by blast
  qed
next
  assume car: "carrier_discharged M e (consumer_carrier_view V) (consumer_input V corr) (=)"
  show "consumer_discharged M e V corr" unfolding consumer_discharged_def
  proof (intro allI impI)
    fix a b u v v' assume a: "resolution_view_term V a = Some (u,v)" and b: "resolution_view_term V b = Some (u,v')"
      and cv: "corr v v'"
    have cv': "corr v' v" using sym cv by (rule sympD)
    show "(e,a) \<in> M \<longleftrightarrow> (e,b) \<in> M"
      using carrier_consumer_step[OF formed car a b cv] carrier_consumer_step[OF formed car b a cv'] by blast
  qed
qed

subsection \<open>Carriers from the notions' witnesses and contracts\<close>

text \<open>
  Along a function's direction, a presented function witness discharges a carrier at the class correspondences: its
  totality gives an output at every corresponding input, its soundness the image's presentation at both outputs. A
  witness relates an input to some presentations of its image, as an output following its input's order does at the
  bag class; a presented function contract, which relates it to every one, discharges the carrier through its witness
  (@{thm [source] presented_function_contract.witness}). Each needs the view to read every pair the operation relates.
\<close>

theorem function_witness_carrier:
  assumes witness: "presented_function_witness R D A S E B f operation"
    and reads: "\<And>t p q. resolution_view_term V t = Some (p,q) \<Longrightarrow> operation p q \<longleftrightarrow> (d,t) \<in> M"
    and realized: "\<And>p q. operation p q \<Longrightarrow> \<exists>t. resolution_view_term V t = Some (p,q)"
  shows "carrier_discharged M d V (presentation_transport R R) (presentation_transport S S)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  interpret w: presented_function_witness R D A S E B f operation by (rule witness)
  fix a x y x' assume holds: "(d,a) \<in> M" and va: "resolution_view_term V a = Some (x,y)"
    and t: "presentation_transport R R x x'"
  have o: "operation x y" using reads[OF va] holds by blast
  obtain c where c: "R c x" "R c x'" using t by (auto simp: presentation_transport_def)
  obtain y' where o': "operation x' y'" using w.total w.left.presentation_boundary[OF c(2)] by blast
  have "S (f c) y" "S (f c) y'" using w.sound[OF c(1) o] w.sound[OF c(2) o'] by blast+
  then have ty: "presentation_transport S S y y'" by (auto simp: presentation_transport_def)
  obtain b where vb: "resolution_view_term V b = Some (x',y')" using realized[OF o'] by blast
  have "(d,b) \<in> M" using reads[OF vb] o' by blast
  then show "\<exists>b y'. (d,b) \<in> M \<and> resolution_view_term V b = Some (x',y') \<and> presentation_transport S S y y'"
    using vb ty by blast
qed

theorem function_contract_carrier:
  assumes contract: "presented_function_contract R D A S E B f operation"
    and reads: "\<And>t p q. resolution_view_term V t = Some (p,q) \<Longrightarrow> operation p q \<longleftrightarrow> (d,t) \<in> M"
    and realized: "\<And>p q. operation p q \<Longrightarrow> \<exists>t. resolution_view_term V t = Some (p,q)"
  shows "carrier_discharged M d V (presentation_transport R R) (presentation_transport S S)"
  by (rule function_witness_carrier[OF presented_function_contract.witness[OF contract] reads realized])

text \<open>
  Against a witness's direction, a carrier from its image's presentation to its subject's is discharged along the
  input's presentation: the output changes with the input, which every presentation of the image reaches from some
  presentation of the same subject (@{text along}), as a key list is the keys of some reordering of every row list
  with the same keys. The witness's soundness identifies the image the input presents.
\<close>

theorem witness_along_carrier:
  assumes witness: "presented_function_witness R D A S E B f operation"
    and along: "\<And>a q p'. R a q \<Longrightarrow> S (f a) p' \<Longrightarrow> \<exists>q'. R a q' \<and> operation q' p'"
    and reads: "\<And>t p q. resolution_view_term V t = Some (p,q) \<Longrightarrow> operation q p \<longleftrightarrow> (d,t) \<in> M"
    and realized: "\<And>p q. operation q p \<Longrightarrow> \<exists>t. resolution_view_term V t = Some (p,q)"
  shows "carrier_discharged M d V (presentation_transport S S) (presentation_transport R R)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  interpret w: presented_function_witness R D A S E B f operation by (rule witness)
  fix a x y x' assume holds: "(d,a) \<in> M" and va: "resolution_view_term V a = Some (x,y)"
    and t: "presentation_transport S S x x'"
  have o: "operation y x" using reads[OF va] holds by blast
  obtain c where c: "S c x" "S c x'" using t by (auto simp: presentation_transport_def)
  obtain r where r: "R r y" using w.left.admitted[OF w.input_boundary[OF o]] by blast
  have "S (f r) x" by (rule w.sound[OF r o])
  then have fr: "c = f r" by (rule w.right.recovery[OF c(1)])
  obtain q' where q': "R r q'" "operation q' x'" using along[OF r] c(2) fr by blast
  obtain b where vb: "resolution_view_term V b = Some (x',q')" using realized[OF q'(2)] by blast
  have "(d,b) \<in> M" using reads[OF vb] q'(2) by blast
  moreover have "presentation_transport R R y q'" using r q'(1) by (auto simp: presentation_transport_def)
  ultimately show "\<exists>b y'. (d,b) \<in> M \<and> resolution_view_term V b = Some (x',y') \<and> presentation_transport R R y y'"
    using vb by blast
qed

text \<open>
  Against a relation contract's direction, its preimage discharges a carrier: the same output answers every input
  presenting the same subject. An output that changes with its input is a witness along it instead.
\<close>

theorem relation_contract_carrier_preimage:
  assumes contract: "presented_relation_contract R D A S E B L observe"
    and reads: "\<And>t p q. resolution_view_term V t = Some (q,p) \<Longrightarrow> observe p q \<longleftrightarrow> (d,t) \<in> M"
    and realized: "\<And>p q. observe p q \<Longrightarrow> \<exists>t. resolution_view_term V t = Some (q,p)"
  shows "carrier_discharged M d V (presentation_transport S S) (presentation_transport R R)"
  unfolding carrier_discharged_def
proof (intro allI impI)
  interpret presented_relation_contract R D A S E B L observe by (rule contract)
  fix a x y x' assume holds: "(d,a) \<in> M" and va: "resolution_view_term V a = Some (x,y)"
    and t: "presentation_transport S S x x'"
  have o: "observe y x" using reads[OF va] holds by blast
  obtain c where c: "S c x" "S c x'" using t by (auto simp: presentation_transport_def)
  obtain r where r: "R r y" using boundaries[OF o] left.admitted by blast
  have o': "observe y x'" using invariance[OF r c(1) r c(2)] o by blast
  obtain b where vb: "resolution_view_term V b = Some (x',y)" using realized[OF o'] by blast
  have "(d,b) \<in> M" using reads[OF vb] o' by blast
  moreover have "presentation_transport R R y y" using r by (auto simp: presentation_transport_def)
  ultimately show "\<exists>b y'. (d,b) \<in> M \<and> resolution_view_term V b = Some (x',y') \<and> presentation_transport R R y y'"
    using vb by blast
qed

section \<open>A socket discharged along its carriers\<close>

text \<open>
  A view read at a call pattern gives the parts of the pattern's value under every valuation, and the pattern's
  variables are its parts' variables.
\<close>

lemma resolution_view_pattern_evaluate:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_term V (evaluate_pattern g (decode_finite_pattern c)) =
    Some (evaluate_pattern g (decode_finite_pattern ci),evaluate_pattern g (decode_finite_pattern co))"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  have lin: "distinct (finite_pattern_occurrences p)" using formed V by (simp add: view_formed_def)
  obtain l where m: "view_pattern_match p c = Some l"
      and ci: "ci = finite_pattern_substitute (view_substitution l) pi"
      and co: "co = finite_pattern_substitute (view_substitution l) po"
    using viewed V by (auto simp: resolution_view_pattern_def split: option.splits)
  define h where "h = (\<lambda>v. evaluate_pattern g (decode_finite_pattern (view_substitution l v)))"
  have sub: "evaluate_pattern g (decode_finite_pattern (finite_pattern_substitute (view_substitution l) q)) =
      evaluate_pattern h (decode_finite_pattern q)" for q
    by (simp add: decode_finite_pattern_substitute h_def comp_def)
  have c: "c = finite_pattern_substitute (view_substitution l) p" using view_pattern_match_sound[OF lin m] by simp
  show ?thesis using resolution_view_evaluate[OF formed[unfolded V], of h] unfolding V c ci co sub .
qed

lemma resolution_view_pattern_variables:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "finite_pattern_variables c = finite_pattern_variables ci |\<union>| finite_pattern_variables co"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  have "finite_view_parts (resolution_view_term (p,pi,po)) c ci co"
    using resolution_view_pattern_parts formed viewed V by blast
  then show ?thesis by (simp add: finite_view_parts_def)
qed

lemma finite_evaluate_cong:
  assumes "\<And>v. v |\<in>| finite_pattern_variables q \<Longrightarrow> g v = g' v"
  shows "evaluate_pattern g (decode_finite_pattern q) = evaluate_pattern g' (decode_finite_pattern q)"
  by (rule evaluate_pattern_cong) (use assms in \<open>simp add: finite_pattern_variables_correct[symmetric]\<close>)

lemma finite_relation_option_unique:
  assumes selected: "finite_relation_option R k = Some a" and member: "(k,b) |\<in>| R"
  shows "b = a"
proof -
  have sel: "fimage snd (ffilter (\<lambda>r. fst r = k) R) = {|a|}"
    using selected by (simp add: finite_relation_option_def finite_singleton_option_some)
  have "b |\<in>| fimage snd (ffilter (\<lambda>r. fst r = k) R)"
    using fimageI[of "(k,b)" "ffilter (\<lambda>r. fst r = k) R" snd] member by simp
  then show ?thesis unfolding sel by simp
qed

lemma decoded_premise:
  "(k,d,p) |\<in>| finite_schema_premises S \<Longrightarrow> (k,d,decode_finite_pattern p) \<in> schema_premises (decode_finite_schema S)"
  by (force simp: decode_finite_call_pattern_def)

lemma decoded_premiseE:
  assumes "(q,e,pp) \<in> schema_premises (decode_finite_schema S)"
  obtains pf where "(q,e,pf) |\<in>| finite_schema_premises S" "pp = decode_finite_pattern pf"
  using assms by (auto simp: decode_finite_call_pattern_def)

subsection \<open>The parts a socket's clause carries\<close>

text \<open>
  The premise at a key of a clause, read at a view (@{text premise_parts}); the variables its output gives; the
  correspondence of two valuations at an output. A carrier of a clause is a key, a view and two correspondences
  (@{text clause_carrier}); the carried variables are the socket's output variables and those its carriers give.
\<close>

type_synonym 's clause_carrier =
  "'s \<times> nat resolution_view \<times> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<times> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool)"

definition premise_parts ::
    "('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> nat resolution_view \<Rightarrow>
      ('a finite_term_pattern \<times> 'a finite_term_pattern) option" where
  "premise_parts S k V = (case finite_relation_option (finite_schema_premises S) k of None \<Rightarrow> None
    | Some (d,p) \<Rightarrow> resolution_view_pattern V p)"

lemma premise_parts_at:
  "finite_relation_option (finite_schema_premises S) k = Some (d,p) \<Longrightarrow>
    premise_parts S k V = resolution_view_pattern V p"
  by (simp add: premise_parts_def)

definition output_variables :: "('a finite_term_pattern \<times> 'a finite_term_pattern) option \<Rightarrow> 'a set" where
  "output_variables z = (case z of None \<Rightarrow> {} | Some (i,out) \<Rightarrow> fset (finite_pattern_variables out))"

definition output_corresponds ::
    "(factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> ('a finite_term_pattern \<times> 'a finite_term_pattern) option \<Rightarrow>
      ('a \<Rightarrow> factor_term) \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> bool" where
  "output_corresponds R z g g' \<longleftrightarrow> (case z of None \<Rightarrow> False
    | Some (i,out) \<Rightarrow> R (evaluate_pattern g (decode_finite_pattern out)) (evaluate_pattern g' (decode_finite_pattern out)))"

lemma output_corresponds_cong:
  assumes corr: "output_corresponds R z g g1" and agree: "\<And>v. v \<in> output_variables z \<Longrightarrow> g1 v = g2 v"
  shows "output_corresponds R z g g2"
proof (cases z)
  case None
  then show ?thesis using corr by (simp add: output_corresponds_def)
next
  case (Some y)
  obtain i out where y: "y = (i,out)" by (cases y)
  have "evaluate_pattern g1 (decode_finite_pattern out) = evaluate_pattern g2 (decode_finite_pattern out)"
    using agree Some y by (intro finite_evaluate_cong) (simp add: output_variables_def)
  then show ?thesis using corr Some y by (simp add: output_corresponds_def)
qed

definition carried_variables ::
    "('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> nat resolution_view \<Rightarrow> 's clause_carrier list \<Rightarrow> 'a set" where
  "carried_variables S s Vp cs = output_variables (premise_parts S s Vp) \<union>
    (\<Union>c\<in>set cs. output_variables (premise_parts S (fst c) (fst (snd c))))"

definition carried_correspond ::
    "('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> nat resolution_view \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
      's clause_carrier list \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> bool" where
  "carried_correspond S s Vp c0 cs g g' \<longleftrightarrow> output_corresponds c0 (premise_parts S s Vp) g g' \<and>
    (\<forall>c\<in>set cs. output_corresponds (snd (snd (snd c))) (premise_parts S (fst c) (fst (snd c))) g g')"

lemma carried_variables_take_Suc:
  assumes "i < length cs"
  shows "carried_variables S s Vp (take (Suc i) cs) =
    carried_variables S s Vp (take i cs) \<union> output_variables (premise_parts S (fst (cs ! i)) (fst (snd (cs ! i))))"
  using assms by (auto simp: carried_variables_def take_Suc_conv_app_nth)

lemma carried_variables_take_mono: "carried_variables S s Vp (take i cs) \<subseteq> carried_variables S s Vp cs"
  unfolding carried_variables_def using set_take_subset[of i cs] by blast

lemma carried_variables_take_le:
  assumes "i \<le> j"
  shows "carried_variables S s Vp (take i cs) \<subseteq> carried_variables S s Vp (take j cs)"
proof -
  have "set (take i cs) \<subseteq> set (take j cs)" using assms by (rule set_take_subset_set_take)
  then show ?thesis unfolding carried_variables_def by blast
qed

lemma carried_correspond_take_Suc:
  assumes "i < length cs"
  shows "carried_correspond S s Vp c0 (take (Suc i) cs) g g' \<longleftrightarrow> carried_correspond S s Vp c0 (take i cs) g g' \<and>
    output_corresponds (snd (snd (snd (cs ! i)))) (premise_parts S (fst (cs ! i)) (fst (snd (cs ! i)))) g g'"
  using assms by (auto simp: carried_correspond_def take_Suc_conv_app_nth)

lemma carried_correspond_cong:
  assumes corr: "carried_correspond S s Vp c0 cs g g1"
    and agree: "\<And>v. v \<in> carried_variables S s Vp cs \<Longrightarrow> g1 v = g2 v"
  shows "carried_correspond S s Vp c0 cs g g2"
proof -
  have "output_corresponds c0 (premise_parts S s Vp) g g2"
    by (rule output_corresponds_cong[of c0 _ g g1]) (use corr agree in \<open>auto simp: carried_correspond_def carried_variables_def\<close>)
  moreover have "\<forall>c\<in>set cs. output_corresponds (snd (snd (snd c))) (premise_parts S (fst c) (fst (snd c))) g g2"
  proof
    fix c assume c: "c \<in> set cs"
    show "output_corresponds (snd (snd (snd c))) (premise_parts S (fst c) (fst (snd c))) g g2"
      by (rule output_corresponds_cong[of _ _ g g1]) (use corr agree c in \<open>auto simp: carried_correspond_def carried_variables_def\<close>)
  qed
  ultimately show ?thesis by (simp add: carried_correspond_def)
qed

text \<open>
  A socket's output is covered where every output its producer answers is a value of the output pattern: at an
  output that is a variable, always.
\<close>

definition output_covered :: "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> nat resolution_view \<Rightarrow> 'a finite_term_pattern \<Rightarrow> bool" where
  "output_covered M d V out \<longleftrightarrow> (\<forall>t u y. (d,t) \<in> M \<longrightarrow> resolution_view_term V t = Some (u,y) \<longrightarrow>
    (\<exists>g. evaluate_pattern g (decode_finite_pattern out) = y))"

lemma output_covered_variable: "output_covered M d V (Finite_Variable w)"
  unfolding output_covered_def by (auto intro: exI[of _ "\<lambda>_. _"])

text \<open>
  The i-th carrier of a socket's clause, in the carrying order: its key holds one premise its view reads, it is
  discharged and its output covered, its input holds carried variables only as given before it, its output variables
  are given by no carrier before it nor by the socket, and its input correspondence follows from the correspondence of
  every output given before it, the rest kept.
\<close>

definition carrier_step ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> nat resolution_view \<Rightarrow>
      (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> 's clause_carrier list \<Rightarrow> nat \<Rightarrow> bool" where
  "carrier_step M S s Vp c0 cs i \<longleftrightarrow> (case cs ! i of (k,V,cin,cout) \<Rightarrow> view_formed V \<and>
    (case finite_relation_option (finite_schema_premises S) k of None \<Rightarrow> False | Some (d,p) \<Rightarrow>
      (case resolution_view_pattern V p of None \<Rightarrow> False | Some (ip,op) \<Rightarrow>
        carrier_discharged M d V cin cout \<and> output_covered M d V op \<and>
        fset (finite_pattern_variables ip) \<inter> carried_variables S s Vp cs \<subseteq> carried_variables S s Vp (take i cs) \<and>
        fset (finite_pattern_variables op) \<inter> carried_variables S s Vp (take i cs) = {} \<and>
        (\<forall>g g'. (\<forall>v. v \<notin> carried_variables S s Vp cs \<longrightarrow> g v = g' v) \<longrightarrow>
          carried_correspond S s Vp c0 (take i cs) g g' \<longrightarrow>
          cin (evaluate_pattern g (decode_finite_pattern ip)) (evaluate_pattern g' (decode_finite_pattern ip))))))"

lemma carrier_step_at:
  assumes "carrier_step M S s Vp c0 cs i" "cs ! i = (k,V,cin,cout)"
  obtains d p ip op where "view_formed V" "finite_relation_option (finite_schema_premises S) k = Some (d,p)"
    "resolution_view_pattern V p = Some (ip,op)"
proof -
  obtain d p where at: "finite_relation_option (finite_schema_premises S) k = Some (d,p)"
    using assms unfolding carrier_step_def by (auto split: option.split_asm prod.split_asm)
  obtain ip op where vw: "resolution_view_pattern V p = Some (ip,op)"
    using assms at unfolding carrier_step_def by (auto split: option.split_asm prod.split_asm)
  have "view_formed V" using assms unfolding carrier_step_def by simp
  then show thesis using that at vw by blast
qed

lemma carrier_step_conditions:
  assumes "carrier_step M S s Vp c0 cs i" "cs ! i = (k,V,cin,cout)"
    "finite_relation_option (finite_schema_premises S) k = Some (d,p)" "resolution_view_pattern V p = Some (ip,op)"
  shows "carrier_discharged M d V cin cout" "output_covered M d V op"
    "fset (finite_pattern_variables ip) \<inter> carried_variables S s Vp cs \<subseteq> carried_variables S s Vp (take i cs)"
    "fset (finite_pattern_variables op) \<inter> carried_variables S s Vp (take i cs) = {}"
    "\<forall>g g'. (\<forall>v. v \<notin> carried_variables S s Vp cs \<longrightarrow> g v = g' v) \<longrightarrow>
      carried_correspond S s Vp c0 (take i cs) g g' \<longrightarrow>
      cin (evaluate_pattern g (decode_finite_pattern ip)) (evaluate_pattern g' (decode_finite_pattern ip))"
  using assms unfolding carrier_step_def by simp_all

lemma carrier_premise_variables:
  assumes step: "carrier_step M S s Vp c0 cs j" and j: "j < length cs"
    and at: "finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp)"
  shows "fset (finite_pattern_variables pp) \<inter> carried_variables S s Vp cs \<subseteq> carried_variables S s Vp (take (Suc j) cs)"
proof -
  obtain k V cin cout where cj: "cs ! j = (k,V,cin,cout)" by (rule prod_cases4[of "cs ! j"])
  obtain d p ip op where vV: "view_formed V" and atj: "finite_relation_option (finite_schema_premises S) k = Some (d,p)"
      and vw: "resolution_view_pattern V p = Some (ip,op)"
    by (rule carrier_step_at[OF step cj])
  have ipC: "fset (finite_pattern_variables ip) \<inter> carried_variables S s Vp cs \<subseteq> carried_variables S s Vp (take j cs)"
    by (rule carrier_step_conditions(3)[OF step cj atj vw])
  have pp: "pp = p" using at atj cj by simp
  have vs: "finite_pattern_variables p = finite_pattern_variables ip |\<union>| finite_pattern_variables op"
    by (rule resolution_view_pattern_variables[OF vV vw])
  have "carried_variables S s Vp (take (Suc j) cs) = carried_variables S s Vp (take j cs) \<union> fset (finite_pattern_variables op)"
  proof -
    have "carried_variables S s Vp (take (Suc j) cs) =
        carried_variables S s Vp (take j cs) \<union> output_variables (premise_parts S k V)"
      using carried_variables_take_Suc[OF j, of S s Vp] cj by simp
    then show ?thesis by (simp add: output_variables_def premise_parts_at[OF atj] vw)
  qed
  then show ?thesis using ipC vs pp by auto
qed

text \<open>
  The head holds carried variables only inside its output χ read at the head's view, and nowhere at a kept head.
\<close>

definition head_apart :: "bool \<Rightarrow> nat resolution_view \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a set \<Rightarrow> bool" where
  "head_apart keep Vh S C \<longleftrightarrow> (case resolution_view_pattern Vh (finite_schema_conclusion S) of
      Some (ci,co) \<Rightarrow> fset (finite_pattern_variables ci) \<inter> C = {} \<and> (keep \<longrightarrow> fset (finite_pattern_variables co) \<inter> C = {})
    | None \<Rightarrow> fset (finite_pattern_variables (finite_schema_conclusion S)) \<inter> C = {})"

text \<open>
  A socket carried by its clause's carriers (@{text socket_carried}): the meaning's answers are formed; the socket's
  key holds one premise its view reads, whose producer is discharged at the view's one hole with correspondence c0,
  whose output is covered and whose input holds no carried variable, and no material premise stands at the key; the
  carriers are in their carrying order; every other premise and every material premise holds no carried variable; the
  head holds them only inside χ.
\<close>

definition socket_carried ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> nat resolution_view \<Rightarrow>
      nat resolution_view \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> 's clause_carrier list \<Rightarrow> bool" where
  "socket_carried M S s keep Vp Vh c0 cs \<longleftrightarrow> (\<forall>e t. (e,t) \<in> M \<longrightarrow> term_formed t) \<and> view_formed Vp \<and>
    (case finite_relation_option (finite_schema_premises S) s of None \<Rightarrow> False | Some (d,p) \<Rightarrow>
      (case resolution_view_pattern Vp p of None \<Rightarrow> False | Some (xi,yo) \<Rightarrow>
        producer_discharged M d Vp [snd (snd Vp)] (\<lambda>_. c0) \<and> output_covered M d Vp yo \<and>
        fset (finite_pattern_variables xi) \<inter> carried_variables S s Vp cs = {})) \<and>
    (\<forall>N. (s,N) \<notin> schema_material_premises (decode_finite_schema S)) \<and>
    (\<forall>i<length cs. carrier_step M S s Vp c0 cs i) \<and>
    (\<forall>q e p. (q,e,p) \<in> schema_premises (decode_finite_schema S) \<longrightarrow> q \<noteq> s \<longrightarrow> q \<notin> fst ` set cs \<longrightarrow>
      pattern_variables p \<inter> carried_variables S s Vp cs = {}) \<and>
    (\<forall>q N. (q,N) \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow>
      material_variables N \<inter> carried_variables S s Vp cs = {}) \<and>
    head_apart keep Vh S (carried_variables S s Vp cs)"

lemma socket_carriedE:
  assumes "socket_carried M S s keep Vp Vh c0 cs"
  obtains d0 p0 xi yo where "finite_relation_option (finite_schema_premises S) s = Some (d0,p0)"
    "resolution_view_pattern Vp p0 = Some (xi,yo)" "producer_discharged M d0 Vp [snd (snd Vp)] (\<lambda>_. c0)"
    "output_covered M d0 Vp yo" "fset (finite_pattern_variables xi) \<inter> carried_variables S s Vp cs = {}"
  using assms unfolding socket_carried_def by (auto split: option.split_asm prod.split_asm)

text \<open>
  The carrying lemma. At a true instance h and a new answer of the socket at the same input, the new instance is
  rebuilt carrier by carrier along the order: the socket's output from the new answer, then each carrier's output from
  the answer its obligation gives at the input as rebuilt, the correspondence of every output given before it giving
  its input's correspondence. Every other variable keeps its value, so every other premise, every material premise
  and the head outside χ keep theirs.
\<close>

theorem socket_discharged_carried:
  assumes carried: "socket_carried M S s keep Vp Vh c0 cs"
  shows "socket_discharged M S s keep Vp Vh"
proof -
  define C where "C = carried_variables S s Vp cs"
  define Cn where "Cn n = carried_variables S s Vp (take n cs)" for n
  note sc = carried[unfolded socket_carried_def, folded C_def]
  have answers: "\<And>e t. (e,t) \<in> M \<Longrightarrow> term_formed t" using sc by blast
  have vp: "view_formed Vp" using sc by blast
  have nomat: "\<And>N. (s,N) \<notin> schema_material_premises (decode_finite_schema S)" using sc by blast
  have steps: "\<And>i. i < length cs \<Longrightarrow> carrier_step M S s Vp c0 cs i" using sc by blast
  have others: "\<And>q e p. (q,e,p) \<in> schema_premises (decode_finite_schema S) \<Longrightarrow> q \<noteq> s \<Longrightarrow> q \<notin> fst ` set cs \<Longrightarrow>
      pattern_variables p \<inter> C = {}" using sc by blast
  have mats: "\<And>q N. (q,N) \<in> schema_material_premises (decode_finite_schema S) \<Longrightarrow> material_variables N \<inter> C = {}"
    using sc by blast
  have head: "head_apart keep Vh S C" using sc by blast
  obtain d0 p0 xi yo where at0: "finite_relation_option (finite_schema_premises S) s = Some (d0,p0)"
      and vw0: "resolution_view_pattern Vp p0 = Some (xi,yo)"
      and prod0: "producer_discharged M d0 Vp [snd (snd Vp)] (\<lambda>_. c0)"
      and cov0: "output_covered M d0 Vp yo" and xi0: "fset (finite_pattern_variables xi) \<inter> C = {}"
    by (rule socket_carriedE[OF carried, folded C_def])
  have mem0: "(s,d0,p0) |\<in>| finite_schema_premises S" by (rule finite_relation_option_member[OF at0])
  have given0: "output_variables (premise_parts S s Vp) = fset (finite_pattern_variables yo)"
    by (simp add: output_variables_def premise_parts_at[OF at0] vw0)
  have yoC: "fset (finite_pattern_variables yo) \<subseteq> C" unfolding C_def carried_variables_def given0 by blast
  have given0_take: "fset (finite_pattern_variables yo) \<subseteq> Cn n" for n
    by (simp add: Cn_def carried_variables_def given0)
  have vars0: "finite_pattern_variables p0 = finite_pattern_variables xi |\<union>| finite_pattern_variables yo"
    by (rule resolution_view_pattern_variables[OF vp vw0])
  have ev0: "resolution_view_term Vp (evaluate_pattern g (decode_finite_pattern p0)) =
      Some (evaluate_pattern g (decode_finite_pattern xi),evaluate_pattern g (decode_finite_pattern yo))" for g
    by (rule resolution_view_pattern_evaluate[OF vp vw0])
  have CnC: "Cn n \<subseteq> C" for n unfolding Cn_def C_def by (rule carried_variables_take_mono)
  have first: "\<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None"
  proof (intro allI impI)
    fix d p assume "(s,d,p) |\<in>| finite_schema_premises S"
    then have "(d,p) = (d0,p0)" by (rule finite_relation_option_unique[OF at0])
    then show "resolution_view_pattern Vp p \<noteq> None" using vw0 by simp
  qed
  have core: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = y'"
    if ct: "clause_true M (decode_finite_schema S) h" and tM: "(d0,t) \<in> M"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')" for h t y'
  proof -
    have prem: "(e,evaluate_pattern h (decode_finite_pattern pp)) \<in> M"
      if "(q,e,pp) |\<in>| finite_schema_premises S" for q e pp
      using ct[unfolded clause_true_def] decoded_premise[OF that] by blast
    have hM0: "(d0,evaluate_pattern h (decode_finite_pattern p0)) \<in> M" by (rule prem[OF mem0])
    obtain g0 where g0: "evaluate_pattern g0 (decode_finite_pattern yo) = y'"
      using cov0[unfolded output_covered_def, rule_format, OF tM vt] by blast
    have c0y: "c0 (evaluate_pattern h (decode_finite_pattern yo)) y'"
      by (rule producer_discharged_single[THEN iffD1, OF prod0, rule_format, OF hM0 tM ev0 vt])
    have build: "\<exists>h'. (\<forall>v. v \<notin> Cn n \<longrightarrow> h' v = h v) \<and> evaluate_pattern h' (decode_finite_pattern p0) = t \<and>
        carried_correspond S s Vp c0 (take n cs) h h' \<and>
        (\<forall>j<n. \<forall>e pp. finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp) \<longrightarrow>
          (e,evaluate_pattern h' (decode_finite_pattern pp)) \<in> M)"
      if "n \<le> length cs" for n
      using that
    proof (induction n)
      case 0
      define h0 where "h0 = (\<lambda>v. if v |\<in>| finite_pattern_variables yo then g0 v else h v)"
      have off: "\<forall>v. v \<notin> Cn 0 \<longrightarrow> h0 v = h v" using given0_take[of 0] by (auto simp: h0_def)
      have "evaluate_pattern h0 (decode_finite_pattern yo) = evaluate_pattern g0 (decode_finite_pattern yo)"
        by (rule finite_evaluate_cong) (simp add: h0_def)
      then have eyo: "evaluate_pattern h0 (decode_finite_pattern yo) = y'" using g0 by simp
      have exi: "evaluate_pattern h0 (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
        by (rule finite_evaluate_cong) (use xi0 yoC in \<open>auto simp: h0_def\<close>)
      have "resolution_view_term Vp (evaluate_pattern h0 (decode_finite_pattern p0)) =
          Some (evaluate_pattern h (decode_finite_pattern xi),y')" using ev0[of h0] exi eyo by simp
      then have ep: "evaluate_pattern h0 (decode_finite_pattern p0) = t" by (rule resolution_view_term_injective[OF vp _ vt])
      have corr: "carried_correspond S s Vp c0 (take 0 cs) h h0"
        using c0y eyo by (simp add: carried_correspond_def output_corresponds_def premise_parts_at[OF at0] vw0)
      show ?case by (rule exI[of _ h0]) (use off ep corr in simp)
    next
      case (Suc n)
      then have n: "n < length cs" and le: "n \<le> length cs" by simp_all
      obtain h1 where off1: "\<forall>v. v \<notin> Cn n \<longrightarrow> h1 v = h v"
          and ep1: "evaluate_pattern h1 (decode_finite_pattern p0) = t"
          and corr1: "carried_correspond S s Vp c0 (take n cs) h h1"
          and prem1: "\<forall>j<n. \<forall>e pp. finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp) \<longrightarrow>
            (e,evaluate_pattern h1 (decode_finite_pattern pp)) \<in> M"
        using Suc.IH[OF le] by blast
      obtain k V cin cout where cn: "cs ! n = (k,V,cin,cout)" by (rule prod_cases4[of "cs ! n"])
      obtain d p ip op where vV: "view_formed V"
          and atn: "finite_relation_option (finite_schema_premises S) k = Some (d,p)"
          and vwn: "resolution_view_pattern V p = Some (ip,op)"
        by (rule carrier_step_at[OF steps[OF n] cn])
      note conds = carrier_step_conditions[OF steps[OF n] cn atn vwn, folded C_def]
      have car: "carrier_discharged M d V cin cout" and cov: "output_covered M d V op"
        using conds(1,2) .
      have ipC: "fset (finite_pattern_variables ip) \<inter> C \<subseteq> Cn n" using conds(3) unfolding Cn_def .
      have opC: "fset (finite_pattern_variables op) \<inter> Cn n = {}" using conds(4) unfolding Cn_def .
      have compat: "\<forall>g g'. (\<forall>v. v \<notin> C \<longrightarrow> g v = g' v) \<longrightarrow> carried_correspond S s Vp c0 (take n cs) g g' \<longrightarrow>
          cin (evaluate_pattern g (decode_finite_pattern ip)) (evaluate_pattern g' (decode_finite_pattern ip))"
        using conds(5) .
      have memn: "(k,d,p) |\<in>| finite_schema_premises S" by (rule finite_relation_option_member[OF atn])
      have givenn: "output_variables (premise_parts S k V) = fset (finite_pattern_variables op)"
        by (simp add: output_variables_def premise_parts_at[OF atn] vwn)
      have "cs ! n \<in> set cs" by (rule nth_mem[OF n])
      then have "output_variables (premise_parts S (fst (cs ! n)) (fst (snd (cs ! n)))) \<subseteq> C"
        unfolding C_def carried_variables_def by blast
      then have opCall: "fset (finite_pattern_variables op) \<subseteq> C" using cn givenn by simp
      have ipop: "fset (finite_pattern_variables ip) \<inter> fset (finite_pattern_variables op) = {}"
        using ipC opC opCall by blast
      have hM: "(d,evaluate_pattern h (decode_finite_pattern p)) \<in> M" by (rule prem[OF memn])
      have evn: "resolution_view_term V (evaluate_pattern g (decode_finite_pattern p)) =
          Some (evaluate_pattern g (decode_finite_pattern ip),evaluate_pattern g (decode_finite_pattern op))" for g
        by (rule resolution_view_pattern_evaluate[OF vV vwn])
      have ci: "cin (evaluate_pattern h (decode_finite_pattern ip)) (evaluate_pattern h1 (decode_finite_pattern ip))"
      proof -
        have agree: "\<And>v. v \<notin> C \<Longrightarrow> h v = h1 v" using off1 CnC[of n] by auto
        show ?thesis by (rule compat[rule_format, OF agree corr1])
      qed
      obtain b y2 where bM: "(d,b) \<in> M"
          and vb: "resolution_view_term V b = Some (evaluate_pattern h1 (decode_finite_pattern ip),y2)"
          and cy: "cout (evaluate_pattern h (decode_finite_pattern op)) y2"
        using car[unfolded carrier_discharged_def, rule_format, OF hM evn[of h] ci] by blast
      obtain g where g: "evaluate_pattern g (decode_finite_pattern op) = y2"
        using cov[unfolded output_covered_def, rule_format, OF bM vb] by blast
      define h2 where "h2 = (\<lambda>v. if v |\<in>| finite_pattern_variables op then g v else h1 v)"
      have "evaluate_pattern h2 (decode_finite_pattern op) = evaluate_pattern g (decode_finite_pattern op)"
        by (rule finite_evaluate_cong) (simp add: h2_def)
      then have h2op: "evaluate_pattern h2 (decode_finite_pattern op) = y2" using g by simp
      have h2ip: "evaluate_pattern h2 (decode_finite_pattern ip) = evaluate_pattern h1 (decode_finite_pattern ip)"
        by (rule finite_evaluate_cong) (use ipop in \<open>auto simp: h2_def\<close>)
      have "resolution_view_term V (evaluate_pattern h2 (decode_finite_pattern p)) =
          Some (evaluate_pattern h1 (decode_finite_pattern ip),y2)" using evn[of h2] h2ip h2op by simp
      then have h2p: "evaluate_pattern h2 (decode_finite_pattern p) = b"
        by (rule resolution_view_term_injective[OF vV _ vb])
      have Cn_Suc: "Cn (Suc n) = Cn n \<union> fset (finite_pattern_variables op)"
      proof -
        have "carried_variables S s Vp (take (Suc n) cs) =
            carried_variables S s Vp (take n cs) \<union> output_variables (premise_parts S k V)"
          using carried_variables_take_Suc[OF n, of S s Vp] cn by simp
        then show ?thesis using givenn by (simp add: Cn_def)
      qed
      have off2: "\<forall>v. v \<notin> Cn (Suc n) \<longrightarrow> h2 v = h v" using off1 Cn_Suc by (auto simp: h2_def)
      have "evaluate_pattern h2 (decode_finite_pattern p0) = evaluate_pattern h1 (decode_finite_pattern p0)"
      proof (rule finite_evaluate_cong)
        fix v assume v: "v |\<in>| finite_pattern_variables p0"
        have "v |\<notin>| finite_pattern_variables op"
        proof
          assume vo: "v |\<in>| finite_pattern_variables op"
          have "v |\<in>| finite_pattern_variables xi \<or> v |\<in>| finite_pattern_variables yo" using v vars0 by simp
          then show False using vo xi0 opCall opC given0_take[of n] by blast
        qed
        then show "h2 v = h1 v" by (simp add: h2_def)
      qed
      then have ep2: "evaluate_pattern h2 (decode_finite_pattern p0) = t" using ep1 by simp
      have "carried_correspond S s Vp c0 (take n cs) h h2"
        by (rule carried_correspond_cong[OF corr1]) (use opC in \<open>auto simp: h2_def Cn_def\<close>)
      then have corr2: "carried_correspond S s Vp c0 (take (Suc n) cs) h h2"
        using cy h2op carried_correspond_take_Suc[OF n, of S s Vp c0 h h2] cn premise_parts_at[OF atn, of V] vwn
        by (simp add: output_corresponds_def)
      have prem2: "\<forall>j<Suc n. \<forall>e pp. finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp) \<longrightarrow>
          (e,evaluate_pattern h2 (decode_finite_pattern pp)) \<in> M"
      proof (intro allI impI)
        fix j e pp assume j: "j < Suc n"
          and atj: "finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp)"
        show "(e,evaluate_pattern h2 (decode_finite_pattern pp)) \<in> M"
        proof (cases "j = n")
          case True
          then have "(e,pp) = (d,p)" using atj atn cn by simp
          then show ?thesis using h2p bM by simp
        next
          case False
          then have jn: "j < n" using j by simp
          have jl: "j < length cs" using jn n by simp
          have vj: "fset (finite_pattern_variables pp) \<inter> C \<subseteq> Cn (Suc j)"
            using carrier_premise_variables[OF steps[OF jl] jl atj] unfolding C_def Cn_def .
          have "Cn (Suc j) \<subseteq> Cn n" using jn unfolding Cn_def by (intro carried_variables_take_le) simp
          then have "evaluate_pattern h2 (decode_finite_pattern pp) = evaluate_pattern h1 (decode_finite_pattern pp)"
            using vj opC opCall by (intro finite_evaluate_cong) (auto simp: h2_def)
          then show ?thesis using prem1 jn atj by simp
        qed
      qed
      show ?case using off2 ep2 corr2 prem2 by blast
    qed
    obtain h' where off: "\<forall>v. v \<notin> Cn (length cs) \<longrightarrow> h' v = h v"
        and ep: "evaluate_pattern h' (decode_finite_pattern p0) = t"
        and premc: "\<forall>j<length cs. \<forall>e pp. finite_relation_option (finite_schema_premises S) (fst (cs ! j)) = Some (e,pp) \<longrightarrow>
          (e,evaluate_pattern h' (decode_finite_pattern pp)) \<in> M"
      using build[of "length cs"] by blast
    have offC: "h' v = h v" if "v \<notin> C" for v using off that by (simp add: Cn_def C_def)
    have exi: "evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
      by (rule finite_evaluate_cong) (use xi0 offC in blast)
    have "Some (evaluate_pattern h (decode_finite_pattern xi),y') =
        Some (evaluate_pattern h' (decode_finite_pattern xi),evaluate_pattern h' (decode_finite_pattern yo))"
      using ev0[of h'] ep vt by simp
    then have eyo: "evaluate_pattern h' (decode_finite_pattern yo) = y'" by simp
    have ct': "clause_true M (decode_finite_schema S) h'"
      unfolding clause_true_def
    proof (intro conjI ballI allI impI)
      fix a assume a: "a \<in> schema_variables (decode_finite_schema S)"
      show "term_formed (h' a)"
      proof (cases "a \<in> C")
        case False
        then show ?thesis using offC ct a unfolding clause_true_def by auto
      next
        case True
        then consider "a |\<in>| finite_pattern_variables yo"
          | c where "c \<in> set cs" "a \<in> output_variables (premise_parts S (fst c) (fst (snd c)))"
          unfolding C_def carried_variables_def given0 by blast
        then show ?thesis
        proof cases
          case 1
          then have "a \<in> pattern_variables (decode_finite_pattern p0)"
            using vars0 by (simp add: finite_pattern_variables_correct[symmetric])
          moreover have "term_formed (evaluate_pattern h' (decode_finite_pattern p0))" using answers[OF tM] ep by simp
          ultimately show ?thesis using evaluate_pattern_variables_formed[of h' "decode_finite_pattern p0" a] by blast
        next
          case 2
          then obtain j where j: "j < length cs" and c: "c = cs ! j" by (auto simp: in_set_conv_nth)
          obtain k V cin cout where cj: "cs ! j = (k,V,cin,cout)" by (rule prod_cases4[of "cs ! j"])
          obtain e pp ip op where vVj: "view_formed V"
              and atj: "finite_relation_option (finite_schema_premises S) k = Some (e,pp)"
              and vwj: "resolution_view_pattern V pp = Some (ip,op)"
            by (rule carrier_step_at[OF steps[OF j] cj])
          have "a |\<in>| finite_pattern_variables op" using 2 c cj
            by (simp add: output_variables_def premise_parts_at[OF atj] vwj)
          then have "a \<in> pattern_variables (decode_finite_pattern pp)"
            using resolution_view_pattern_variables[OF vVj vwj] by (simp add: finite_pattern_variables_correct[symmetric])
          moreover have "(e,evaluate_pattern h' (decode_finite_pattern pp)) \<in> M" using premc j atj cj by simp
          then have "term_formed (evaluate_pattern h' (decode_finite_pattern pp))" by (rule answers)
          ultimately show ?thesis using evaluate_pattern_variables_formed[of h' "decode_finite_pattern pp" a] by blast
        qed
      qed
    next
      fix q e pp assume qp: "(q,e,pp) \<in> schema_premises (decode_finite_schema S)"
      obtain pf where memf: "(q,e,pf) |\<in>| finite_schema_premises S" and pp: "pp = decode_finite_pattern pf"
        using decoded_premiseE[OF qp] by blast
      show "(e,evaluate_pattern h' pp) \<in> M"
      proof (cases "q = s")
        case True
        then have "(e,pf) = (d0,p0)" using finite_relation_option_unique[OF at0] memf by simp
        then show ?thesis using ep tM pp by simp
      next
        case qs: False
        show ?thesis
        proof (cases "q \<in> fst ` set cs")
          case True
          then obtain j where j: "j < length cs" and qj: "q = fst (cs ! j)" by (auto simp: in_set_conv_nth)
          obtain k V cin cout where cj: "cs ! j = (k,V,cin,cout)" by (rule prod_cases4[of "cs ! j"])
          obtain dj pj ipj opj where "view_formed V"
              and atj: "finite_relation_option (finite_schema_premises S) k = Some (dj,pj)"
              and "resolution_view_pattern V pj = Some (ipj,opj)"
            by (rule carrier_step_at[OF steps[OF j] cj])
          have "(e,pf) = (dj,pj)" using finite_relation_option_unique[OF atj] memf qj cj by simp
          then show ?thesis using premc j atj cj pp by auto
        next
          case False
          have "pattern_variables pp \<inter> C = {}" by (rule others[OF qp qs False])
          then have "evaluate_pattern h' pp = evaluate_pattern h pp"
            by (intro evaluate_pattern_cong) (use offC in blast)
          then show ?thesis using ct qp unfolding clause_true_def by auto
        qed
      qed
    next
      fix q N assume qN: "(q,N) \<in> schema_material_premises (decode_finite_schema S)"
      have "material_variables N \<inter> C = {}" by (rule mats[OF qN])
      then have "evaluate_material_satisfaction h' N \<longleftrightarrow> evaluate_material_satisfaction h N"
        by (intro evaluate_material_satisfaction_cong) (use offC in blast)
      then show "evaluate_material_satisfaction h' N" using ct qN unfolding clause_true_def by auto
    qed
    have hk: "head_kept keep Vh S h h'"
    proof (cases "resolution_view_pattern Vh (finite_schema_conclusion S)")
      case None
      then have "fset (finite_pattern_variables (finite_schema_conclusion S)) \<inter> C = {}"
        using head by (simp add: head_apart_def)
      then have "evaluate_pattern h' (decode_finite_pattern (finite_schema_conclusion S)) =
          evaluate_pattern h (decode_finite_pattern (finite_schema_conclusion S))"
        by (intro finite_evaluate_cong) (use offC in blast)
      then show ?thesis using None by (simp add: head_kept_def)
    next
      case (Some z)
      obtain ci co where z: "z = (ci,co)" by (cases z)
      have hd: "fset (finite_pattern_variables ci) \<inter> C = {}" "keep \<longrightarrow> fset (finite_pattern_variables co) \<inter> C = {}"
        using head Some z by (simp_all add: head_apart_def)
      have "evaluate_pattern h' (decode_finite_pattern ci) = evaluate_pattern h (decode_finite_pattern ci)"
        using hd(1) by (intro finite_evaluate_cong) (use offC in blast)
      moreover have "keep \<longrightarrow> evaluate_pattern h' (decode_finite_pattern co) = evaluate_pattern h (decode_finite_pattern co)"
      proof
        assume keep
        then have "fset (finite_pattern_variables co) \<inter> C = {}" using hd(2) by blast
        then show "evaluate_pattern h' (decode_finite_pattern co) = evaluate_pattern h (decode_finite_pattern co)"
          by (intro finite_evaluate_cong) (use offC in blast)
      qed
      ultimately show ?thesis using Some z by (simp add: head_kept_def)
    qed
    show ?thesis using ct' hk exi eyo by blast
  qed
  have calls: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi') = evaluate_pattern h (decode_finite_pattern xi') \<and>
      evaluate_pattern h' (decode_finite_pattern yo') = y'"
    if ct: "clause_true M (decode_finite_schema S) h" and memp: "(s,d,p) |\<in>| finite_schema_premises S"
      and vwp: "resolution_view_pattern Vp p = Some (xi',yo')" and tM: "(d,t) \<in> M"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi'),y')"
    for h d p xi' yo' t y'
  proof -
    have "(d,p) = (d0,p0)" by (rule finite_relation_option_unique[OF at0 memp])
    then have d: "d = d0" and p: "p = p0" by simp_all
    then have x: "xi' = xi" and y: "yo' = yo" using vwp vw0 by simp_all
    show ?thesis using core[OF ct, of t y'] tM vt d x y by simp
  qed
  show ?thesis unfolding socket_discharged_def using first calls nomat by blast
qed

end
