theory Factor_Finite_Data_Syntax
  imports Factor_Finite_Artifact_Enumeration Factor_Executable_Data_Values Factor_Complete_Data_Quotation
    RRA_Finite_Syntax_Construction Natural_Binary_Digits
begin

section \<open>A node counter in binary digits addresses the data syntax\<close>

text \<open>
  A complete data quotation admits every injective formed readdressing of the data syntax. The
  syntax itself addresses the children of a pair by prefixing their addresses, so in a data list
  the addresses of the k-th element have length about k and the total size of the quotation grows
  with the square of the list. The executable quotation numbers the nodes of the same syntax by a
  counter in construction order and writes each number in binary digits: the root keeps the
  empty address, every other node receives a distinct short address, and the result is the syntax
  readdressed, so every existing contract of complete data quotations applies to it unchanged.
\<close>

definition compact_syntax_address :: "nat \<Rightarrow> local_address" where
  "compact_syntax_address n=map of_bool (natural_binary_digits n)"

lemma compact_syntax_address_injective: "inj compact_syntax_address"
proof (rule injI)
  fix m n assume same: "compact_syntax_address m=compact_syntax_address n"
  have digit: "inj (of_bool :: bool \<Rightarrow> nat)" by (rule injI) (simp only: of_bool_eq_iff)
  have "natural_binary_digits m=natural_binary_digits n"
    using same by (simp only: compact_syntax_address_def inj_map_eq_map[OF digit])
  then show "m=n" by (simp only: natural_binary_digits_injective)
qed

lemma compact_syntax_address_eq [simp]: "compact_syntax_address m=compact_syntax_address n \<longleftrightarrow> m=n"
  using compact_syntax_address_injective by (auto dest: injD)

lemma compact_syntax_address_formed [simp]: "octets_formed (compact_syntax_address n)"
  by (auto simp: compact_syntax_address_def octets_formed_def of_bool_def)

lemma compact_syntax_address_root [simp]: "compact_syntax_address 0=[]"
  by (simp add: compact_syntax_address_def)

fun data_syntax_size :: "factor_term \<Rightarrow> nat" where
  "data_syntax_size (Target_Term t)=1"
| "data_syntax_size (Payload_Term v)=1"
| "data_syntax_size (Pair_Term x y)=3+data_syntax_size x+data_syntax_size y"

fun data_syntax_position :: "nat \<Rightarrow> factor_term \<Rightarrow> local_address \<Rightarrow> nat" where
  "data_syntax_position n (Pair_Term x y) (i#a)=
    (if i=2 then data_syntax_position (n+3) x a
     else if i=3 then data_syntax_position (n+3+data_syntax_size x) y a
     else if i=0 \<and> a=[] then Suc n else if i=1 \<and> a=[] then Suc (Suc n) else n)"
| "data_syntax_position n t a=n"

lemma data_syntax_position_root [simp]: "data_syntax_position n t []=n"
  by (cases t) simp_all

lemma data_syntax_position_pair [simp]:
  "data_syntax_position n (Pair_Term x y) [0]=Suc n"
  "data_syntax_position n (Pair_Term x y) [1]=Suc (Suc n)"
  "data_syntax_position n (Pair_Term x y) (2#a)=data_syntax_position (n+3) x a"
  "data_syntax_position n (Pair_Term x y) (3#a)=data_syntax_position (n+3+data_syntax_size x) y a"
  by simp_all

definition data_syntax_address :: "nat \<Rightarrow> factor_term \<Rightarrow> local_address \<Rightarrow> local_address" where
  "data_syntax_address n t a=compact_syntax_address (data_syntax_position n t a)"

lemma data_syntax_address_root [simp]: "data_syntax_address n t []=compact_syntax_address n"
  by (simp add: data_syntax_address_def)

section \<open>The positions number the carrier of the data syntax exactly\<close>

lemma data_syntax_carrier:
  assumes "self_contained_term t"
  shows "finite (rra_carrier (object_structure (term_syntax t))) \<and>
    card (rra_carrier (object_structure (term_syntax t)))=data_syntax_size t \<and>
    data_syntax_position n t ` rra_carrier (object_structure (term_syntax t))={n..<n+data_syntax_size t}"
  using assms
proof (induction t arbitrary: n)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  show ?case by (simp add: payload_syntax_def)
next
  case (Pair_Term x y)
  let ?X="rra_carrier (object_structure (term_syntax x))"
  let ?Y="rra_carrier (object_structure (term_syntax y))"
  let ?m="n+3+data_syntax_size x"
  have closed: "self_contained_term x" "self_contained_term y" using Pair_Term.prems by simp_all
  have left: "finite ?X" "card ?X=data_syntax_size x"
      "data_syntax_position (n+3) x ` ?X={n+3..<n+3+data_syntax_size x}"
    using Pair_Term.IH(1)[OF closed(1), of "n+3"] by simp_all
  have right: "finite ?Y" "card ?Y=data_syntax_size y"
      "data_syntax_position ?m y ` ?Y={?m..<?m+data_syntax_size y}"
    using Pair_Term.IH(2)[OF closed(2), of ?m] by simp_all
  have carrier: "rra_carrier (object_structure (term_syntax (Pair_Term x y)))=
      {[],[0],[1]} \<union> Cons 2 ` ?X \<union> Cons 3 ` ?Y"
    by (simp add: pair_syntax_def)
  have finite_ports: "finite ({[],[0],[1]} \<union> Cons 2 ` ?X)" using left(1) by simp
  have disjoint_left: "{[],[0],[1]} \<inter> Cons 2 ` ?X={}" by auto
  have disjoint_right: "({[],[0],[1]} \<union> Cons 2 ` ?X) \<inter> Cons 3 ` ?Y={}" by auto
  have card_ports: "card ({[],[0],[1]::local_address})=3" by simp
  have card_left: "card (Cons 2 ` ?X)=card ?X" by (rule card_image) (simp add: inj_on_def)
  have card_right: "card (Cons 3 ` ?Y)=card ?Y" by (rule card_image) (simp add: inj_on_def)
  have card_inner: "card ({[],[0],[1]} \<union> Cons 2 ` ?X)=3+data_syntax_size x"
    using card_Un_disjoint[of "{[],[0],[1]}" "Cons 2 ` ?X"] left(1) disjoint_left card_ports card_left left(2)
    by simp
  have card: "card ({[],[0],[1]} \<union> Cons 2 ` ?X \<union> Cons 3 ` ?Y)=3+data_syntax_size x+data_syntax_size y"
    using card_Un_disjoint[of "{[],[0],[1]} \<union> Cons 2 ` ?X" "Cons 3 ` ?Y"] finite_ports right(1)
      disjoint_right card_inner card_right right(2)
    by simp
  have image: "data_syntax_position n (Pair_Term x y) ` ({[],[0],[1]} \<union> Cons 2 ` ?X \<union> Cons 3 ` ?Y)=
      {n,Suc n,Suc (Suc n)} \<union> data_syntax_position (n+3) x ` ?X \<union> data_syntax_position ?m y ` ?Y"
    by (simp add: image_Un image_image)
  have interval: "{n,Suc n,Suc (Suc n)} \<union> {n+3..<n+3+data_syntax_size x} \<union> {?m..<?m+data_syntax_size y}=
      {n..<n+(3+data_syntax_size x+data_syntax_size y)}"
    by (rule set_eqI) (simp add: atLeastLessThan_iff; arith)
  have finite_all: "finite ({[],[0],[1]} \<union> Cons 2 ` ?X \<union> Cons 3 ` ?Y)" using finite_ports right(1) by simp
  show ?case
    unfolding carrier data_syntax_size.simps
    using finite_all card image left(3) right(3) interval by simp
qed

lemma data_syntax_address_injective:
  assumes "self_contained_term t"
  shows "inj_on (data_syntax_address n t) (rra_carrier (object_structure (term_syntax t)))"
proof -
  have facts: "finite (rra_carrier (object_structure (term_syntax t)))"
      "card (rra_carrier (object_structure (term_syntax t)))=data_syntax_size t"
      "data_syntax_position n t ` rra_carrier (object_structure (term_syntax t))={n..<n+data_syntax_size t}"
    using data_syntax_carrier[OF assms, of n] by simp_all
  have positions: "inj_on (data_syntax_position n t) (rra_carrier (object_structure (term_syntax t)))"
    using facts by (simp only: inj_on_iff_eq_card[OF facts(1)]) simp
  have composed: "data_syntax_address n t=compact_syntax_address \<circ> data_syntax_position n t"
    by (simp add: fun_eq_iff data_syntax_address_def)
  show ?thesis
    unfolding composed
    by (rule comp_inj_on[OF positions]) (rule inj_on_subset[OF compact_syntax_address_injective], simp)
qed

section \<open>The compact construction is the data syntax readdressed\<close>

definition finite_compact_payload :: "nat \<Rightarrow> octets \<Rightarrow> finite_exact_artifact" where
  "finite_compact_payload n v=\<lparr>finite_structure=\<lparr>finite_carrier={|compact_syntax_address n|},finite_incidence={||}\<rparr>,
    finite_data=finite_payload_basis (compact_syntax_address n) v\<rparr>"

definition finite_compact_pair :: "nat \<Rightarrow> nat \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_compact_pair n m R S=finite_syntax_join id id
    {|compact_syntax_address n,compact_syntax_address (Suc n),compact_syntax_address (Suc (Suc n))|}
    {|(compact_syntax_address n,compact_syntax_address (Suc n),compact_syntax_address (n+3)),
      (compact_syntax_address n,compact_syntax_address (Suc (Suc n)),compact_syntax_address m),
      (compact_syntax_address (Suc n),compact_syntax_address (Suc n),compact_syntax_address (Suc (Suc n)))|} R S"

fun finite_data_syntax_at :: "nat \<Rightarrow> factor_term \<Rightarrow> (nat\<times>finite_exact_artifact) option" where
  "finite_data_syntax_at n (Target_Term t)=None"
| "finite_data_syntax_at n (Payload_Term v)=Some (Suc n,finite_compact_payload n v)"
| "finite_data_syntax_at n (Pair_Term x y)=(case finite_data_syntax_at (n+3) x of None \<Rightarrow> None
    | Some (m,R) \<Rightarrow> (case finite_data_syntax_at m y of None \<Rightarrow> None
      | Some (k,S) \<Rightarrow> Some (k,finite_compact_pair n m R S)))"

lemma finite_data_syntax_at_domain:
  "finite_data_syntax_at n t=None \<longleftrightarrow> \<not>self_contained_term t"
proof (induction t arbitrary: n)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  then show ?case by simp
next
  case (Pair_Term x y)
  show ?case
  proof (cases "finite_data_syntax_at (n+3) x")
    case None
    then show ?thesis using Pair_Term.IH(1)[of "n+3"] by simp
  next
    case (Some p)
    obtain m R where p: "p=(m,R)" by (cases p)
    have built: "finite_data_syntax_at (n+3) x=Some (m,R)" using Some p by simp
    have left: "self_contained_term x" using Pair_Term.IH(1)[of "n+3"] built by simp
    show ?thesis
    proof (cases "finite_data_syntax_at m y")
      case None
      then show ?thesis using Pair_Term.IH(2)[of m] built left by simp
    next
      case (Some q)
      obtain l S where q: "q=(l,S)" by (cases q)
      show ?thesis using Pair_Term.IH(2)[of m] built left Some q by simp
    qed
  qed
qed

lemma finite_data_syntax_at_counter:
  "finite_data_syntax_at n t=Some (k,C) \<Longrightarrow> k=n+data_syntax_size t"
proof (induction t arbitrary: n k C)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  then show ?case by simp
next
  case (Pair_Term x y)
  obtain m R l S where left: "finite_data_syntax_at (n+3) x=Some (m,R)"
    and right: "finite_data_syntax_at m y=Some (l,S)" and k: "k=l"
    using Pair_Term.prems by (auto split: option.splits)
  show ?case using Pair_Term.IH(1)[OF left] Pair_Term.IH(2)[OF right] k by simp
qed

lemma pushed_count_zero: "pushed_count U f (\<lambda>_. 0)=(\<lambda>_. 0)"
  by (simp add: pushed_count_def fun_eq_iff split_def)

lemma finite_data_syntax_at_sound:
  "finite_data_syntax_at n t=Some (k,C) \<Longrightarrow>
    decode_finite_object C=push_object (data_syntax_address n t) (term_syntax t)"
proof (induction t arbitrary: n k C)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term v)
  then have built: "C=finite_compact_payload n v" by simp
  show ?case
    by (simp add: built finite_compact_payload_def finite_payload_basis_def payload_syntax_def push_object_def
        push_structure_def push_basis_def pushed_count_zero decode_finite_object_def decode_finite_structure_def
        decode_finite_basis_def data_syntax_address_def zero_multiset.rep_eq)
next
  case (Pair_Term x y)
  obtain m R l S where left: "finite_data_syntax_at (n+3) x=Some (m,R)"
    and right: "finite_data_syntax_at m y=Some (l,S)" and built: "C=finite_compact_pair n m R S"
    using Pair_Term.prems by (auto split: option.splits)
  have m: "m=n+3+data_syntax_size x" by (rule finite_data_syntax_at_counter[OF left])
  have R: "decode_finite_object R=push_object (data_syntax_address (n+3) x) (term_syntax x)"
    by (rule Pair_Term.IH(1)[OF left])
  have S: "decode_finite_object S=push_object (data_syntax_address m y) (term_syntax y)"
    by (rule Pair_Term.IH(2)[OF right])
  have left_address: "data_syntax_address n (Pair_Term x y) (2#a)=data_syntax_address (n+3) x a" for a
    by (simp add: data_syntax_address_def)
  have right_address: "data_syntax_address n (Pair_Term x y) (3#a)=data_syntax_address m y a" for a
    by (simp add: data_syntax_address_def m)
  have ports: "data_syntax_address n (Pair_Term x y) []=compact_syntax_address n"
      "data_syntax_address n (Pair_Term x y) [0]=compact_syntax_address (Suc n)"
      "data_syntax_address n (Pair_Term x y) [1]=compact_syntax_address (Suc (Suc n))"
      "data_syntax_address n (Pair_Term x y) [Suc 0]=compact_syntax_address (Suc (Suc n))"
      "data_syntax_address n (Pair_Term x y) [2]=compact_syntax_address (n+3)"
      "data_syntax_address n (Pair_Term x y) [3]=compact_syntax_address m"
    by (simp_all add: data_syntax_address_def m)
  show ?case
    by (simp add: built finite_compact_pair_def decode_finite_syntax_join R S push_object_def push_structure_def
        push_basis_def pushed_count_zero pair_syntax_def image_Un image_image image_insert case_prod_unfold
        left_address right_address ports insert_commute)
qed

section \<open>The executable complete data quotation\<close>

definition finite_data_syntax :: "factor_term \<Rightarrow> finite_exact_artifact option" where
  "finite_data_syntax t=map_option snd (finite_data_syntax_at 0 t)"

theorem finite_data_syntax_domain:
  "finite_data_syntax t=None \<longleftrightarrow> \<not>self_contained_term t"
  by (simp add: finite_data_syntax_def finite_data_syntax_at_domain)

lemma finite_data_syntax_closed:
  assumes built: "finite_data_syntax t=Some C"
  shows "self_contained_term t"
proof (rule ccontr)
  assume "\<not>self_contained_term t"
  then have "finite_data_syntax t=None" by (simp add: finite_data_syntax_domain)
  then show False using built by simp
qed

theorem finite_data_syntax_sound:
  assumes "finite_data_syntax t=Some C"
  shows "decode_finite_object C=push_object (data_syntax_address 0 t) (term_syntax t)"
proof -
  obtain k where "finite_data_syntax_at 0 t=Some (k,C)"
    using assms by (auto simp: finite_data_syntax_def)
  then show ?thesis by (rule finite_data_syntax_at_sound)
qed

theorem finite_data_syntax_exact:
  "finite_data_syntax t=Some C \<longleftrightarrow>
    self_contained_term t \<and> decode_finite_object C=push_object (data_syntax_address 0 t) (term_syntax t)"
proof
  assume built: "finite_data_syntax t=Some C"
  have "self_contained_term t" by (rule finite_data_syntax_closed[OF built])
  then show "self_contained_term t \<and> decode_finite_object C=push_object (data_syntax_address 0 t) (term_syntax t)"
    using finite_data_syntax_sound[OF built] by simp
next
  assume parts: "self_contained_term t \<and> decode_finite_object C=push_object (data_syntax_address 0 t) (term_syntax t)"
  have available: "finite_data_syntax t\<noteq>None"
    using parts finite_data_syntax_domain[of t] by simp
  then obtain B where built: "finite_data_syntax t=Some B" by blast
  have "decode_finite_object B=decode_finite_object C"
    using finite_data_syntax_sound[OF built] parts by simp
  then show "finite_data_syntax t=Some C" using built by simp
qed

theorem finite_data_syntax_complete_quotation:
  assumes formed: "term_formed t" and built: "finite_data_syntax t=Some C"
  shows "complete_data_quoted_at (decode_finite_object C) [] t"
proof -
  have closed: "self_contained_term t" by (rule finite_data_syntax_closed[OF built])
  have addressing: "finite_addressing (rra_carrier (object_structure (term_syntax t))) (data_syntax_address 0 t)"
    unfolding finite_addressing_def
    using data_syntax_address_injective[OF closed, of 0] by (simp add: data_syntax_address_def)
  have root: "data_syntax_address 0 t []=[]" by (simp add: data_syntax_address_def)
  show ?thesis
    unfolding complete_data_quoted_at_def
    using formed closed addressing finite_data_syntax_sound[OF built] root by metis
qed

text \<open>
  The constructors build the payload and pair syntax at compact addresses and preserve its
  complete incidence and bindings; decoding gives exactly the data syntax readdressed by an
  injective map that keeps the root. They reject target-bearing terms and preserve malformed
  payload bytes for the separate formation and admission checks.
\<close>

end
