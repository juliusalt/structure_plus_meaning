theory Finite_Term_Word_Readers
  imports Finite_Term_Words
begin

section \<open>The word of a term without targets is read back\<close>

text \<open>
  A report or an answer is transported as the prefix-free digit word of its presented term
  (\<open>finite_term_shared_word\<close>), and the host packs the bits into octets followed by one
  terminating bit and zero padding. A term that holds no target has an empty table of artifact
  rows, so its word is the empty count followed by the term's own word. The readers below invert
  each layer exactly: the digit words of naturals and addresses, the term word, the shared word of
  a term without targets and the padding, so a transported word is read as the term it presents or
  refused. Only unpacking octets into bits is left to the host, as packing bits into octets is.
\<close>

fun digit_naturals_read :: "nat \<Rightarrow> bool list \<Rightarrow> (nat list\<times>bool list) option" where
  "digit_naturals_read 0 source=Some ([],source)"
| "digit_naturals_read (Suc n) source=(case read_digit_natural_path source of None \<Rightarrow> None
    | Some (d,rest) \<Rightarrow> map_option (\<lambda>(ds,after). (d#ds,after)) (digit_naturals_read n rest))"

text \<open>
  The readers are defined by the count they still have to read; they execute through equations
  that test that count instead of matching it as a successor, so they run where naturals are
  machine integers.
\<close>

lemma digit_naturals_read_code [code]:
  "digit_naturals_read n source=(case n of 0 \<Rightarrow> Some ([],source) | Suc m \<Rightarrow>
    (case read_digit_natural_path source of None \<Rightarrow> None
    | Some (d,rest) \<Rightarrow> map_option (\<lambda>(ds,after). (d#ds,after)) (digit_naturals_read m rest)))"
  by (cases n) simp_all

lemma digit_naturals_read_exact:
  "digit_naturals_read n source=Some (ds,rest) \<longleftrightarrow>
    length ds=n \<and> source=prefix_word_encoding digit_natural_path ds@rest"
proof (induction n arbitrary: source ds)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case
  proof
    assume "digit_naturals_read (Suc n) source=Some (ds,rest)"
    then obtain d rest0 ds' where first: "read_digit_natural_path source=Some (d,rest0)"
      and others: "digit_naturals_read n rest0=Some (ds',rest)" and list: "ds=d#ds'"
      by (auto split: option.splits)
    have "source=digit_natural_path d@rest0" using first by (simp only: read_digit_natural_path_exact)
    moreover have "length ds'=n \<and> rest0=prefix_word_encoding digit_natural_path ds'@rest"
      using others Suc.IH by blast
    ultimately show "length ds=Suc n \<and> source=prefix_word_encoding digit_natural_path ds@rest"
      by (simp add: list)
  next
    assume "length ds=Suc n \<and> source=prefix_word_encoding digit_natural_path ds@rest"
    then obtain d ds' where list: "ds=d#ds'" and count: "length ds'=n"
      and word: "source=digit_natural_path d@(prefix_word_encoding digit_natural_path ds'@rest)"
      by (cases ds) auto
    have "digit_naturals_read n (prefix_word_encoding digit_natural_path ds'@rest)=Some (ds',rest)"
      using Suc.IH count by blast
    then show "digit_naturals_read (Suc n) source=Some (ds,rest)" by (simp add: word list)
  qed
qed

definition digit_address_word_read :: "bool list \<Rightarrow> (local_address\<times>bool list) option" where
  "digit_address_word_read source=(case read_digit_natural_path source of None \<Rightarrow> None
    | Some (n,rest) \<Rightarrow> digit_naturals_read n rest)"

theorem digit_address_word_read_exact:
  "digit_address_word_read source=Some (a,rest) \<longleftrightarrow> source=digit_address_word a@rest"
proof
  assume "digit_address_word_read source=Some (a,rest)"
  then obtain n rest0 where count: "read_digit_natural_path source=Some (n,rest0)"
    and digits: "digit_naturals_read n rest0=Some (a,rest)"
    by (auto simp: digit_address_word_read_def split: option.splits)
  have "source=digit_natural_path n@rest0" using count by (simp only: read_digit_natural_path_exact)
  moreover have "length a=n \<and> rest0=prefix_word_encoding digit_natural_path a@rest"
    using digits by (simp only: digit_naturals_read_exact)
  ultimately show "source=digit_address_word a@rest"
    by (simp add: digit_address_word_def counted_digit_word_def)
next
  assume word: "source=digit_address_word a@rest"
  have "read_digit_natural_path source=Some (length a,prefix_word_encoding digit_natural_path a@rest)"
    by (simp add: word digit_address_word_def counted_digit_word_def)
  moreover have "digit_naturals_read (length a) (prefix_word_encoding digit_natural_path a@rest)=Some (a,rest)"
    by (simp only: digit_naturals_read_exact)
  ultimately show "digit_address_word_read source=Some (a,rest)" by (simp add: digit_address_word_read_def)
qed

lemma digit_address_word_read_word [simp]:
  "digit_address_word_read (digit_address_word a@rest)=Some (a,rest)"
  by (simp only: digit_address_word_read_exact)

section \<open>A term word is read by recursion over its constructors\<close>

fun finite_term_word_read_fuel :: "nat \<Rightarrow> bool list \<Rightarrow> (finite_factor_term\<times>bool list) option" where
  "finite_term_word_read_fuel 0 source=None"
| "finite_term_word_read_fuel (Suc n) (True#source)=(case finite_term_word_read_fuel n source of None \<Rightarrow> None
    | Some (t,rest) \<Rightarrow> map_option (\<lambda>(u,after). (Finite_Pair t u,after)) (finite_term_word_read_fuel n rest))"
| "finite_term_word_read_fuel (Suc n) (False#False#source)=
    map_option (\<lambda>(v,rest). (Finite_Payload v,rest)) (digit_address_word_read source)"
| "finite_term_word_read_fuel (Suc n) []=None"
| "finite_term_word_read_fuel (Suc n) [False]=None"
| "finite_term_word_read_fuel (Suc n) (False#True#source)=None"

lemma finite_term_word_read_fuel_code [code]:
  "finite_term_word_read_fuel n source=(case n of 0 \<Rightarrow> None | Suc m \<Rightarrow> (case source of
      True#rest \<Rightarrow> (case finite_term_word_read_fuel m rest of None \<Rightarrow> None
        | Some (t,after) \<Rightarrow> map_option (\<lambda>(u,final). (Finite_Pair t u,final)) (finite_term_word_read_fuel m after))
    | False#False#rest \<Rightarrow> map_option (\<lambda>(v,after). (Finite_Payload v,after)) (digit_address_word_read rest)
    | _ \<Rightarrow> None))"
  by (cases "(n,source)" rule: finite_term_word_read_fuel.cases) simp_all

lemma finite_term_word_read_fuel_sound:
  "finite_term_word_read_fuel n source=Some (t,rest) \<Longrightarrow>
    source=finite_term_word_with leaf t@rest \<and> finite_term_targets t={}"
proof (induction n source arbitrary: t rest rule: finite_term_word_read_fuel.induct)
  case (2 n source)
  from "2.prems" obtain t0 rest0 u where first: "finite_term_word_read_fuel n source=Some (t0,rest0)"
    and second: "finite_term_word_read_fuel n rest0=Some (u,rest)" and pair: "t=Finite_Pair t0 u"
    by (auto split: option.splits)
  have left: "source=finite_term_word_with leaf t0@rest0 \<and> finite_term_targets t0={}"
    by (rule "2.IH"(1)[OF first])
  have right: "rest0=finite_term_word_with leaf u@rest \<and> finite_term_targets u={}"
    by (rule "2.IH"(2)[OF first refl second])
  show ?case using left right by (simp add: pair)
next
  case (3 n source)
  then obtain v where "digit_address_word_read source=Some (v,rest)" "t=Finite_Payload v"
    by (auto split: option.splits)
  then show ?case by (simp add: digit_address_word_read_exact)
qed simp_all

fun finite_term_depth :: "finite_factor_term \<Rightarrow> nat" where
  "finite_term_depth (Finite_Pair t u)=Suc (max (finite_term_depth t) (finite_term_depth u))"
| "finite_term_depth (Finite_Payload v)=0"
| "finite_term_depth (Finite_Target x)=0"

lemma finite_term_word_read_fuel_complete:
  "finite_term_targets t={} \<Longrightarrow> finite_term_depth t<n \<Longrightarrow>
    finite_term_word_read_fuel n (finite_term_word_with leaf t@rest)=Some (t,rest)"
proof (induction t arbitrary: n rest)
  case (Finite_Pair t u)
  obtain m where n: "n=Suc m" using Finite_Pair.prems(2) by (cases n) auto
  have left: "finite_term_word_read_fuel m (finite_term_word_with leaf t@(finite_term_word_with leaf u@rest))=
      Some (t,finite_term_word_with leaf u@rest)"
    using Finite_Pair.IH(1) Finite_Pair.prems n by auto
  have right: "finite_term_word_read_fuel m (finite_term_word_with leaf u@rest)=Some (u,rest)"
    using Finite_Pair.IH(2) Finite_Pair.prems n by auto
  show ?case using left right by (simp add: n)
next
  case (Finite_Payload v)
  then obtain m where "n=Suc m" by (cases n) auto
  then show ?case by simp
next
  case (Finite_Target x)
  then show ?case by simp
qed

lemma finite_term_word_depth: "finite_term_depth t<length (finite_term_word_with leaf t)"
  by (induction t) auto

definition finite_term_word_read :: "bool list \<Rightarrow> (finite_factor_term\<times>bool list) option" where
  "finite_term_word_read source=finite_term_word_read_fuel (length source) source"

theorem finite_term_word_read_exact:
  "finite_term_word_read source=Some (t,rest) \<longleftrightarrow>
    source=finite_term_word_with leaf t@rest \<and> finite_term_targets t={}"
proof
  assume "finite_term_word_read source=Some (t,rest)"
  then show "source=finite_term_word_with leaf t@rest \<and> finite_term_targets t={}"
    unfolding finite_term_word_read_def by (rule finite_term_word_read_fuel_sound)
next
  assume word: "source=finite_term_word_with leaf t@rest \<and> finite_term_targets t={}"
  have "finite_term_depth t<length source"
    using finite_term_word_depth[of t leaf] word by simp
  then show "finite_term_word_read source=Some (t,rest)"
    using finite_term_word_read_fuel_complete[of t "length source" leaf rest] word
    by (simp add: finite_term_word_read_def)
qed

section \<open>The shared word of a term without targets\<close>

lemma finite_term_word_target_free:
  "finite_term_targets t={} \<Longrightarrow> finite_term_word_with leaf t=finite_term_word_with leaf' t"
  by (induction t) auto

lemma finite_term_rows_target_free: "finite_term_targets t={} \<Longrightarrow> finite_term_rows t=[]"
  using finite_term_rows_onto_set[of t "[]"] by (simp add: finite_term_rows_def)

lemma finite_term_shared_word_target_free:
  assumes free: "finite_term_targets t={}"
  shows "finite_term_shared_word t=digit_natural_path 0@finite_term_word_with leaf t"
proof -
  have word: "finite_term_word_with (finite_target_reference_word []) t=finite_term_word_with leaf t"
    by (rule finite_term_word_target_free[OF free])
  show ?thesis
    by (simp add: finite_term_shared_word_def finite_term_rows_target_free[OF free] counted_digit_word_def word)
qed

definition finite_shared_word_read :: "bool list \<Rightarrow> finite_factor_term option" where
  "finite_shared_word_read source=(case read_digit_natural_path source of None \<Rightarrow> None
    | Some (n,rest) \<Rightarrow> if n=0 then (case finite_term_word_read rest of None \<Rightarrow> None
        | Some (t,after) \<Rightarrow> if after=[] then Some t else None) else None)"

theorem finite_shared_word_read_exact:
  "finite_shared_word_read source=Some t \<longleftrightarrow> source=finite_term_shared_word t \<and> finite_term_targets t={}"
proof
  assume "finite_shared_word_read source=Some t"
  then obtain rest where count: "read_digit_natural_path source=Some (0,rest)"
    and body: "finite_term_word_read rest=Some (t,[])"
    by (auto simp: finite_shared_word_read_def split: option.splits if_splits)
  have "rest=finite_term_word_with (\<lambda>_. []) t@[] \<and> finite_term_targets t={}"
    using body finite_term_word_read_exact[of rest t "[]" "\<lambda>_. []"] by blast
  moreover have "source=digit_natural_path 0@rest" using count by (simp only: read_digit_natural_path_exact)
  ultimately show "source=finite_term_shared_word t \<and> finite_term_targets t={}"
    using finite_term_shared_word_target_free[of t "\<lambda>_. []"] by simp
next
  assume word: "source=finite_term_shared_word t \<and> finite_term_targets t={}"
  then have source: "source=digit_natural_path 0@finite_term_word_with (\<lambda>_. []) t"
    using finite_term_shared_word_target_free[of t "\<lambda>_. []"] by simp
  have "finite_term_word_read (finite_term_word_with (\<lambda>_. []) t)=Some (t,[])"
    using word finite_term_word_read_exact[of "finite_term_word_with (\<lambda>_. []) t" t "[]" "\<lambda>_. []"] by simp
  then show "finite_shared_word_read source=Some t" by (simp add: finite_shared_word_read_def source)
qed

section \<open>Padding is one terminating bit followed by zeros\<close>

definition finite_padded_word_read :: "bool list \<Rightarrow> bool list option" where
  "finite_padded_word_read bits=(case dropWhile Not (rev bits) of [] \<Rightarrow> None
    | b#rest \<Rightarrow> Some (rev rest))"

lemma finite_padded_word_read_exact:
  "finite_padded_word_read bits=Some w \<longleftrightarrow> (\<exists>k. bits=w@True#replicate k False)"
proof
  assume read: "finite_padded_word_read bits=Some w"
  obtain b rest where dropped: "dropWhile Not (rev bits)=b#rest" and word: "w=rev rest"
    using read by (auto simp: finite_padded_word_read_def split: list.splits)
  have bit: "b" using dropped dropWhile_eq_Cons_conv[of Not "rev bits" b rest] by auto
  have zeros: "takeWhile Not (rev bits)=replicate (length (takeWhile Not (rev bits))) False"
    by (rule replicate_eqI) (auto dest: set_takeWhileD)
  have "rev bits=takeWhile Not (rev bits)@dropWhile Not (rev bits)" by simp
  then have "rev bits=replicate (length (takeWhile Not (rev bits))) False@True#rest"
    using zeros dropped bit by simp
  then have "bits=rev rest@True#replicate (length (takeWhile Not (rev bits))) False"
    by (metis rev_append rev_replicate rev_rev_ident rev.simps(2) append_Cons append.left_neutral append.assoc)
  then show "\<exists>k. bits=w@True#replicate k False" by (auto simp: word)
next
  assume "\<exists>k. bits=w@True#replicate k False"
  then obtain k where bits: "bits=w@True#replicate k False" by blast
  have "dropWhile Not (rev bits)=True#rev w"
    by (simp add: bits dropWhile_append)
  then show "finite_padded_word_read bits=Some w" by (simp add: finite_padded_word_read_def)
qed

definition finite_padded_term_read :: "bool list \<Rightarrow> finite_factor_term option" where
  "finite_padded_term_read bits=Option.bind (finite_padded_word_read bits) finite_shared_word_read"

theorem finite_padded_term_read_exact:
  "finite_padded_term_read bits=Some t \<longleftrightarrow>
    (\<exists>k. bits=finite_term_shared_word t@True#replicate k False) \<and> finite_term_targets t={}"
  by (auto simp: finite_padded_term_read_def bind_eq_Some_conv finite_padded_word_read_exact
    finite_shared_word_read_exact)

text \<open>
  Reading refuses every word that is not exactly the padded word of a term without targets; the
  term read is the only term with that word, since the word is injective
  (\<open>finite_term_shared_word_injective\<close>). A word with targets is refused: its table of artifact
  rows has its own reader to be established when a transported value needs one.
\<close>

end
