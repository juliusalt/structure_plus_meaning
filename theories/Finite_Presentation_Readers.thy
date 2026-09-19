theory Finite_Presentation_Readers
  imports Finite_Presented_Coordinates Factor_Finite_Data_Value_Readers
begin

section \<open>A reader of a presentation reads exactly what the presentation presents\<close>

text \<open>
  A presentation presents a value as an executable term. Its reader maps a term to the value the
  term presents and every other term to nothing: a term is read as a value exactly when it is that
  value's presentation (\<open>finite_reads\<close>). The reader therefore decides the image of the
  presentation and inverts it there, so a term is read without knowing where it came from, and a
  presentation with an exact reader is injective. Readers compose as presentations compose: the
  reader of a pair or a sequence is exact whenever the readers of its parts are, and a reading
  through a partial inverse is exact whenever that inverse is.
\<close>

definition finite_reads :: "(finite_factor_term \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> bool" where
  "finite_reads read present \<longleftrightarrow> (\<forall>t x. read t=Some x \<longleftrightarrow> t=present x)"

lemma finite_readsI:
  assumes "\<And>t x. read t=Some x \<longleftrightarrow> t=present x"
  shows "finite_reads read present"
  using assms by (simp add: finite_reads_def)

lemma finite_readsD:
  assumes "finite_reads read present"
  shows "read t=Some x \<longleftrightarrow> t=present x"
  using assms by (simp add: finite_reads_def)

lemma finite_reads_present:
  assumes "finite_reads read present"
  shows "read (present x)=Some x"
  using finite_readsD[OF assms] by simp

lemma finite_reads_injective:
  assumes reads: "finite_reads read present"
  shows "inj present"
proof (rule injI)
  fix x y assume same: "present x=present y"
  have "read (present x)=Some y" by (simp only: same finite_reads_present[OF reads])
  then show "x=y" by (simp only: finite_reads_present[OF reads] option.inject)
qed

section \<open>Payloads, and readings through a partial inverse\<close>

lemma finite_payload_reads: "finite_reads finite_payload_value_read Finite_Payload"
proof (rule finite_readsI)
  fix t p show "finite_payload_value_read t=Some p \<longleftrightarrow> t=Finite_Payload p"
    by (cases t) simp_all
qed

definition finite_read_through ::
    "('b \<Rightarrow> 'a option) \<Rightarrow> (finite_factor_term \<Rightarrow> 'b option) \<Rightarrow> finite_factor_term \<Rightarrow> 'a option" where
  "finite_read_through decode read t=Option.bind (read t) decode"

theorem finite_read_through_reads:
  assumes reads: "finite_reads read present" and decode: "\<And>y x. decode y=Some x \<longleftrightarrow> y=code x"
  shows "finite_reads (finite_read_through decode read) (present \<circ> code)"
proof (rule finite_readsI)
  fix t x
  show "finite_read_through decode read t=Some x \<longleftrightarrow> t=(present \<circ> code) x"
  proof
    assume "finite_read_through decode read t=Some x"
    then obtain y where "read t=Some y" "decode y=Some x"
      by (auto simp: finite_read_through_def bind_eq_Some_conv)
    then show "t=(present \<circ> code) x" by (simp add: finite_readsD[OF reads] decode)
  next
    assume "t=(present \<circ> code) x"
    then show "finite_read_through decode read t=Some x"
      by (simp add: finite_read_through_def finite_reads_present[OF reads] decode)
  qed
qed

section \<open>Bit paths and binary naturals\<close>

definition finite_path_bits :: "nat list \<Rightarrow> bool list option" where
  "finite_path_bits ds=(if list_all (\<lambda>d. d\<le>1) ds then Some (map (\<lambda>d. d=1) ds) else None)"

lemma finite_path_bits_exact:
  "finite_path_bits ds=Some bs \<longleftrightarrow> ds=map (\<lambda>b. if b then 1 else 0) bs"
proof
  assume "finite_path_bits ds=Some bs"
  then have digits: "list_all (\<lambda>d. d\<le>1) ds" and bits: "bs=map (\<lambda>d. d=1) ds"
    by (simp_all add: finite_path_bits_def split: if_splits)
  have "map (\<lambda>b. if b then 1 else 0) (map (\<lambda>d. d=(1::nat)) ds)=ds"
    using digits by (induction ds) auto
  then show "ds=map (\<lambda>b. if b then 1 else 0) bs" by (simp only: bits)
next
  assume digits: "ds=map (\<lambda>b. if b then 1 else 0) bs"
  have bound: "list_all (\<lambda>d. d\<le>(1::nat)) (map (\<lambda>b. if b then 1 else 0) bs)" by (induction bs) auto
  have restored: "map (\<lambda>d. d=(1::nat)) (map (\<lambda>b. if b then 1 else 0) bs)=bs" by (induction bs) auto
  show "finite_path_bits ds=Some bs" by (simp only: digits finite_path_bits_def bound restored if_True)
qed

definition finite_storage_path_read :: "finite_factor_term \<Rightarrow> bool list option" where
  "finite_storage_path_read=finite_read_through finite_path_bits finite_payload_value_read"

theorem finite_storage_path_reads: "finite_reads finite_storage_path_read finite_storage_path_value"
proof -
  have code: "finite_storage_path_value=Finite_Payload \<circ> (\<lambda>bs. map (\<lambda>b. if b then 1 else 0) bs)"
    by (rule ext) (simp add: finite_storage_path_value_def)
  show ?thesis
    unfolding finite_storage_path_read_def code
    by (rule finite_read_through_reads[OF finite_payload_reads finite_path_bits_exact])
qed

definition finite_natural_digits :: "bool list \<Rightarrow> nat option" where
  "finite_natural_digits bs=(let n=natural_binary_value bs in
    if natural_binary_digits n=bs then Some n else None)"

lemma finite_natural_digits_exact: "finite_natural_digits bs=Some n \<longleftrightarrow> bs=natural_binary_digits n"
  by (auto simp: finite_natural_digits_def Let_def)

definition finite_binary_natural_read :: "finite_factor_term \<Rightarrow> nat option" where
  "finite_binary_natural_read=finite_read_through finite_natural_digits finite_storage_path_read"

theorem finite_binary_natural_reads: "finite_reads finite_binary_natural_read finite_binary_natural_value"
proof -
  have code: "finite_binary_natural_value=finite_storage_path_value \<circ> natural_binary_digits"
    by (rule ext) (simp add: finite_binary_natural_value_def)
  show ?thesis
    unfolding finite_binary_natural_read_def code
    by (rule finite_read_through_reads[OF finite_storage_path_reads finite_natural_digits_exact])
qed

section \<open>Pairs and sequences\<close>

fun finite_pair_read ::
    "(finite_factor_term \<Rightarrow> 'a option) \<Rightarrow> (finite_factor_term \<Rightarrow> 'b option) \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a\<times>'b) option" where
  "finite_pair_read left right (Finite_Pair a b)=(case left a of None \<Rightarrow> None
    | Some x \<Rightarrow> map_option (Pair x) (right b))"
| "finite_pair_read left right (Finite_Payload p)=None"
| "finite_pair_read left right (Finite_Target v)=None"

theorem finite_pair_reads:
  assumes left: "finite_reads left f" and right: "finite_reads right g"
  shows "finite_reads (finite_pair_read left right) (finite_pair_presentation f g)"
proof (rule finite_readsI)
  fix t z
  show "finite_pair_read left right t=Some z \<longleftrightarrow> t=finite_pair_presentation f g z"
  proof (cases t)
    case (Finite_Pair a b)
    obtain x y where z: "z=(x,y)" by (cases z)
    show ?thesis
      by (auto simp: Finite_Pair z finite_readsD[OF left] finite_readsD[OF right] finite_reads_present[OF left]
        finite_reads_present[OF right] inj_eq[OF finite_reads_injective[OF left]]
        inj_eq[OF finite_reads_injective[OF right]] split: option.splits)
  qed (simp_all add: finite_pair_presentation_def)
qed

definition finite_sequence_read ::
    "(finite_factor_term \<Rightarrow> 'a option) \<Rightarrow> finite_factor_term \<Rightarrow> 'a list option" where
  "finite_sequence_read read t=Option.bind (finite_data_list_read t) (\<lambda>xs. those (map read xs))"

lemma finite_data_sequence_list: "foldr Finite_Pair xs (Finite_Payload [])=finite_data_list xs"
  by (induction xs) simp_all

lemma those_map_reads:
  assumes reads: "finite_reads read present"
  shows "those (map read xs)=Some ys \<longleftrightarrow> xs=map present ys"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof
    assume "those (map read (x#xs))=Some ys"
    then obtain y zs where "read x=Some y" "those (map read xs)=Some zs" "ys=y#zs"
      by (auto split: option.splits)
    then show "x#xs=map present ys" using Cons.IH[of zs] by (simp add: finite_readsD[OF reads])
  next
    assume "x#xs=map present ys"
    then obtain y zs where "ys=y#zs" "x=present y" "xs=map present zs" by (cases ys) auto
    then show "those (map read (x#xs))=Some ys"
      using Cons.IH[of zs] by (simp add: finite_reads_present[OF reads])
  qed
qed

theorem finite_sequence_reads:
  assumes reads: "finite_reads read present"
  shows "finite_reads (finite_sequence_read read) (finite_sequence_presentation present)"
proof (rule finite_readsI)
  fix t ys
  show "finite_sequence_read read t=Some ys \<longleftrightarrow> t=finite_sequence_presentation present ys"
  proof
    assume "finite_sequence_read read t=Some ys"
    then obtain xs where "finite_data_list_read t=Some xs" "those (map read xs)=Some ys"
      by (auto simp: finite_sequence_read_def bind_eq_Some_conv)
    then show "t=finite_sequence_presentation present ys"
      by (simp add: finite_data_list_read_sequence finite_data_sequence_list those_map_reads[OF reads]
        finite_sequence_presentation_def)
  next
    assume "t=finite_sequence_presentation present ys"
    then have "finite_data_list_read t=Some (map present ys)"
      by (simp add: finite_data_list_read_sequence finite_data_sequence_list finite_sequence_presentation_def)
    moreover have "those (map read (map present ys))=Some ys" by (simp only: those_map_reads[OF reads])
    ultimately show "finite_sequence_read read t=Some ys" by (simp add: finite_sequence_read_def)
  qed
qed

text \<open>
  Each reader is stated once for its presentation, and every reader built from these by pairing,
  sequencing or a partial inverse is exact by the composition theorems alone; no composed reader
  is proved again.
\<close>

end
