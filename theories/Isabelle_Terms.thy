theory Isabelle_Terms
  imports Finite_Presented_Coordinates
begin

section \<open>Checked Isabelle types and terms are structural subjects\<close>

text \<open>
  Types and terms follow the constructors of the Pure kernel. An abstraction keeps no
  bound name, so structural equality of terms is the kernel's equality up to renaming of
  bound variables. Every name of a type constructor, class, constant, free or schematic
  variable is a position in the name table of its context, so a term retains the
  distinctions of the kernel without repeating any name. A term is stated over what presents
  its types: the kernel's term carries a type at every constant, variable and abstraction
  (\<open>isabelle_term\<close>), and a term whose types are presented elsewhere is the same datatype
  over that presentation, read back through the datatype's own map.
\<close>

datatype isabelle_type =
    Isabelle_Type_Application nat "isabelle_type list"
  | Isabelle_Type_Free nat "nat list"
  | Isabelle_Type_Variable nat nat "nat list"

datatype 'ty isabelle_term_with =
    Isabelle_Constant nat 'ty
  | Isabelle_Free nat 'ty
  | Isabelle_Variable nat nat 'ty
  | Isabelle_Bound nat
  | Isabelle_Abstraction 'ty "'ty isabelle_term_with"
  | Isabelle_Application "'ty isabelle_term_with" "'ty isabelle_term_with"

type_synonym isabelle_term = "isabelle_type isabelle_term_with"

section \<open>Names, positions, types and terms have injective executable presentations\<close>

definition isabelle_name_data :: "String.literal \<Rightarrow> finite_factor_term" where
  "isabelle_name_data s=Finite_Payload (map of_char (String.explode s))"

lemma isabelle_name_data_injective [intro]: "inj isabelle_name_data"
proof (rule injI)
  fix s t assume "isabelle_name_data s=isabelle_name_data t"
  then have "map (of_char :: char \<Rightarrow> nat) (String.explode s)=map of_char (String.explode t)"
    by (simp add: isabelle_name_data_def)
  then have "String.explode s=String.explode t"
    using inj_of_char[where ?'a=nat] by (simp add: inj_map_eq_map)
  then show "s=t" by (simp add: String.explode_inject)
qed

lemma isabelle_name_data_formed [simp]: "finite_term_formed (isabelle_name_data s)"
  by (simp add: isabelle_name_data_def octets_formed_def)

definition isabelle_names_data :: "String.literal list \<Rightarrow> finite_factor_term" where
  "isabelle_names_data=finite_sequence_presentation isabelle_name_data"

lemma isabelle_names_data_injective [intro]: "inj isabelle_names_data"
  unfolding isabelle_names_data_def by (intro finite_sequence_presentation_injective isabelle_name_data_injective)

lemma isabelle_names_data_formed [simp]: "finite_term_formed (isabelle_names_data ss)"
  by (simp add: isabelle_names_data_def finite_sequence_presentation_def finite_data_list_formed list_all_iff)

text \<open>
  A name position uses the existing binary presentation of natural coordinates, so a long
  table costs no nested pair per position.
\<close>

definition isabelle_position_data :: "nat \<Rightarrow> finite_factor_term" where
  "isabelle_position_data=finite_binary_natural_value"

lemma isabelle_position_data_injective [intro]: "inj isabelle_position_data"
  unfolding isabelle_position_data_def by (rule finite_binary_natural_value_injective)

lemma isabelle_position_data_formed [simp]: "finite_term_formed (isabelle_position_data n)"
  by (simp add: isabelle_position_data_def)

definition isabelle_sort_data :: "nat list \<Rightarrow> finite_factor_term" where
  "isabelle_sort_data=finite_sequence_presentation isabelle_position_data"

lemma isabelle_sort_data_injective [intro]: "inj isabelle_sort_data"
  unfolding isabelle_sort_data_def by (intro finite_sequence_presentation_injective isabelle_position_data_injective)

lemma isabelle_sort_data_formed [simp]: "finite_term_formed (isabelle_sort_data S)"
  by (simp add: isabelle_sort_data_def finite_sequence_presentation_def finite_data_list_formed list_all_iff)

fun isabelle_type_data :: "isabelle_type \<Rightarrow> finite_factor_term" where
  "isabelle_type_data (Isabelle_Type_Application c Ts)=Finite_Pair (Finite_Payload [0])
    (Finite_Pair (isabelle_position_data c) (finite_data_list (map isabelle_type_data Ts)))"
| "isabelle_type_data (Isabelle_Type_Free a S)=Finite_Pair (Finite_Payload [1])
    (Finite_Pair (isabelle_position_data a) (isabelle_sort_data S))"
| "isabelle_type_data (Isabelle_Type_Variable a i S)=Finite_Pair (Finite_Payload [2])
    (Finite_Pair (isabelle_position_data a) (Finite_Pair (isabelle_position_data i) (isabelle_sort_data S)))"

lemma isabelle_type_application_sequence:
  "isabelle_type_data (Isabelle_Type_Application c Ts)=Finite_Pair (Finite_Payload [0])
    (Finite_Pair (isabelle_position_data c) (finite_sequence_presentation isabelle_type_data Ts))"
  by (simp add: finite_sequence_presentation_def)

lemma isabelle_type_data_injective [intro]: "inj isabelle_type_data"
proof (rule injI)
  fix T U show "isabelle_type_data T=isabelle_type_data U \<Longrightarrow> T=U"
  proof (induction T arbitrary: U)
    case (Isabelle_Type_Application c Ts)
    from Isabelle_Type_Application.prems obtain Us where U: "U=Isabelle_Type_Application c Us"
      and same: "map isabelle_type_data Ts=map isabelle_type_data Us"
      by (cases U) (auto simp: inj_eq[OF isabelle_position_data_injective] finite_data_list_injective)
    have "Ts=Us" by (rule map_members_injective[OF Isabelle_Type_Application.IH same])
    then show ?case by (simp add: U)
  next
    case (Isabelle_Type_Free a S)
    then show ?case
      by (cases U) (auto simp: inj_eq[OF isabelle_position_data_injective] inj_eq[OF isabelle_sort_data_injective])
  next
    case (Isabelle_Type_Variable a i S)
    then show ?case
      by (cases U) (auto simp: inj_eq[OF isabelle_position_data_injective] inj_eq[OF isabelle_sort_data_injective])
  qed
qed

lemma isabelle_type_data_formed [simp]: "finite_term_formed (isabelle_type_data T)"
  by (induction T) (auto simp: octets_formed_def finite_data_list_formed list_all_iff)

fun isabelle_term_data :: "isabelle_term \<Rightarrow> finite_factor_term" where
  "isabelle_term_data (Isabelle_Constant c T)=Finite_Pair (Finite_Payload [0])
    (Finite_Pair (isabelle_position_data c) (isabelle_type_data T))"
| "isabelle_term_data (Isabelle_Free x T)=Finite_Pair (Finite_Payload [1])
    (Finite_Pair (isabelle_position_data x) (isabelle_type_data T))"
| "isabelle_term_data (Isabelle_Variable x i T)=Finite_Pair (Finite_Payload [2])
    (Finite_Pair (isabelle_position_data x) (Finite_Pair (isabelle_position_data i) (isabelle_type_data T)))"
| "isabelle_term_data (Isabelle_Bound i)=Finite_Pair (Finite_Payload [3]) (isabelle_position_data i)"
| "isabelle_term_data (Isabelle_Abstraction T t)=Finite_Pair (Finite_Payload [4])
    (Finite_Pair (isabelle_type_data T) (isabelle_term_data t))"
| "isabelle_term_data (Isabelle_Application t u)=Finite_Pair (Finite_Payload [5])
    (Finite_Pair (isabelle_term_data t) (isabelle_term_data u))"

lemma isabelle_term_data_injective [intro]: "inj isabelle_term_data"
proof (rule injI)
  fix t u show "isabelle_term_data t=isabelle_term_data u \<Longrightarrow> t=u"
  proof (induction t arbitrary: u)
    case (Isabelle_Constant c T)
    then show ?case
      by (cases u) (auto simp: inj_eq[OF isabelle_position_data_injective] inj_eq[OF isabelle_type_data_injective])
  next
    case (Isabelle_Free x T)
    then show ?case
      by (cases u) (auto simp: inj_eq[OF isabelle_position_data_injective] inj_eq[OF isabelle_type_data_injective])
  next
    case (Isabelle_Variable x i T)
    then show ?case
      by (cases u) (auto simp: inj_eq[OF isabelle_position_data_injective] inj_eq[OF isabelle_type_data_injective])
  next
    case (Isabelle_Bound i)
    then show ?case by (cases u) (auto simp: inj_eq[OF isabelle_position_data_injective])
  next
    case (Isabelle_Abstraction T t)
    then show ?case by (cases u) (auto simp: inj_eq[OF isabelle_type_data_injective])
  next
    case (Isabelle_Application t t')
    then show ?case by (cases u) auto
  qed
qed

lemma isabelle_term_data_formed [simp]: "finite_term_formed (isabelle_term_data t)"
  by (induction t) (simp_all add: octets_formed_def)

theorem isabelle_type_presentation_class:
  "presentation_class (finite_presents isabelle_type_data) (\<lambda>_. True)
    (\<lambda>p. \<exists>T. p=decode_finite_term (isabelle_type_data T))"
  using finite_presents_class[of isabelle_type_data "\<lambda>_. True"] isabelle_type_data_injective by simp

theorem isabelle_term_presentation_class:
  "presentation_class (finite_presents isabelle_term_data) (\<lambda>_. True)
    (\<lambda>p. \<exists>t. p=decode_finite_term (isabelle_term_data t))"
  using finite_presents_class[of isabelle_term_data "\<lambda>_. True"] isabelle_term_data_injective by simp

section \<open>A term keeps the name positions it uses\<close>

fun isabelle_type_positions :: "isabelle_type \<Rightarrow> nat list" where
  "isabelle_type_positions (Isabelle_Type_Application c Ts)=c#concat (map isabelle_type_positions Ts)"
| "isabelle_type_positions (Isabelle_Type_Free a S)=a#S"
| "isabelle_type_positions (Isabelle_Type_Variable a i S)=a#S"

fun isabelle_term_positions :: "isabelle_term \<Rightarrow> nat list" where
  "isabelle_term_positions (Isabelle_Constant c T)=c#isabelle_type_positions T"
| "isabelle_term_positions (Isabelle_Free x T)=x#isabelle_type_positions T"
| "isabelle_term_positions (Isabelle_Variable x i T)=x#isabelle_type_positions T"
| "isabelle_term_positions (Isabelle_Bound i)=[]"
| "isabelle_term_positions (Isabelle_Abstraction T t)=isabelle_type_positions T@isabelle_term_positions t"
| "isabelle_term_positions (Isabelle_Application t u)=isabelle_term_positions t@isabelle_term_positions u"

text \<open>
  Each presentation is one member of its notion's class: it satisfies only injectivity,
  and every client uses that local contract. Name, position, sort, type and term
  presenters are distinct notions composed from the generic payload, binary coordinate,
  sequence and pair presentations. A schematic variable keeps its index, so structural
  equality distinguishes exactly what the kernel distinguishes.
\<close>

end
