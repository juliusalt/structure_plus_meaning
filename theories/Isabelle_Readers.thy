theory Isabelle_Readers
  imports Isabelle_Entities Finite_Presentation_Readers
begin

section \<open>A presented name, type, term or entity is read back exactly\<close>

text \<open>
  The presentations of names, positions, sorts, types, terms and entities are injective; their
  readers invert them exactly on their images, so a presented entity arriving from anywhere is
  read as the entity it presents or refused. Positions and sorts are read by the generic binary
  natural and sequence readers; a name is read through the octets of its characters, which the
  presentation keeps below 128; a type and a term are read by recursion over their constructors,
  each constructor identified by the payload its presentation begins with, as the presentation
  identifies it. The payload is read as a value and compared, not matched as a pattern of
  successors, so the readers execute where naturals are machine integers.
\<close>

definition isabelle_name_octets :: "nat list \<Rightarrow> String.literal option" where
  "isabelle_name_octets os=(if list_all (\<lambda>k. k<128) os then Some (String.implode (map char_of os)) else None)"

lemma isabelle_name_char_bound:
  assumes member: "c\<in>set (String.explode s)"
  shows "of_char c<(128::nat)"
proof -
  have "String.explode s\<in>{cs. \<forall>c\<in>set cs. \<not> digit7 c}" by (rule String.explode)
  then have ascii: "\<not> digit7 c" using member by blast
  have "(of_char c::nat)=of_char (String.ascii_of c)" by (simp only: String.ascii_of_idem[OF ascii])
  also have "\<dots>=take_bit 7 (of_char c)" by (rule String.char_of_ascii_of)
  also have "\<dots><2^7" by (rule take_bit_nat_less_exp)
  finally show ?thesis by simp
qed

lemma isabelle_name_octet_char:
  assumes "k<(128::nat)"
  shows "of_char (String.ascii_of (char_of k))=k"
proof -
  have "(of_char (String.ascii_of (char_of k))::nat)=take_bit 7 (of_char (char_of k))"
    by (rule String.char_of_ascii_of)
  also have "\<dots>=take_bit 7 (k mod 256)" by simp
  also have "\<dots>=k" using assms by (simp add: take_bit_eq_mod)
  finally show ?thesis .
qed

lemma isabelle_name_octets_exact:
  "isabelle_name_octets os=Some s \<longleftrightarrow> os=map of_char (String.explode s)"
proof
  assume read: "isabelle_name_octets os=Some s"
  then have bound: "list_all (\<lambda>k. k<128) os" and name: "s=String.implode (map char_of os)"
    by (simp_all add: isabelle_name_octets_def split: if_splits)
  have "map of_char (String.explode s)=map (\<lambda>k. of_char (String.ascii_of (char_of k))) os"
    by (simp add: name)
  also have "\<dots>=os" using bound by (induction os) (simp_all add: take_bit_eq_mod)
  finally show "os=map of_char (String.explode s)" by simp
next
  assume octets: "os=map of_char (String.explode s)"
  have bound: "list_all (\<lambda>k. k<(128::nat)) os"
    using isabelle_name_char_bound by (auto simp: octets list_all_iff)
  have "String.implode (map char_of os)=s" by (simp add: octets comp_def)
  then show "isabelle_name_octets os=Some s" using bound by (simp add: isabelle_name_octets_def)
qed

definition isabelle_name_read :: "finite_factor_term \<Rightarrow> String.literal option" where
  "isabelle_name_read=finite_read_through isabelle_name_octets finite_payload_value_read"

theorem isabelle_name_reads: "finite_reads isabelle_name_read isabelle_name_data"
proof -
  have code: "isabelle_name_data=Finite_Payload \<circ> (\<lambda>s. map of_char (String.explode s))"
    by (rule ext) (simp add: isabelle_name_data_def)
  show ?thesis
    unfolding isabelle_name_read_def code
    by (rule finite_read_through_reads[OF finite_payload_reads isabelle_name_octets_exact])
qed

definition isabelle_names_read :: "finite_factor_term \<Rightarrow> String.literal list option" where
  "isabelle_names_read=finite_sequence_read isabelle_name_read"

theorem isabelle_names_reads: "finite_reads isabelle_names_read isabelle_names_data"
  unfolding isabelle_names_read_def isabelle_names_data_def by (rule finite_sequence_reads[OF isabelle_name_reads])

definition isabelle_position_read :: "finite_factor_term \<Rightarrow> nat option" where
  "isabelle_position_read=finite_binary_natural_read"

theorem isabelle_position_reads: "finite_reads isabelle_position_read isabelle_position_data"
  unfolding isabelle_position_read_def isabelle_position_data_def by (rule finite_binary_natural_reads)

definition isabelle_sort_read :: "finite_factor_term \<Rightarrow> nat list option" where
  "isabelle_sort_read=finite_sequence_read isabelle_position_read"

theorem isabelle_sort_reads: "finite_reads isabelle_sort_read isabelle_sort_data"
  unfolding isabelle_sort_read_def isabelle_sort_data_def by (rule finite_sequence_reads[OF isabelle_position_reads])

lemmas isabelle_part_reads=finite_readsD[OF isabelle_position_reads] finite_readsD[OF isabelle_sort_reads]
  finite_reads_present[OF isabelle_position_reads] finite_reads_present[OF isabelle_sort_reads]

section \<open>Types and terms are read by recursion over their constructors\<close>

fun isabelle_type_read :: "finite_factor_term \<Rightarrow> isabelle_type option"
and isabelle_types_read :: "finite_factor_term \<Rightarrow> isabelle_type list option" where
  "isabelle_type_read (Finite_Pair (Finite_Payload k) (Finite_Pair a b))=
    (case isabelle_position_read a of None \<Rightarrow> None | Some a' \<Rightarrow>
      if k=[0] then map_option (Isabelle_Type_Application a') (isabelle_types_read b)
      else if k=[1] then map_option (Isabelle_Type_Free a') (isabelle_sort_read b)
      else if k=[2] then (case b of
          Finite_Pair i S \<Rightarrow> (case isabelle_position_read i of None \<Rightarrow> None
            | Some i' \<Rightarrow> map_option (Isabelle_Type_Variable a' i') (isabelle_sort_read S))
        | _ \<Rightarrow> None)
      else None)"
| "isabelle_type_read _=None"
| "isabelle_types_read (Finite_Payload [])=Some []"
| "isabelle_types_read (Finite_Pair T Ts)=(case isabelle_type_read T of None \<Rightarrow> None
    | Some T' \<Rightarrow> map_option (Cons T') (isabelle_types_read Ts))"
| "isabelle_types_read _=None"

lemma isabelle_types_read_data:
  assumes "\<And>T. T\<in>set Ts \<Longrightarrow> isabelle_type_read (isabelle_type_data T)=Some T"
  shows "isabelle_types_read (finite_data_list (map isabelle_type_data Ts))=Some Ts"
  using assms by (induction Ts) simp_all

lemma isabelle_type_read_data: "isabelle_type_read (isabelle_type_data T)=Some T"
proof (induction T)
  case (Isabelle_Type_Application c Ts)
  then show ?case by (simp add: isabelle_types_read_data isabelle_part_reads)
next
  case (Isabelle_Type_Free a S)
  then show ?case by (simp add: isabelle_part_reads)
next
  case (Isabelle_Type_Variable a i S)
  then show ?case by (simp add: isabelle_part_reads)
qed

lemma isabelle_type_read_sound:
  "isabelle_type_read t=Some T \<Longrightarrow> t=isabelle_type_data T"
  "isabelle_types_read u=Some Ts \<Longrightarrow> u=finite_data_list (map isabelle_type_data Ts)"
  by (induction t and u arbitrary: T and Ts rule: isabelle_type_read_isabelle_types_read.induct)
    (auto simp: isabelle_part_reads split: option.splits prod.splits if_splits finite_factor_term.splits)

theorem isabelle_type_reads: "finite_reads isabelle_type_read isabelle_type_data"
  by (rule finite_readsI) (use isabelle_type_read_sound(1) isabelle_type_read_data in blast)

lemmas isabelle_type_part_reads=finite_readsD[OF isabelle_type_reads] finite_reads_present[OF isabelle_type_reads]

fun isabelle_term_read :: "finite_factor_term \<Rightarrow> isabelle_term option" where
  "isabelle_term_read (Finite_Pair (Finite_Payload k) b)=
    (if k=[3] then map_option Isabelle_Bound (isabelle_position_read b)
     else case b of
       Finite_Pair x y \<Rightarrow>
         (if k=[0] then (case (isabelle_position_read x,isabelle_type_read y) of
             (Some c',Some T') \<Rightarrow> Some (Isabelle_Constant c' T') | _ \<Rightarrow> None)
          else if k=[1] then (case (isabelle_position_read x,isabelle_type_read y) of
             (Some x',Some T') \<Rightarrow> Some (Isabelle_Free x' T') | _ \<Rightarrow> None)
          else if k=[2] then (case y of
              Finite_Pair i T \<Rightarrow> (case (isabelle_position_read x,isabelle_position_read i,isabelle_type_read T) of
                (Some x',Some i',Some T') \<Rightarrow> Some (Isabelle_Variable x' i' T') | _ \<Rightarrow> None)
            | _ \<Rightarrow> None)
          else if k=[4] then (case (isabelle_type_read x,isabelle_term_read y) of
             (Some T',Some t') \<Rightarrow> Some (Isabelle_Abstraction T' t') | _ \<Rightarrow> None)
          else if k=[5] then (case (isabelle_term_read x,isabelle_term_read y) of
             (Some t',Some u') \<Rightarrow> Some (Isabelle_Application t' u') | _ \<Rightarrow> None)
          else None)
     | _ \<Rightarrow> None)"
| "isabelle_term_read _=None"

lemma isabelle_term_read_data: "isabelle_term_read (isabelle_term_data t)=Some t"
  by (induction t) (simp_all add: isabelle_part_reads isabelle_type_part_reads)

lemma isabelle_term_read_sound: "isabelle_term_read s=Some t \<Longrightarrow> s=isabelle_term_data t"
  by (induction s arbitrary: t rule: isabelle_term_read.induct)
    (auto simp: isabelle_part_reads isabelle_type_part_reads
      split: option.splits prod.splits if_splits finite_factor_term.splits)

theorem isabelle_term_reads: "finite_reads isabelle_term_read isabelle_term_data"
  by (rule finite_readsI) (use isabelle_term_read_sound isabelle_term_read_data in blast)

lemmas isabelle_term_part_reads=finite_readsD[OF isabelle_term_reads] finite_reads_present[OF isabelle_term_reads]

section \<open>Entities and contexts\<close>

definition isabelle_entity_read :: "finite_factor_term \<Rightarrow> isabelle_entity option" where
  "isabelle_entity_read s=(case s of
      Finite_Pair (Finite_Payload k) t \<Rightarrow>
        (if k=[0] then map_option Isabelle_Base_Constant (isabelle_term_read t)
         else if k=[1] then map_option Isabelle_Development_Constant (isabelle_term_read t)
         else if k=[2] then map_option Isabelle_Frontier_Constant (isabelle_term_read t)
         else if k=[3] then map_option Isabelle_Definition (isabelle_term_read t)
         else if k=[4] then map_option Isabelle_Specification (isabelle_term_read t)
         else if k=[5] then map_option Isabelle_Code_Equation (isabelle_term_read t)
         else None)
    | _ \<Rightarrow> None)"

theorem isabelle_entity_reads: "finite_reads isabelle_entity_read isabelle_entity_data"
proof (rule finite_readsI)
  fix s e
  show "isabelle_entity_read s=Some e \<longleftrightarrow> s=isabelle_entity_data e"
  proof
    assume "isabelle_entity_read s=Some e"
    then show "s=isabelle_entity_data e"
      by (auto simp: isabelle_entity_read_def isabelle_term_part_reads split: finite_factor_term.splits if_splits)
  next
    assume "s=isabelle_entity_data e"
    then show "isabelle_entity_read s=Some e"
      by (cases e) (simp_all add: isabelle_entity_read_def isabelle_term_part_reads)
  qed
qed

definition isabelle_context_read :: "finite_factor_term \<Rightarrow> isabelle_context option" where
  "isabelle_context_read=finite_pair_read isabelle_names_read (finite_sequence_read isabelle_entity_read)"

theorem isabelle_context_reads: "finite_reads isabelle_context_read isabelle_context_data"
  unfolding isabelle_context_read_def isabelle_context_data_def
  by (intro finite_pair_reads finite_sequence_reads isabelle_names_reads isabelle_entity_reads)

text \<open>
  Every reader here is exact for its presentation, so the presentations are the readers' images and
  nothing read is ever more than a presentation says: a term that presents no entity, or an entity
  with a malformed part, is refused as a whole.
\<close>

end
