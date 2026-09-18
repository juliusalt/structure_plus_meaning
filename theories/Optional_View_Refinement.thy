theory Optional_View_Refinement
  imports Main
begin

datatype optional_view_program = Read_Optional | Project_Optional | Force_Optional
datatype source_reader_program = Keep_Source_Reader | Always_Available
datatype optional_view_requirement = Complete_Optional_View | Original_Source_Reader | No_Repeated_Reader

fun optional_view_run where
  "optional_view_run read project fallback Read_Optional result = map_option read result"
| "optional_view_run read project fallback Project_Optional result = map_option project result"
| "optional_view_run read project fallback Force_Optional result =
    Some (case result of None \<Rightarrow> fallback | Some value \<Rightarrow> project value)"

fun source_reader_run where
  "source_reader_run Keep_Source_Reader check subject = check subject"
| "source_reader_run Always_Available check subject = True"

fun optional_view_calls_reader where
  "optional_view_calls_reader Read_Optional = True"
| "optional_view_calls_reader Project_Optional = False"
| "optional_view_calls_reader Force_Optional = False"

lemma optional_view_no_reader_dependency:
  assumes "\<not> optional_view_calls_reader program"
  shows "optional_view_run read project fallback program result =
    optional_view_run other_read project fallback program result"
  using assms by (cases program) simp_all

definition optional_view_observation where
  "optional_view_observation program requirement = (case requirement of
    Complete_Optional_View \<Rightarrow> fst program \<noteq> Force_Optional
  | Original_Source_Reader \<Rightarrow> snd program = Keep_Source_Reader
  | No_Repeated_Reader \<Rightarrow> \<not> optional_view_calls_reader (fst program))"

locale constructed_optional_view =
  fixes construct :: "'x \<Rightarrow> 'a option"
    and read project :: "'a \<Rightarrow> 'b"
    and fallback :: 'b
    and check :: "'c \<Rightarrow> bool"
    and missing :: 'x and bad_source :: 'c
  assumes original_view: "\<And>x. map_option read (construct x) = map_option project (construct x)"
    and original_refusal: "construct missing = None"
    and original_negative: "\<not> check bad_source"
begin

definition requirement where
  "requirement program facet = (case facet of
    Complete_Optional_View \<Rightarrow> (\<forall>x. (construct x,
      optional_view_run read project fallback (fst program) (construct x)) =
      (construct x,map_option read (construct x)))
  | Original_Source_Reader \<Rightarrow> (\<forall>source.
      source_reader_run (snd program) check source = check source)
  | No_Repeated_Reader \<Rightarrow> \<not> optional_view_calls_reader (fst program))"

lemma complete_view_exact:
  "(\<forall>x. optional_view_run read project fallback program (construct x) =
    map_option read (construct x)) \<longleftrightarrow> program \<noteq> Force_Optional"
proof (cases program)
  case Read_Optional then show ?thesis by simp
next
  case Project_Optional then show ?thesis by (simp add: original_view)
next
  case Force_Optional
  have unequal: "optional_view_run read project fallback program (construct missing) \<noteq>
      map_option read (construct missing)" by (simp add: Force_Optional original_refusal)
  then show ?thesis by (auto simp: Force_Optional)
qed

lemma arbitrary_reader_exact:
  "(\<forall>source. source_reader_run program check source = check source)
    \<longleftrightarrow> program = Keep_Source_Reader"
  using original_negative by (cases program) auto

theorem observation_exact:
  "optional_view_observation program facet = requirement program facet"
  by (cases facet) (simp_all add: optional_view_observation_def requirement_def
    complete_view_exact arbitrary_reader_exact)

end

text \<open>The programs denote their actual optional view and arbitrary-source
  operation. Observation exactness needs the whole original view equation, an
  actual refused constructor input and an actual negative source. The final
  facet identifies interpreter dependence on the original reader; it asserts
  neither an elapsed-time bound nor global optimality.\<close>

end
