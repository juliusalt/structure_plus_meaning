theory RRA_Executable_Retention
  imports RRA_Executable_Citations RRA_Read_Environment Bootstrap_Finite_Closure
begin

section \<open>Finite environment closure follows the supplied bindings\<close>

definition finite_environment_uses :: "'u finite_artifact_environment \<Rightarrow> 'u fset" where
  "finite_environment_uses E = fimage fst (finite_environment_artifacts E)"

lemma finite_environment_uses_correct:
  "fset (finite_environment_uses E) = environment_uses (decode_finite_environment E)"
  by (simp add: finite_environment_uses_def environment_uses_def rel_dom_image fimage.rep_eq)

definition finite_environment_edges :: "'u finite_artifact_environment \<Rightarrow> ('u \<times> 'u) fset" where
  "finite_environment_edges E = fimage (\<lambda>((u,k),v). (u,v)) (finite_environment_bindings E)"

lemma finite_environment_edges_correct:
  "fset (finite_environment_edges E) = environment_edges (decode_finite_environment E)"
  by (auto simp: finite_environment_edges_def environment_edges_def binds_slot_def fimage.rep_eq
      split: prod.splits; force)

definition finite_environment_reachable :: "'u finite_artifact_environment \<Rightarrow> 'u fset \<Rightarrow> 'u fset" where
  "finite_environment_reachable E roots = roots |\<union>| fimage snd
    (ffilter (\<lambda>(u,v). u |\<in>| roots) (finite_edge_closure (finite_environment_edges E)))"

lemma finite_environment_reachable_correct:
  "fset (finite_environment_reachable E roots) = environment_reachable (decode_finite_environment E) (fset roots)"
  by (auto simp: finite_environment_reachable_def environment_reachable_def fimage.rep_eq
      finite_edge_closure_correct finite_environment_edges_correct rtrancl_eq_or_trancl
      split: prod.splits; force)

definition finite_environment_closed ::
  "'u finite_artifact_environment \<Rightarrow> 'u fset \<Rightarrow> ('u \<times> local_address) fset \<Rightarrow> bool" where
  "finite_environment_closed E roots demands \<longleftrightarrow>
    finite_environment_formed E \<and> roots |\<subseteq>| finite_environment_uses E \<and>
    finite_environment_uses E=finite_environment_reachable E roots \<and>
    fimage fst (finite_environment_bindings E)=demands"

theorem finite_environment_closed_correct:
  "finite_environment_closed E roots demands \<longleftrightarrow>
    environment_closed (decode_finite_environment E) (fset roots) (fset demands)"
  by (simp add: finite_environment_closed_def environment_closed_def finite_environment_formed_correct
      fset_inject[symmetric] finite_environment_uses_correct finite_environment_reachable_correct
      less_eq_fset.rep_eq fimage.rep_eq rel_dom_image)

section \<open>Retention keeps exactly the sources and demanded bindings\<close>

definition finite_read_environment_uses ::
  "'u finite_artifact_environment \<Rightarrow> 'u fset \<Rightarrow> ('u \<times> local_address) fset \<Rightarrow> 'u fset" where
  "finite_read_environment_uses E U D = U |\<union>| fimage snd
    (ffilter (\<lambda>entry. fst entry |\<in>| D) (finite_environment_bindings E))"

lemma finite_read_environment_uses_correct:
  "fset (finite_read_environment_uses E U D) =
    read_environment_uses (decode_finite_environment E) (fset U) (fset D)"
  by (auto simp: finite_read_environment_uses_def read_environment_uses_def binds_slot_def
      fimage.rep_eq split: prod.splits; force)

definition finite_read_environment ::
  "'u finite_artifact_environment \<Rightarrow> 'u fset \<Rightarrow> ('u \<times> local_address) fset \<Rightarrow>
    'u finite_artifact_environment" where
  "finite_read_environment E U D =
    \<lparr>finite_environment_artifacts=ffilter
       (\<lambda>entry. fst entry |\<in>| finite_read_environment_uses E U D) (finite_environment_artifacts E),
     finite_environment_bindings=ffilter (\<lambda>entry. fst entry |\<in>| D) (finite_environment_bindings E)\<rparr>"

theorem finite_read_environment_correct:
  "decode_finite_environment (finite_read_environment E U D) =
    read_environment (decode_finite_environment E) (fset U) (fset D)"
proof -
  let ?F = "decode_finite_environment (finite_read_environment E U D)"
  let ?G = "read_environment (decode_finite_environment E) (fset U) (fset D)"
  have artifacts: "environment_artifacts ?F=environment_artifacts ?G"
    by (auto simp: finite_read_environment_def read_environment_def
        finite_read_environment_uses_correct map_relation_values_def split: prod.splits)
  have bindings: "environment_bindings ?F=environment_bindings ?G"
    by (auto simp: finite_read_environment_def read_environment_def)
  show ?thesis using artifacts bindings by (cases ?F; cases ?G) simp
qed

section \<open>Actual citation records determine their requested slots\<close>

definition finite_requested_slots ::
  "'u finite_artifact_environment \<Rightarrow> ('u \<times> local_address) fset \<Rightarrow>
    ('u \<times> local_address) fset" where
  "finite_requested_slots E Q = ffUnion (fimage (\<lambda>(u,r).
    ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>(c,I).
      fimage (Pair u) (finite_citation_slots c)) (finite_citation_candidates C r)))
      (finite_artifacts_at E u))) Q)"

lemma finite_requested_slots_step:
  "(u,k) |\<in>| finite_requested_slots E Q \<longleftrightarrow>
    (\<exists>r C c I. (u,r) |\<in>| Q \<and> C |\<in>| finite_artifacts_at E u \<and>
      (c,I) |\<in>| finite_citation_candidates C r \<and> k |\<in>| finite_citation_slots c)"
  by (auto simp: finite_requested_slots_def ffUnion.rep_eq fimage.rep_eq split: prod.splits; force)

theorem finite_requested_slots_correct:
  "fset (finite_requested_slots E Q) = requested_slots (decode_finite_environment E) (fset Q)"
proof -
  have member: "(u,k) |\<in>| finite_requested_slots E Q \<longleftrightarrow>
      (u,k) \<in> requested_slots (decode_finite_environment E) (fset Q)" for u k
  proof
    assume "(u,k) |\<in>| finite_requested_slots E Q"
    then obtain r C c I where request: "(u,r) |\<in>| Q" and source: "C |\<in>| finite_artifacts_at E u"
      and citation: "(c,I) |\<in>| finite_citation_candidates C r" and slot: "k |\<in>| finite_citation_slots c"
      by (auto simp: finite_requested_slots_step)
    have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
      using source by (simp add: finite_artifacts_at_member)
    have read: "citation_at (decode_finite_object C) r c (fset I)"
      using citation by (simp add: finite_citation_candidates_correct)
    have demanded: "k \<in> citation_slots c" using slot by (simp add: finite_citation_slots_correct)
    show "(u,k) \<in> requested_slots (decode_finite_environment E) (fset Q)"
      using request art read demanded by (auto simp: requested_slots_def)
  next
    assume "(u,k) \<in> requested_slots (decode_finite_environment E) (fset Q)"
    then obtain r R c I where request: "(u,r) |\<in>| Q"
      and art: "artifact_at (decode_finite_environment E) u R"
      and read: "citation_at R r c I" and slot: "k \<in> citation_slots c"
      by (simp only: requested_slots_def mem_Collect_eq prod.case; blast)
    obtain C where source: "C |\<in>| finite_artifacts_at E u" and decoded: "decode_finite_object C=R"
      using art by (simp only: finite_artifacts_at_complete Bex_def; blast)
    have citation: "citation_at (decode_finite_object C) r c I" using read decoded by simp
    obtain J where actual: "(c,J) |\<in>| finite_citation_candidates C r"
      using finite_citation_candidates_complete[OF citation] by blast
    show "(u,k) |\<in>| finite_requested_slots E Q"
      unfolding finite_requested_slots_step
      apply (rule exI[of _ r], rule exI[of _ C], rule exI[of _ c], rule exI[of _ J])
      using request source actual slot by (simp add: finite_citation_slots_correct)
  qed
  show ?thesis using member by (auto split: prod.splits)
qed

export_code finite_environment_closed finite_read_environment finite_requested_slots checking SML

text \<open>
  Closure checks the complete supplied environment against explicit roots and
  demanded slots. Retention follows only those demands and preserves every
  supplied binding at a demanded source slot. Citation requests derive their
  slots from the actual citation records, including on incomplete inputs.
  These operations compute the existing closure and retention relations;
  the grammar that makes the requests still determines which slots are needed.
\<close>

end
