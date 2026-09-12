theory Factor_Generation_Scope_Extensions
  imports Factor_Generation_Scopes RRA_Generation_Construction
begin

section \<open>A new scope record refers to the existing predecessor presentations\<close>

theorem generation_judgment_scope_extension:
  fixes A :: "local_address option artifact_environment" and n :: nat
  assumes existing: "environment_formed A"
    and quote: "judgment_value_quoted_at C r F pu pr au ar"
    and locus: "target_formed l" and payload: "target_formed p"
    and distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at A (v i) (a i) (g i)"
  shows "\<exists>B u. environment_formed B \<and> environment_included A B \<and>
    generation_at B u [] (Generation l (Abs_fset (g ` {..<n})) p (Whole_Artifact C)) \<and>
    generation_judgment_scope_at B u [] (Generation l (Abs_fset (g ` {..<n})) p (Whole_Artifact C)) F pu pr au ar"
proof -
  have cause: "target_formed (Whole_Artifact C)"
    using judgment_value_quoted_formed[OF quote] by simp
  obtain B u where formed: "environment_formed B" and included: "environment_included A B"
    and gen: "generation_at B u [] (Generation l (Abs_fset (g ` {..<n})) p (Whole_Artifact C))"
    using generation_record_extension[OF existing locus payload cause distinct predecessors] by blast
  have scope: "generation_judgment_scope_at B u []
      (Generation l (Abs_fset (g ` {..<n})) p (Whole_Artifact C)) F pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF gen _ quote]) simp
  show ?thesis using formed included gen scope by blast
qed

text \<open>
  The record-extension constructor installs references to the supplied existing
  predecessor uses. The complete cause supplies the same quoted judgment
  scope. This shared construction has no cause role of its own: base admission
  and construction must establish their respective payload-to-judgment joins.

  The existing predecessor judgments remain prerequisites. This extension
  theorem does not replace them with metadata or infer historical permission.
\<close>

end
