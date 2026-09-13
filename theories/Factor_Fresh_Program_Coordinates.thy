theory Factor_Fresh_Program_Coordinates
  imports Factor_Program_Scopes RRA_Fresh_Uses
begin

section \<open>Extend existing definition coordinates without moving their material\<close>

theorem fresh_program_coordinates:
  fixes E :: "local_address option artifact_environment"
    and g :: "'d\<Rightarrow>local_address option definition_site"
  assumes environment: "environment_formed E" and finite: "finite V"
    and injective: "inj_on g U" and positions: "g ` U\<subseteq>environment_positions E"
  shows "\<exists>h. inj_on h V \<and> (\<forall>d\<in>U. h d=g d) \<and>
    (\<forall>d\<in>V-U. snd (h d)=[]) \<and>
    fst ` h ` (V-U)\<inter>environment_uses E={}"
proof -
  obtain f where addressing: "finite_addressing (V-U) f"
    using finite_addressing_exists[of "V-U"] finite by blast
  let ?uses="environment_uses E"
  let ?new="\<lambda>d. fresh_use_map ?uses None (Some (f d))"
  let ?h="\<lambda>d. if d\<in>U then g d else (?new d,[])"
  have finite_uses: "finite ?uses" by (rule environment_uses_finite[OF environment])
  have fresh: "?new d\<notin>?uses" for d
    using fresh_use_map_outside[OF finite_uses, of None "f d"] by simp
  have used: "fst (g d)\<in>?uses" if "d\<in>U" for d
  proof -
    have position: "g d\<in>environment_positions E" using positions that by blast
    show ?thesis using position
      by (auto simp: environment_positions_def environment_uses_def artifact_at_def rel_dom_def)
  qed
  have new_injective: "inj_on ?new (V-U)"
    using addressing by (auto simp: finite_addressing_def inj_on_def)
  have all_injective: "inj_on ?h V"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>V" and y: "y\<in>V" and eq: "?h x=?h y"
    show "x=y"
    proof (cases "x\<in>U"; cases "y\<in>U")
      assume oldx: "x\<in>U" and oldy: "y\<in>U"
      have "g x=g y" using eq oldx oldy by simp
      then show ?thesis by (rule inj_onD[OF injective _ oldx oldy])
    next
      assume oldx: "x\<in>U" and newy: "y\<notin>U"
      have "fst (g x)=?new y" using eq oldx newy by (auto dest: arg_cong[where f=fst])
      then show ?thesis using used[OF oldx] fresh[of y] by simp
    next
      assume newx: "x\<notin>U" and oldy: "y\<in>U"
      have "?new x=fst (g y)" using eq newx oldy by (auto dest: arg_cong[where f=fst])
      then show ?thesis using used[OF oldy] fresh[of x] by simp
    next
      assume newx: "x\<notin>U" and newy: "y\<notin>U"
      have same: "?new x=?new y" using eq newx newy by simp
      show ?thesis by (rule inj_onD[OF new_injective same]) (use x y newx newy in auto)
    qed
  qed
  show ?thesis by (rule exI[of _ ?h]) (use all_injective fresh in auto)
qed

text \<open>
  Every old coordinate is fixed at its actual existing position. Each new
  definition receives a distinct fresh use and an empty artifact-root address.
  The finite source environment determines the reserved boundary. The existing
  finite-address and fresh-use constructions supply all allocation choices.
\<close>

end
