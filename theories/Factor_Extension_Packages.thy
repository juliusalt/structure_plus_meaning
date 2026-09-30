theory Factor_Extension_Packages
  imports Factor_Environment_Additions Factor_Package_Membership Factor_Package_Locality
begin

section \<open>The given part of an extension is the given's\<close>

text \<open>
  An extension adds rows at uses the given does not hold and bindings sourced at those uses
  (@{const environment_additions}). So at a given use the extension holds exactly the given's artifact and
  bindings, and every use reached from a given use is a given use.
\<close>

lemma additions_parts:
  assumes "environment_additions E A B"
  shows "environment_formed E" and "rel_dom A\<inter>environment_uses E={}"
    and "\<And>z. z\<in>B \<Longrightarrow> fst (fst z)\<in>rel_dom A" and "finite A" and "finite B"
  using assms by (auto simp: environment_additions_def)

lemma extension_uses:
  "environment_uses (environment_extension E A B)=environment_uses E\<union>rel_dom A"
  by (simp add: environment_uses_def rel_dom_union)

lemma extension_given_binding:
  assumes additions: "environment_additions E A B" and given: "u\<in>environment_uses E"
  shows "binds_slot (environment_extension E A B) u k v \<longleftrightarrow> binds_slot E u k v"
proof -
  have "((u,k),v)\<notin>B"
  proof
    assume "((u,k),v)\<in>B"
    then have "u\<in>rel_dom A" using additions_parts(3)[OF additions, of "((u,k),v)"] by simp
    then show False using given additions_parts(2)[OF additions] by blast
  qed
  then show ?thesis by (auto simp: binds_slot_def)
qed

lemma extension_added_binding:
  assumes additions: "environment_additions E A B" and added: "u\<in>rel_dom A"
  shows "binds_slot (environment_extension E A B) u k v \<longleftrightarrow> ((u,k),v)\<in>B"
proof -
  have "\<not>binds_slot E u k v"
  proof
    assume "binds_slot E u k v"
    then have "u\<in>environment_uses E" by (rule environment_binding_uses(1)[OF additions_parts(1)[OF additions]])
    then show False using added additions_parts(2)[OF additions] by blast
  qed
  then show ?thesis by (auto simp: binds_slot_def)
qed

lemma extension_given_artifact:
  assumes additions: "environment_additions E A B" and given: "u\<in>environment_uses E"
  shows "artifact_at (environment_extension E A B) u R \<longleftrightarrow> artifact_at E u R"
proof -
  have "(u,R)\<notin>A"
  proof
    assume "(u,R)\<in>A"
    then have "u\<in>rel_dom A" by (rule rel_domI)
    then show False using given additions_parts(2)[OF additions] by blast
  qed
  then show ?thesis by (auto simp: artifact_at_def)
qed

lemma extension_given_reachable:
  assumes additions: "environment_additions E A B" and given: "u\<in>environment_uses E"
  shows "environment_reachable (environment_extension E A B) {u}\<subseteq>environment_uses E"
proof
  fix v assume "v\<in>environment_reachable (environment_extension E A B) {u}"
  then have path: "(u,v)\<in>(environment_edges (environment_extension E A B))\<^sup>*"
    by (simp add: environment_reachable_def)
  show "v\<in>environment_uses E" using path
  proof (induction rule: rtrancl_induct)
    case base
    show ?case by (rule given)
  next
    case (step a b)
    obtain k where "binds_slot (environment_extension E A B) a k b"
      using step.hyps(2) by (auto simp: environment_edges_def)
    then have "binds_slot E a k b" using extension_given_binding[OF additions step.IH] by blast
    then show ?case by (rule environment_binding_uses(2)[OF additions_parts(1)[OF additions]])
  qed
qed

lemma extension_given_sites:
  assumes additions: "environment_additions E A B" and given: "fst ` D\<subseteq>environment_uses E"
  shows "fst ` native_definition_sites (environment_extension E A B) D\<subseteq>environment_uses E"
proof
  fix v assume "v\<in>fst ` native_definition_sites (environment_extension E A B) D"
  then obtain d y where d: "v=fst d" and y: "y\<in>D"
    and path: "(y,d)\<in>(native_definition_edges (environment_extension E A B))\<^sup>*"
    by (auto simp: native_definition_sites_def)
  have "(fst y,fst d)\<in>(environment_edges (environment_extension E A B))\<^sup>*"
    by (rule native_definition_path_uses[OF path])
  then have reached: "fst d\<in>environment_reachable (environment_extension E A B) {fst y}"
    by (simp add: environment_reachable_def)
  have "fst y\<in>environment_uses E" using given y by blast
  then show "v\<in>environment_uses E" using extension_given_reachable[OF additions] reached d by blast
qed

text \<open>
  A given definition reads the same in the extension as in the given: its reading reads only its own use's
  artifact and bindings and their targets, and these are the given's, which the extension includes.
\<close>

theorem extension_given_definition:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and given: "v\<in>environment_uses E"
  shows "native_definition_at (environment_extension E A B) v r p C \<longleftrightarrow> native_definition_at E v r p C"
proof
  let ?F="environment_extension E A B" and ?D="rel_dom (environment_bindings E)"
  assume defn: "native_definition_at ?F v r p C"
  have ef: "environment_formed E" by (rule additions_parts(1)[OF additions])
  have sources: "fst ` ?D\<subseteq>environment_uses E"
  proof
    fix u assume "u\<in>fst ` ?D"
    then obtain k w where "binds_slot E u k w" by (auto simp: rel_dom_def binds_slot_def)
    then show "u\<in>environment_uses E" by (rule environment_binding_uses(1)[OF ef])
  qed
  have boundary: "read_boundary_formed ?F (environment_uses E) ?D"
    using ff sources by (auto simp: read_boundary_formed_def extension_uses rel_dom_def)
  have slots: "\<forall>k\<in>native_definition_slots ?F v r. (v,k)\<in>?D"
  proof
    fix k assume "k\<in>native_definition_slots ?F v r"
    then have "(v,k)\<in>rel_dom (environment_bindings ?F)" by (rule native_definition_slots_bound)
    then obtain w where "binds_slot ?F v k w" by (auto simp: rel_dom_def binds_slot_def)
    then have "binds_slot E v k w" using extension_given_binding[OF additions given] by blast
    then show "(v,k)\<in>?D" by (auto simp: rel_dom_def binds_slot_def)
  qed
  have read: "native_definition_at (read_environment ?F (environment_uses E) ?D) v r p C"
    by (rule native_definition_read_environment(1)[OF defn boundary given slots])
  have included: "environment_included (read_environment ?F (environment_uses E) ?D) E"
    by (rule read_environment_least[OF ff ef environment_extension_included]) simp_all
  show "native_definition_at E v r p C" by (rule native_definition_included[OF read included ef])
next
  assume "native_definition_at E v r p C"
  then show "native_definition_at (environment_extension E A B) v r p C"
    by (rule native_definition_included[OF _ environment_extension_included ff])
qed

theorem extension_given_formed:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and given: "fst ` D\<subseteq>environment_uses E"
  shows "native_package_formed (environment_extension E A B) D \<longleftrightarrow> native_package_formed E D"
proof
  let ?F="environment_extension E A B"
  assume formed: "native_package_formed ?F D"
  let ?U="native_definition_sites ?F D"
  have ef: "environment_formed E" by (rule additions_parts(1)[OF additions])
  have bound: "\<forall>d\<in>?U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U)"
  proof
    fix d assume member: "d\<in>?U"
    obtain p C where raw: "native_definition_at ?F (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U"
      using native_package_sites_closed_bound[OF formed] member by blast
    have "fst d\<in>environment_uses E" using extension_given_sites[OF additions given] member by blast
    then have "native_definition_at E (fst d) (snd d) p C"
      using extension_given_definition[OF additions ff] raw(1) by blast
    then show "\<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U)" using raw(2) by blast
  qed
  show "native_package_formed E D"
    unfolding native_package_finite_closed_bound
    using ef native_package_sites(2)[OF formed] native_definition_roots[of D ?F] bound by blast
next
  assume "native_package_formed E D"
  then show "native_package_formed (environment_extension E A B) D"
    using native_dependency_package_included[OF _ environment_extension_included ff] by blast
qed

text \<open>A site at a given use: the extension's package there is the given's.\<close>

theorem extension_given_package:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and given: "u\<in>environment_uses E"
  shows "native_package_at (environment_extension E A B) u r P \<longleftrightarrow> native_package_at E u r P"
proof
  let ?F="environment_extension E A B"
  assume package: "native_package_at ?F u r P"
  have ef: "environment_formed E" by (rule additions_parts(1)[OF additions])
  have boundary: "read_boundary_formed ?F (native_package_sources ?F u r) (native_package_demands ?F u r)"
    by (rule native_package_read_boundary[OF package])
  have sources: "native_package_sources ?F u r\<subseteq>environment_uses E"
    using native_package_sources_reachable[of ?F u r] extension_given_reachable[OF additions given] by blast
  have slots: "native_package_demands ?F u r\<subseteq>rel_dom (environment_bindings E)"
  proof
    fix z assume member: "z\<in>native_package_demands ?F u r"
    obtain v k where z: "z=(v,k)" by (cases z)
    have bound: "(v,k)\<in>rel_dom (environment_bindings ?F)" and source: "v\<in>native_package_sources ?F u r"
      using boundary member z by (auto simp: read_boundary_formed_def)
    obtain w where "binds_slot ?F v k w" using bound by (auto simp: rel_dom_def binds_slot_def)
    then have "binds_slot E v k w" using extension_given_binding[OF additions] source sources by blast
    then show "z\<in>rel_dom (environment_bindings E)" using z by (auto simp: rel_dom_def binds_slot_def)
  qed
  have included: "environment_included (native_package_environment ?F u r) E"
    unfolding native_package_environment_def
    by (rule read_environment_least[OF ff ef environment_extension_included sources slots])
  show "native_package_at E u r P" by (rule native_package_dependency_locality[OF package ef included])
next
  assume "native_package_at E u r P"
  then show "native_package_at (environment_extension E A B) u r P"
    by (rule native_package_included[OF _ environment_extension_included ff])
qed

section \<open>The additions' least environment\<close>

text \<open>
  The added rows, the given rows the added bindings target, and the added bindings: the extension read at the
  added uses and the added binding keys. It is formed, included in the extension, and it holds everything an
  added definition's reading reads.
\<close>

definition additions_least_environment ::
  "'u artifact_environment \<Rightarrow> ('u\<times>exact_artifact) set \<Rightarrow> (('u\<times>local_address)\<times>'u) set \<Rightarrow>
    'u artifact_environment" where
  "additions_least_environment E A B=read_environment (environment_extension E A B) (rel_dom A) (rel_dom B)"

lemma additions_read_boundary:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
  shows "read_boundary_formed (environment_extension E A B) (rel_dom A) (rel_dom B)"
proof -
  have "fst ` rel_dom B\<subseteq>rel_dom A"
  proof
    fix u assume "u\<in>fst ` rel_dom B"
    then obtain k w where "((u,k),w)\<in>B" by (auto simp: rel_dom_def)
    then show "u\<in>rel_dom A" using additions_parts(3)[OF additions, of "((u,k),w)"] by simp
  qed
  then show ?thesis using ff by (auto simp: read_boundary_formed_def extension_uses rel_dom_def)
qed

lemma additions_least_formed:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
  shows "environment_formed (additions_least_environment E A B)"
  unfolding additions_least_environment_def by (rule read_environment_formed[OF additions_read_boundary[OF additions ff]])

lemma additions_least_included:
  "environment_included (additions_least_environment E A B) (environment_extension E A B)"
  unfolding additions_least_environment_def by (rule read_environment_included)

lemma additions_least_closed:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
  shows "environment_closed (additions_least_environment E A B) (rel_dom A) (rel_dom B)"
  unfolding additions_least_environment_def by (rule read_environment_closed[OF additions_read_boundary[OF additions ff]])

text \<open>It is the least: every formed environment the extension includes, holding the added uses and binding
  keys, includes it.\<close>

lemma additions_least_least:
  assumes ff: "environment_formed (environment_extension E A B)" and formed: "environment_formed F"
    and included: "environment_included F (environment_extension E A B)"
    and uses: "rel_dom A\<subseteq>environment_uses F" and slots: "rel_dom B\<subseteq>rel_dom (environment_bindings F)"
  shows "environment_included (additions_least_environment E A B) F"
  unfolding additions_least_environment_def by (rule read_environment_least[OF ff formed included uses slots])

lemma additions_least_bindings:
  assumes additions: "environment_additions E A B"
  shows "environment_bindings (additions_least_environment E A B)=B"
proof -
  have outside: "fst z\<notin>rel_dom B" if member: "z\<in>environment_bindings E" for z
  proof
    assume "fst z\<in>rel_dom B"
    then obtain w where "(fst z,w)\<in>B" by (auto simp: rel_dom_def)
    then have added: "fst (fst z)\<in>rel_dom A" using additions_parts(3)[OF additions, of "(fst z,w)"] by simp
    obtain u k v where zz: "z=((u,k),v)" by (cases z) auto
    have "binds_slot E u k v" using member zz by (simp add: binds_slot_def)
    then have "u\<in>environment_uses E" by (rule environment_binding_uses(1)[OF additions_parts(1)[OF additions]])
    then show False using added zz additions_parts(2)[OF additions] by auto
  qed
  have own: "fst z\<in>rel_dom B" if "z\<in>B" for z using that rel_domI[of "fst z" "snd z" B] by simp
  show ?thesis using outside own by (auto simp: additions_least_environment_def read_environment_def)
qed

lemma additions_least_artifacts:
  assumes additions: "environment_additions E A B"
  shows "environment_artifacts (additions_least_environment E A B)=
    A\<union>{z\<in>environment_artifacts E. fst z\<in>snd ` B}"
proof -
  let ?F="environment_extension E A B"
  have slot: "binds_slot ?F u k v \<longleftrightarrow> ((u,k),v)\<in>B" if key: "(u,k)\<in>rel_dom B" for u k v
  proof -
    obtain w where "((u,k),w)\<in>B" using key unfolding rel_dom_def by blast
    then have "u\<in>rel_dom A" using additions_parts(3)[OF additions, of "((u,k),w)"] by simp
    then show ?thesis by (rule extension_added_binding[OF additions])
  qed
  have targets: "read_environment_uses ?F (rel_dom A) (rel_dom B)=rel_dom A\<union>snd ` B"
  proof
    show "read_environment_uses ?F (rel_dom A) (rel_dom B)\<subseteq>rel_dom A\<union>snd ` B"
    proof
      fix v assume "v\<in>read_environment_uses ?F (rel_dom A) (rel_dom B)"
      then consider "v\<in>rel_dom A" | u k where "(u,k)\<in>rel_dom B" "binds_slot ?F u k v"
        by (auto simp: read_environment_uses_def)
      then show "v\<in>rel_dom A\<union>snd ` B"
      proof cases
        case 1
        then show ?thesis by simp
      next
        case (2 u k)
        have "((u,k),v)\<in>B" using slot[OF 2(1)] 2(2) by blast
        then show ?thesis using image_eqI[of v snd "((u,k),v)" B] by simp
      qed
    qed
    show "rel_dom A\<union>snd ` B\<subseteq>read_environment_uses ?F (rel_dom A) (rel_dom B)"
    proof
      fix v assume "v\<in>rel_dom A\<union>snd ` B"
      then consider "v\<in>rel_dom A" | y where "y\<in>B" "v=snd y" by blast
      then show "v\<in>read_environment_uses ?F (rel_dom A) (rel_dom B)"
      proof cases
        case 1
        then show ?thesis by (simp add: read_environment_uses_def)
      next
        case (2 y)
        obtain u k where y: "y=((u,k),v)" using 2 by (cases y) auto
        have row: "((u,k),v)\<in>B" using 2(1) y by simp
        have key: "(u,k)\<in>rel_dom B" by (rule rel_domI[OF row])
        have "binds_slot ?F u k v" using slot[OF key] row by blast
        then show ?thesis using key by (auto simp: read_environment_uses_def)
      qed
    qed
  qed
  have fresh: "fst z\<notin>rel_dom A" if "z\<in>environment_artifacts E" for z
  proof -
    have "fst z\<in>environment_uses E"
      using that rel_domI[of "fst z" "snd z" "environment_artifacts E"] by (simp add: environment_uses_def)
    then show ?thesis using additions_parts(2)[OF additions] by blast
  qed
  have own: "fst z\<in>rel_dom A" if "z\<in>A" for z using that rel_domI[of "fst z" "snd z" A] by simp
  show ?thesis using fresh own
    by (auto simp: additions_least_environment_def read_environment_def targets)
qed

text \<open>An added definition, and the root family at an added site, read the same in the extension and in the least
  environment.\<close>

theorem extension_added_definition:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and added: "v\<in>rel_dom A"
  shows "native_definition_at (environment_extension E A B) v r p C \<longleftrightarrow>
    native_definition_at (additions_least_environment E A B) v r p C"
proof
  let ?F="environment_extension E A B"
  assume defn: "native_definition_at ?F v r p C"
  have slots: "\<forall>k\<in>native_definition_slots ?F v r. (v,k)\<in>rel_dom B"
  proof
    fix k assume "k\<in>native_definition_slots ?F v r"
    then have "(v,k)\<in>rel_dom (environment_bindings ?F)" by (rule native_definition_slots_bound)
    then obtain w where "binds_slot ?F v k w" by (auto simp: rel_dom_def binds_slot_def)
    then have "((v,k),w)\<in>B" using extension_added_binding[OF additions added] by blast
    then show "(v,k)\<in>rel_dom B" by (rule rel_domI)
  qed
  show "native_definition_at (additions_least_environment E A B) v r p C"
    unfolding additions_least_environment_def
    by (rule native_definition_read_environment(1)[OF defn additions_read_boundary[OF additions ff] added slots])
next
  assume "native_definition_at (additions_least_environment E A B) v r p C"
  then show "native_definition_at (environment_extension E A B) v r p C"
    by (rule native_definition_included[OF _ additions_least_included ff])
qed

theorem extension_added_root_family:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and added: "u\<in>rel_dom A"
  shows "native_root_family_at (environment_extension E A B) u r Q \<longleftrightarrow>
    native_root_family_at (additions_least_environment E A B) u r Q"
proof
  let ?F="environment_extension E A B"
  assume family: "native_root_family_at ?F u r Q"
  have requests: "requested_slots ?F ({u}\<times>family_endpoints ?F u r)\<subseteq>rel_dom (environment_bindings ?F)"
    using requested_slots_subset[OF native_root_requests_formed[OF family]] by (simp add: native_root_requests_def)
  have slots: "requested_slots ?F ({u}\<times>family_endpoints ?F u r)\<subseteq>rel_dom B"
  proof
    fix z assume member: "z\<in>requested_slots ?F ({u}\<times>family_endpoints ?F u r)"
    obtain v k where z: "z=(v,k)" by (cases z)
    have member': "(v,k)\<in>requested_slots ?F ({u}\<times>family_endpoints ?F u r)" using member z by simp
    have "v\<in>fst ` ({u}\<times>family_endpoints ?F u r)" by (rule requested_slot_source[OF member'])
    then have source: "v=u" by (auto split: if_split_asm)
    have "(v,k)\<in>rel_dom (environment_bindings ?F)" using requests member' by (rule subsetD)
    then obtain w where "binds_slot ?F v k w" by (auto simp: rel_dom_def binds_slot_def)
    then have "((v,k),w)\<in>B" using extension_added_binding[OF additions added] source by blast
    then show "z\<in>rel_dom B" using z by (auto intro: rel_domI)
  qed
  show "native_root_family_at (additions_least_environment E A B) u r Q"
    unfolding additions_least_environment_def
    by (rule native_root_family_read_environment[OF family additions_read_boundary[OF additions ff] added slots])
next
  assume "native_root_family_at (additions_least_environment E A B) u r Q"
  then show "native_root_family_at (environment_extension E A B) u r Q"
    by (rule native_root_family_included[OF _ additions_least_included ff])
qed

section \<open>The closure bounded by the given's uses\<close>

text \<open>
  A bounded closure is a finite set of definitions covering the roots together with a boundary, each member's
  callees in the set or on the boundary. With an empty boundary it is the closed bound of a formed package
  (@{thm [source] native_package_finite_closed_bound}).
\<close>

definition bounded_package_formed ::
  "'u artifact_environment \<Rightarrow> 'u definition_site set \<Rightarrow> 'u definition_site set \<Rightarrow> bool" where
  "bounded_package_formed E roots Y \<longleftrightarrow> environment_formed E \<and> (\<exists>U. finite U \<and> roots\<subseteq>U\<union>Y \<and>
    (\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y)))"

lemma bounded_package_formed_empty:
  "bounded_package_formed E roots {} \<longleftrightarrow> native_package_formed E roots"
  by (simp add: bounded_package_formed_def native_package_finite_closed_bound)

lemma native_definition_sites_member:
  assumes "y\<in>native_definition_sites E R"
  shows "native_definition_sites E {y}\<subseteq>native_definition_sites E R"
  by (rule native_definition_sites_least) (auto intro: assms native_definition_step)

lemma native_definition_sites_self: "y\<in>native_definition_sites E {y}"
  using native_definition_roots[of "{y}" E] by blast

definition bounded_closure_formed ::
  "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow> 'u definition_site set \<Rightarrow> bool" where
  "bounded_closure_formed L E roots \<longleftrightarrow>
    (\<exists>Y. finite Y \<and> bounded_package_formed L roots Y \<and> (\<forall>y\<in>Y. native_package_formed E {y}))"

text \<open>
  A bounded closure read in an environment the extension includes, its boundary's packages formed in the given,
  gives the package in the extension: the bound's definitions and each boundary site's package are read there.
\<close>

theorem bounded_closure_package:
  assumes least: "environment_included L F" and given: "environment_included E F" and ff: "environment_formed F"
    and family: "native_root_family_at L u r Q" and bounded: "bounded_closure_formed L E (rel_ran Q)"
  shows "\<exists>P. native_package_at F u r P"
proof -
  obtain Y where finY: "finite Y" and bpf: "bounded_package_formed L (rel_ran Q) Y"
    and givenY: "\<forall>y\<in>Y. native_package_formed E {y}"
    using bounded by (auto simp: bounded_closure_formed_def)
  obtain U where finU: "finite U" and roots: "rel_ran Q\<subseteq>U\<union>Y"
    and defined: "\<forall>d\<in>U. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y)"
    using bpf by (auto simp: bounded_package_formed_def)
  have gformed: "native_package_formed F {y}" if "y\<in>Y" for y
    using givenY that native_dependency_package_included[OF _ given ff] by blast
  let ?V="U\<union>(\<Union>y\<in>Y. native_definition_sites F {y})"
  have boundary: "Y\<subseteq>?V" using native_definition_sites_self by blast
  have "native_package_formed F (rel_ran Q)"
    unfolding native_package_finite_closed_bound
  proof (intro conjI exI[of _ ?V])
    show "environment_formed F" by (rule ff)
    show "finite ?V" using finU finY native_package_sites(2)[OF gformed] by auto
    show "rel_ran Q\<subseteq>?V" using roots boundary by blast
    show "\<forall>d\<in>?V. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?V)"
    proof
      fix d assume "d\<in>?V"
      then consider (added) "d\<in>U" | (boundary_site) y where "y\<in>Y" "d\<in>native_definition_sites F {y}" by blast
      then show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?V)"
      proof cases
        case added
        obtain p C where raw: "native_definition_at L (fst d) (snd d) p C"
          "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y" using defined added by blast
        have "native_definition_at F (fst d) (snd d) p C" by (rule native_definition_included[OF raw(1) least ff])
        then show ?thesis using raw(2) boundary by blast
      next
        case (boundary_site y)
        obtain p C where raw: "native_definition_at F (fst d) (snd d) p C"
          "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>native_definition_sites F {y}"
          using native_package_sites_closed_bound[OF gformed[OF boundary_site(1)]] boundary_site(2) by blast
        then show ?thesis using boundary_site(1) by blast
      qed
    qed
  qed
  moreover have "native_root_family_at F u r Q" by (rule native_root_family_included[OF family least ff])
  ultimately show ?thesis unfolding native_package_at_def by blast
qed



section \<open>The package at a site of an extension\<close>

text \<open>
  At an added site the package exists exactly when the root family read in the least environment has a bounded
  closure there whose boundary is formed in the given, each boundary site's package formed there.
\<close>

theorem extension_added_package:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and added: "u\<in>rel_dom A"
  shows "(\<exists>P. native_package_at (environment_extension E A B) u r P) \<longleftrightarrow>
    (\<exists>Q. native_root_family_at (additions_least_environment E A B) u r Q \<and>
      bounded_closure_formed (additions_least_environment E A B) E (rel_ran Q))"
proof
  let ?F="environment_extension E A B" and ?L="additions_least_environment E A B"
  assume "\<exists>P. native_package_at ?F u r P"
  then obtain Q where family: "native_root_family_at ?F u r Q" and formed: "native_package_formed ?F (rel_ran Q)"
    by (auto simp: native_package_at_def)
  let ?S="native_definition_sites ?F (rel_ran Q)"
  let ?U="{d\<in>?S. fst d\<in>rel_dom A}" and ?Y="{d\<in>?S. fst d\<in>environment_uses E}"
  have finite: "finite ?S" by (rule native_package_sites(2)[OF formed])
  have split: "?S\<subseteq>?U\<union>?Y"
  proof
    fix d assume member: "d\<in>?S"
    obtain p C where "native_definition_at ?F (fst d) (snd d) p C"
      using formed member by (auto simp: native_package_formed_def)
    then obtain R where "artifact_at ?F (fst d) R" by (auto simp: native_definition_at_def)
    then have "fst d\<in>environment_uses ?F"
      using rel_domI[of "fst d" R] by (simp add: environment_uses_def artifact_at_def)
    then show "d\<in>?U\<union>?Y" using member by (auto simp: extension_uses)
  qed
  have lfamily: "native_root_family_at ?L u r Q"
    using extension_added_root_family[OF additions ff added] family by blast
  have bounded: "bounded_package_formed ?L (rel_ran Q) ?Y"
    unfolding bounded_package_formed_def
  proof (intro conjI exI[of _ ?U])
    show "environment_formed ?L" by (rule additions_least_formed[OF additions ff])
    show "finite ?U" by (rule finite_subset[OF _ finite]) auto
    show "rel_ran Q\<subseteq>?U\<union>?Y" using native_definition_roots[of "rel_ran Q" ?F] split by blast
    show "\<forall>d\<in>?U. \<exists>p C. native_definition_at ?L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U\<union>?Y)"
    proof
      fix d assume member: "d\<in>?U"
      obtain p C where raw: "native_definition_at ?F (fst d) (snd d) p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S"
        using native_package_sites_closed_bound[OF formed] member by blast
      have "native_definition_at ?L (fst d) (snd d) p C"
        using extension_added_definition[OF additions ff] raw(1) member by blast
      then show "\<exists>p C. native_definition_at ?L (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U\<union>?Y)" using raw(2) split by blast
    qed
  qed
  have given: "\<forall>y\<in>?Y. native_package_formed E {y}"
  proof
    fix y assume member: "y\<in>?Y"
    have sub: "native_definition_sites ?F {y}\<subseteq>?S" by (rule native_definition_sites_member) (use member in simp)
    have "native_package_formed ?F {y}" using formed sub ff by (auto simp: native_package_formed_def)
    then show "native_package_formed E {y}" using extension_given_formed[OF additions ff, of "{y}"] member by auto
  qed
  have "finite ?Y" by (rule finite_subset[OF _ finite]) auto
  then show "\<exists>Q. native_root_family_at ?L u r Q \<and> bounded_closure_formed ?L E (rel_ran Q)"
    using lfamily bounded given unfolding bounded_closure_formed_def by blast
next
  let ?F="environment_extension E A B" and ?L="additions_least_environment E A B"
  assume "\<exists>Q. native_root_family_at ?L u r Q \<and> bounded_closure_formed ?L E (rel_ran Q)"
  then obtain Q where lfamily: "native_root_family_at ?L u r Q" and bounded: "bounded_closure_formed ?L E (rel_ran Q)"
    by blast
  show "\<exists>P. native_package_at ?F u r P"
    by (rule bounded_closure_package[OF additions_least_included environment_extension_included ff lfamily bounded])
qed

text \<open>
  The members of the package at a site of the extension: its added members, and for each given member the
  given's package at it, whose members the extension's package holds unchanged.
\<close>

theorem extension_package_members:
  assumes additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and package: "native_package_at (environment_extension E A B) u r P"
  shows "system_definitions P={d\<in>system_definitions P. fst d\<in>rel_dom A}\<union>
    (\<Union>y\<in>{d\<in>system_definitions P. fst d\<in>environment_uses E}. native_definition_sites E {y})"
proof -
  let ?F="environment_extension E A B" and ?R="native_package_roots (environment_extension E A B) u r"
  have S: "system_definitions P=native_definition_sites ?F ?R"
    using native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  have formed: "native_package_formed ?F ?R" by (rule native_package_projection(1)[OF package])
  have same: "native_definition_sites E {y}=native_definition_sites ?F {y}"
    if member: "y\<in>system_definitions P" and given: "fst y\<in>environment_uses E" for y
  proof -
    have sub: "native_definition_sites ?F {y}\<subseteq>native_definition_sites ?F ?R"
      by (rule native_definition_sites_member) (use member S in simp)
    have fformed: "native_package_formed ?F {y}" using formed sub ff by (auto simp: native_package_formed_def)
    have eformed: "native_package_formed E {y}"
      using extension_given_formed[OF additions ff, of "{y}"] fformed given by auto
    have "native_program ?F {y}=native_program E {y}"
      using native_dependency_package_included[OF eformed environment_extension_included ff] by blast
    then show ?thesis using native_program_definitions[OF fformed] native_program_definitions[OF eformed] by simp
  qed
  show ?thesis
  proof
    show "system_definitions P\<subseteq>{d\<in>system_definitions P. fst d\<in>rel_dom A}\<union>
      (\<Union>y\<in>{d\<in>system_definitions P. fst d\<in>environment_uses E}. native_definition_sites E {y})"
    proof
      fix d assume member: "d\<in>system_definitions P"
      have "fst d\<in>environment_uses ?F" by (rule native_package_member_use[OF package member])
      then consider "fst d\<in>rel_dom A" | "fst d\<in>environment_uses E" by (auto simp: extension_uses)
      then show "d\<in>{d\<in>system_definitions P. fst d\<in>rel_dom A}\<union>
        (\<Union>y\<in>{d\<in>system_definitions P. fst d\<in>environment_uses E}. native_definition_sites E {y})"
        using member native_definition_sites_self[of d E] by cases blast+
    qed
    show "{d\<in>system_definitions P. fst d\<in>rel_dom A}\<union>
      (\<Union>y\<in>{d\<in>system_definitions P. fst d\<in>environment_uses E}. native_definition_sites E {y})\<subseteq>system_definitions P"
    proof
      fix d assume "d\<in>{d\<in>system_definitions P. fst d\<in>rel_dom A}\<union>
        (\<Union>y\<in>{d\<in>system_definitions P. fst d\<in>environment_uses E}. native_definition_sites E {y})"
      then consider "d\<in>system_definitions P" | y where "y\<in>system_definitions P" "fst y\<in>environment_uses E"
        "d\<in>native_definition_sites E {y}" by blast
      then show "d\<in>system_definitions P"
      proof cases
        case 1
        then show ?thesis .
      next
        case (2 y)
        have "d\<in>native_definition_sites ?F {y}" using same[OF 2(1,2)] 2(3) by simp
        moreover have "native_definition_sites ?F {y}\<subseteq>native_definition_sites ?F ?R"
          by (rule native_definition_sites_member) (use 2(1) S in simp)
        ultimately show ?thesis using S by blast
      qed
    qed
  qed
qed

section \<open>The native readers of the package at a site of an extension\<close>

text \<open>
  Seven ordinary definitions, at 955 to 961 above every numbered site of the library and views over package
  membership (83), read G2 at the pair of the given's site value and the additions. 955 and 956 check a
  proposed least environment's rows: each is an added row (47 over the added rows) or a row of the given (37 at
  the given's value). 957 admits the proposed least environment (26), its rows so checked and its bindings the
  added ones. 958 and 959 check a bounded closure's members: an added definition read in the least environment
  with its callees in the bound (76), or a given site, a member of the given's package (83 at the given's site)
  or a site whose closure is formed in the given (77 at the given's value). 960 checks the bound: the roots in it
  (47) and every member checked. 961 is G2: at an added site the root family read in the least environment (79)
  and its bounded closure; at a given site package admission at the given's value (80). The least environment and
  the bound are premise-only: handed in, never produced by these clauses.
\<close>

definition extension_row_added_schema :: "(nat,nat,nat) factor_schema" where
  "extension_row_added_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,47,Pattern_Pair (Pattern_Pair data_z (Pattern_Payload [])) data_y)}"

definition extension_row_given_schema :: "(nat,nat,nat) factor_schema" where
  "extension_row_given_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,37,Pattern_Pair data_x data_z)}"

definition extension_row_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "extension_row_clauses={(0,extension_row_added_schema),(1,extension_row_given_schema)}"

definition least_environment_schema :: "(nat,nat,nat) factor_schema" where
  "least_environment_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Pair data_w data_z))
    {(0,26,Pattern_Pair data_w data_z),(1,956,Pattern_Pair (Pattern_Pair data_x data_y) data_w)}"

abbreviation bounded_member_pattern :: "nat term_pattern" where
  "bounded_member_pattern \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair data_x (source_root_pattern data_y data_z data_w))
    (Pattern_Variable 4)) (Pattern_Variable 5)"

definition bounded_member_added_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_added_schema=data_rule bounded_member_pattern
    {(0,76,Pattern_Pair (Pattern_Pair data_x (Pattern_Variable 4)) (Pattern_Pair (Pattern_Variable 5) (Pattern_Payload [])))}"

definition bounded_member_package_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_package_schema=data_rule bounded_member_pattern
    {(0,83,Pattern_Pair (source_root_pattern data_y data_z data_w) (Pattern_Variable 5))}"

definition bounded_member_closure_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_closure_schema=data_rule bounded_member_pattern
    {(0,77,Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 5) (Pattern_Payload [])))}"

definition bounded_member_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "bounded_member_clauses={(0,bounded_member_added_schema),(1,bounded_member_package_schema),
    (2,bounded_member_closure_schema)}"

definition bounded_closure_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_closure_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,26,data_x),(1,47,Pattern_Pair data_z data_w),
     (2,959,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_w) data_w)}"

abbreviation extension_package_pattern :: "nat term_pattern" where
  "extension_package_pattern \<equiv> Pattern_Pair (source_root_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6))
    (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4)))"

definition extension_added_site_schema :: "(nat,nat,nat) factor_schema" where
  "extension_added_site_schema=data_rule extension_package_pattern
    {(0,957,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Variable 7)),
     (1,79,citation_observation_pattern (Pattern_Variable 7) data_w (Pattern_Variable 4) (Pattern_Variable 8)),
     (2,960,Pattern_Pair (Pattern_Pair (Pattern_Variable 7)
       (source_root_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6))) (Pattern_Variable 8))}"

definition extension_given_site_schema :: "(nat,nat,nat) factor_schema" where
  "extension_given_site_schema=data_rule extension_package_pattern
    {(0,80,source_root_pattern data_x data_w (Pattern_Variable 4))}"

definition extension_package_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "extension_package_clauses={(0,extension_added_site_schema),(1,extension_given_site_schema)}"

definition extension_row_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_row_system=add_view_definition package_membership_system 955 data_x extension_row_clauses"

definition extension_rows_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_rows_system=add_view_definition extension_row_system 956 data_x (context_list_clauses 955 956)"

definition least_environment_system :: "(nat,nat,nat,nat) schema_system" where
  "least_environment_system=add_view_definition extension_rows_system 957 data_x {(0,least_environment_schema)}"

definition bounded_member_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_member_system=add_view_definition least_environment_system 958 data_x bounded_member_clauses"

definition bounded_members_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_members_system=add_view_definition bounded_member_system 959 data_x (context_list_clauses 958 959)"

definition bounded_closure_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_closure_system=add_view_definition bounded_members_system 960 data_x {(0,bounded_closure_schema)}"

definition extension_package_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_package_system=add_view_definition bounded_closure_system 961 data_x extension_package_clauses"

lemmas extension_package_schema_defs = extension_row_clauses_def extension_row_added_schema_def
  extension_row_given_schema_def least_environment_schema_def bounded_member_clauses_def
  bounded_member_added_schema_def bounded_member_package_schema_def bounded_member_closure_schema_def
  bounded_closure_schema_def extension_package_clauses_def extension_added_site_schema_def
  extension_given_site_schema_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def

lemma extension_row_system_formed [simp]: "schema_system_formed extension_row_system"
  unfolding extension_row_system_def
  by (rule add_recursive_definition_formed[OF package_membership_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_row_definitions [simp]:
  "system_definitions extension_row_system=insert 955 (system_definitions package_membership_system)"
  by (simp add: extension_row_system_def)

lemma extension_rows_system_formed [simp]: "schema_system_formed extension_rows_system"
  unfolding extension_rows_system_def
  by (rule add_recursive_definition_formed[OF extension_row_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_rows_definitions [simp]:
  "system_definitions extension_rows_system=insert 956 (system_definitions extension_row_system)"
  by (simp add: extension_rows_system_def)

lemma least_environment_system_formed [simp]: "schema_system_formed least_environment_system"
  unfolding least_environment_system_def
  by (rule add_recursive_definition_formed[OF extension_rows_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma least_environment_definitions [simp]:
  "system_definitions least_environment_system=insert 957 (system_definitions extension_rows_system)"
  by (simp add: least_environment_system_def)

lemma bounded_member_system_formed [simp]: "schema_system_formed bounded_member_system"
  unfolding bounded_member_system_def
  by (rule add_recursive_definition_formed[OF least_environment_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma bounded_member_definitions [simp]:
  "system_definitions bounded_member_system=insert 958 (system_definitions least_environment_system)"
  by (simp add: bounded_member_system_def)

lemma bounded_members_system_formed [simp]: "schema_system_formed bounded_members_system"
  unfolding bounded_members_system_def
  by (rule add_recursive_definition_formed[OF bounded_member_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma bounded_members_definitions [simp]:
  "system_definitions bounded_members_system=insert 959 (system_definitions bounded_member_system)"
  by (simp add: bounded_members_system_def)

lemma bounded_closure_system_formed [simp]: "schema_system_formed bounded_closure_system"
  unfolding bounded_closure_system_def
  by (rule add_recursive_definition_formed[OF bounded_members_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma bounded_closure_definitions [simp]:
  "system_definitions bounded_closure_system=insert 960 (system_definitions bounded_members_system)"
  by (simp add: bounded_closure_system_def)

lemma extension_package_system_formed [simp]: "schema_system_formed extension_package_system"
  unfolding extension_package_system_def
  by (rule add_recursive_definition_formed[OF bounded_closure_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_package_definitions [simp]:
  "system_definitions extension_package_system=insert 961 (system_definitions bounded_closure_system)"
  by (simp add: extension_package_system_def)

lemma extension_row_call:
  "schema_call_formed extension_row_system d t \<longleftrightarrow> d\<in>system_definitions extension_row_system \<and> term_formed t"
  using added_variable_calls[OF package_membership_system_formed
    extension_row_system_formed[unfolded extension_row_system_def] package_membership_call]
  by (simp only: extension_row_system_def[symmetric])

lemma extension_rows_call:
  "schema_call_formed extension_rows_system d t \<longleftrightarrow> d\<in>system_definitions extension_rows_system \<and> term_formed t"
  using added_variable_calls[OF extension_row_system_formed
    extension_rows_system_formed[unfolded extension_rows_system_def] extension_row_call]
  by (simp only: extension_rows_system_def[symmetric])

lemma least_environment_call:
  "schema_call_formed least_environment_system d t \<longleftrightarrow> d\<in>system_definitions least_environment_system \<and> term_formed t"
  using added_variable_calls[OF extension_rows_system_formed
    least_environment_system_formed[unfolded least_environment_system_def] extension_rows_call]
  by (simp only: least_environment_system_def[symmetric])

lemma bounded_member_call:
  "schema_call_formed bounded_member_system d t \<longleftrightarrow> d\<in>system_definitions bounded_member_system \<and> term_formed t"
  using added_variable_calls[OF least_environment_system_formed
    bounded_member_system_formed[unfolded bounded_member_system_def] least_environment_call]
  by (simp only: bounded_member_system_def[symmetric])

lemma bounded_members_call:
  "schema_call_formed bounded_members_system d t \<longleftrightarrow> d\<in>system_definitions bounded_members_system \<and> term_formed t"
  using added_variable_calls[OF bounded_member_system_formed
    bounded_members_system_formed[unfolded bounded_members_system_def] bounded_member_call]
  by (simp only: bounded_members_system_def[symmetric])

lemma bounded_closure_call:
  "schema_call_formed bounded_closure_system d t \<longleftrightarrow> d\<in>system_definitions bounded_closure_system \<and> term_formed t"
  using added_variable_calls[OF bounded_members_system_formed
    bounded_closure_system_formed[unfolded bounded_closure_system_def] bounded_members_call]
  by (simp only: bounded_closure_system_def[symmetric])

lemma extension_package_call:
  "schema_call_formed extension_package_system d t \<longleftrightarrow> d\<in>system_definitions extension_package_system \<and> term_formed t"
  using added_variable_calls[OF bounded_closure_system_formed
    extension_package_system_formed[unfolded extension_package_system_def] bounded_closure_call]
  by (simp only: extension_package_system_def[symmetric])

lemma extension_package_old_meaning:
  assumes old: "d\<in>system_definitions package_membership_system"
  shows "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
proof -
  have step1: "(d,t)\<in>positive_meaning extension_row_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
    using added_definition_preserves_old(2)[OF package_membership_system_formed
      extension_row_system_formed[unfolded extension_row_system_def], of d t] old
    by (auto simp: extension_row_system_def)
  have step2: "(d,t)\<in>positive_meaning extension_rows_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_row_system"
    using added_definition_preserves_old(2)[OF extension_row_system_formed
      extension_rows_system_formed[unfolded extension_rows_system_def], of d t] old
    by (auto simp: extension_rows_system_def)
  have step3: "(d,t)\<in>positive_meaning least_environment_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_rows_system"
    using added_definition_preserves_old(2)[OF extension_rows_system_formed
      least_environment_system_formed[unfolded least_environment_system_def], of d t] old
    by (auto simp: least_environment_system_def)
  have step4: "(d,t)\<in>positive_meaning bounded_member_system \<longleftrightarrow> (d,t)\<in>positive_meaning least_environment_system"
    using added_definition_preserves_old(2)[OF least_environment_system_formed
      bounded_member_system_formed[unfolded bounded_member_system_def], of d t] old
    by (auto simp: bounded_member_system_def)
  have step5: "(d,t)\<in>positive_meaning bounded_members_system \<longleftrightarrow> (d,t)\<in>positive_meaning bounded_member_system"
    using added_definition_preserves_old(2)[OF bounded_member_system_formed
      bounded_members_system_formed[unfolded bounded_members_system_def], of d t] old
    by (auto simp: bounded_members_system_def)
  have step6: "(d,t)\<in>positive_meaning bounded_closure_system \<longleftrightarrow> (d,t)\<in>positive_meaning bounded_members_system"
    using added_definition_preserves_old(2)[OF bounded_members_system_formed
      bounded_closure_system_formed[unfolded bounded_closure_system_def], of d t] old
    by (auto simp: bounded_closure_system_def)
  have step7: "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning bounded_closure_system"
    using added_definition_preserves_old(2)[OF bounded_closure_system_formed
      extension_package_system_formed[unfolded extension_package_system_def], of d t] old
    by (auto simp: extension_package_system_def)
  show ?thesis using step1 step2 step3 step4 step5 step6 step7 by simp
qed

lemma extension_package_components:
  "(26,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
  "(37,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(47,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(77,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (77,t)\<in>positive_meaning package_closure_admission_system"
  "(79,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(80,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(83,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
proof -
  have pm: "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
    if "d\<in>{26,37,47,76,77,79,80,83}" for d using that by (intro extension_package_old_meaning) auto
  have pa: "(d,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_admission_system"
    if "d\<in>{26,37,47,76,77}" for d using that by (intro package_membership_previous_meaning) auto
  have closure: "(d,t)\<in>positive_meaning package_admission_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning package_closure_admission_system"
    if "d\<in>{26,47,76}" for d using that by (intro package_admission_previous_meaning) auto
  have lookup: "(37,t)\<in>positive_meaning package_admission_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
    using package_admission_old_meaning[of 37 t] root_family_reading_components(1)[of t] by simp
  show "(26,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
    "(37,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
    "(47,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    "(76,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    "(77,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (77,t)\<in>positive_meaning package_closure_admission_system"
    "(79,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
    "(80,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
    "(83,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
    using pm[of 26] pm[of 37] pm[of 47] pm[of 76] pm[of 77] pm[of 79] pm[of 80] pm[of 83]
      pa[of 26] pa[of 37] pa[of 47] pa[of 76] pa[of 77] closure[of 26] closure[of 47] closure[of 76] lookup
      package_closure_admission_components[of t] package_admission_components[of t]
      package_membership_components(1,2)[of t] by simp_all
qed

lemma extension_package_families:
  "((955,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_row_clauses"
  "((956,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 955 956"
  "((957,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=least_environment_schema"
  "((958,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>bounded_member_clauses"
  "((959,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 958 959"
  "((960,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=bounded_closure_schema"
  "((961,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_package_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_membership_system \<Longrightarrow> d\<in>system_definitions package_membership_system"
    for d c S using package_membership_system_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses package_membership_system" if "d\<in>{955,956,957,958,959,960,961}" for d c S
    using that by (auto dest: owned)
  show "((955,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_row_clauses"
    "((956,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 955 956"
    "((957,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=least_environment_schema"
    "((958,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>bounded_member_clauses"
    "((959,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 958 959"
    "((960,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=bounded_closure_schema"
    "((961,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_package_clauses"
    using absent by (auto simp: extension_package_system_def bounded_closure_system_def bounded_members_system_def
      bounded_member_system_def least_environment_system_def extension_rows_system_def extension_row_system_def)
qed

interpretation extension_rows_lists: context_list_profile extension_package_system 955 956
  by (rule context_list_profile.intro) (auto simp: extension_package_call extension_package_families)

interpretation bounded_members_lists: context_list_profile extension_package_system 958 959
  by (rule context_list_profile.intro) (auto simp: extension_package_call extension_package_families)

lemma extension_package_valuation:
  assumes "(d,t)\<in>positive_meaning extension_package_system"
  shows "\<exists>c S f. ((d,c),S)\<in>system_clauses extension_package_system \<and> (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system)"
  using schema_consequences_valuationD[of d t extension_package_system "positive_meaning extension_package_system"]
    assms positive_meaning_unfold[of extension_package_system] by blast

subsection \<open>The raw readings of the new clauses\<close>

lemma extension_row_raw:
  "(955,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g a x. t=Pair_Term (Pair_Term g a) x \<and>
    term_formed g \<and> term_formed a \<and> term_formed x \<and>
    ((47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system \<or>
     (37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((955,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>extension_row_clauses" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> t=Pair_Term (Pair_Term (f 0) (f 1)) (f 2) \<and>
    ((47,Pair_Term (Pair_Term (f 2) (Payload_Term [])) (f 1))\<in>positive_meaning data_subset_system \<or>
     (37,Pair_Term (f 0) (f 2))\<in>positive_meaning artifact_lookup_system)"
    using family vars conclusion support
    by (auto simp: extension_package_schema_defs schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g a x where t: "t=Pair_Term (Pair_Term g a) x" and formed: "term_formed g" "term_formed a" "term_formed x"
    and calls: "(47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system \<or>
      (37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else x"
  from calls show ?lhs
  proof
    assume sub: "(47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system"
    have "(955,evaluate_pattern ?f (schema_conclusion extension_row_added_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed sub in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t extension_row_added_schema_def)
  next
    assume lookup: "(37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system"
    have "(955,evaluate_pattern ?f (schema_conclusion extension_row_given_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed lookup in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t extension_row_given_schema_def)
  qed
qed

lemma least_environment_raw:
  "(957,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g a b w. t=Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term w b) \<and>
    term_formed g \<and> term_formed a \<and> term_formed b \<and> term_formed w \<and>
    (\<exists>L. environment_value_presents L (Pair_Term w b)) \<and>
    (956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((957,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have schema: "S=least_environment_schema" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and>
    t=Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) (Pair_Term (f 3) (f 2)) \<and>
    (\<exists>L. environment_value_presents L (Pair_Term (f 3) (f 2))) \<and>
    (956,Pair_Term (Pair_Term (f 0) (f 1)) (f 3))\<in>positive_meaning extension_package_system"
    using vars conclusion support
    by (auto simp: schema least_environment_schema_def schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g a b w where t: "t=Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term w b)"
    and formed: "term_formed g" "term_formed a" "term_formed b" "term_formed w"
    and admitted: "\<exists>L. environment_value_presents L (Pair_Term w b)"
    and rows: "(956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else w"
  have "(957,evaluate_pattern ?f (schema_conclusion least_environment_schema))\<in>positive_meaning extension_package_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed admitted rows in \<open>auto simp: extension_package_families least_environment_schema_def
        schema_variables_def extension_package_call extension_package_components\<close>)
  then show ?lhs by (simp add: t least_environment_schema_def)
qed

lemma bounded_member_raw:
  "(958,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>l g gu gr k x.
    t=Pair_Term (Pair_Term (Pair_Term l (source_root_argument g gu gr)) k) x \<and>
    term_formed l \<and> term_formed g \<and> term_formed gu \<and> term_formed gr \<and> term_formed k \<and> term_formed x \<and>
    ((76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
     (83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
     (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((958,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>bounded_member_clauses" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
    term_formed (f 5) \<and> t=Pair_Term (Pair_Term (Pair_Term (f 0) (source_root_argument (f 1) (f 2) (f 3))) (f 4)) (f 5) \<and>
    ((76,Pair_Term (Pair_Term (f 0) (f 4)) (Pair_Term (f 5) (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
     (83,package_subject_argument (f 1) (f 2) (f 3) (f 5))\<in>positive_meaning package_membership_system \<or>
     (77,Pair_Term (f 1) (Pair_Term (f 5) (Payload_Term [])))\<in>positive_meaning package_closure_admission_system)"
    using family vars conclusion support
    by (auto simp: extension_package_schema_defs schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain l g gu gr k x where t: "t=Pair_Term (Pair_Term (Pair_Term l (source_root_argument g gu gr)) k) x"
    and formed: "term_formed l" "term_formed g" "term_formed gu" "term_formed gr" "term_formed k" "term_formed x"
    and calls: "(76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
     (83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
     (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then l else if n=1 then g else if n=2 then gu else if n=3 then gr else if n=4 then k else x"
  from calls show ?lhs
  proof (elim disjE)
    assume call: "(76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
    have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_added_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed call in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t bounded_member_added_schema_def)
  next
    assume call: "(83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system"
    have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_package_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed call in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t bounded_member_package_schema_def)
  next
    assume call: "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_closure_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=2])
        (use formed call in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t bounded_member_closure_schema_def)
  qed
qed

lemma bounded_closure_raw:
  "(960,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>l s z k. t=Pair_Term (Pair_Term l s) z \<and>
    term_formed l \<and> term_formed s \<and> term_formed z \<and> term_formed k \<and> (\<exists>L. environment_value_presents L l) \<and>
    (47,Pair_Term z k)\<in>positive_meaning data_subset_system \<and>
    (959,Pair_Term (Pair_Term (Pair_Term l s) k) k)\<in>positive_meaning extension_package_system)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((960,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have schema: "S=bounded_closure_schema" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and>
    t=Pair_Term (Pair_Term (f 0) (f 1)) (f 2) \<and> (\<exists>L. environment_value_presents L (f 0)) \<and>
    (47,Pair_Term (f 2) (f 3))\<in>positive_meaning data_subset_system \<and>
    (959,Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (f 3)) (f 3))\<in>positive_meaning extension_package_system"
    using vars conclusion support
    by (auto simp: schema bounded_closure_schema_def schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain l s z k where t: "t=Pair_Term (Pair_Term l s) z"
    and formed: "term_formed l" "term_formed s" "term_formed z" "term_formed k"
    and admitted: "\<exists>L. environment_value_presents L l"
    and sub: "(47,Pair_Term z k)\<in>positive_meaning data_subset_system"
    and members: "(959,Pair_Term (Pair_Term (Pair_Term l s) k) k)\<in>positive_meaning extension_package_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then l else if n=1 then s else if n=2 then z else k"
  have "(960,evaluate_pattern ?f (schema_conclusion bounded_closure_schema))\<in>positive_meaning extension_package_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed admitted sub members in \<open>auto simp: extension_package_families bounded_closure_schema_def
        schema_variables_def extension_package_call extension_package_components\<close>)
  then show ?lhs by (simp add: t bounded_closure_schema_def)
qed

lemma extension_package_raw:
  "(961,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g gu gr a b u r.
    t=Pair_Term (source_root_argument g gu gr) (Pair_Term (Pair_Term a b) (Pair_Term u r)) \<and>
    term_formed g \<and> term_formed gu \<and> term_formed gr \<and> term_formed a \<and> term_formed b \<and> term_formed u \<and> term_formed r \<and>
    ((\<exists>l q. term_formed l \<and> term_formed q \<and>
       (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
       (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
       (960,Pair_Term (Pair_Term l (source_root_argument g gu gr)) q)\<in>positive_meaning extension_package_system) \<or>
     (80,source_root_argument g u r)\<in>positive_meaning package_admission_system))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((961,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>extension_package_clauses" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 5) \<and> term_formed (f 6) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and>
    term_formed (f 3) \<and> term_formed (f 4) \<and>
    t=Pair_Term (source_root_argument (f 0) (f 5) (f 6)) (Pair_Term (Pair_Term (f 1) (f 2)) (Pair_Term (f 3) (f 4))) \<and>
    ((\<exists>l q. term_formed l \<and> term_formed q \<and>
       (957,Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) l)\<in>positive_meaning extension_package_system \<and>
       (79,citation_observation_argument l (f 3) (f 4) q)\<in>positive_meaning root_family_reading_system \<and>
       (960,Pair_Term (Pair_Term l (source_root_argument (f 0) (f 5) (f 6))) q)\<in>positive_meaning extension_package_system) \<or>
     (80,source_root_argument (f 0) (f 3) (f 4))\<in>positive_meaning package_admission_system)"
  proof -
    have base: "term_formed (f 0) \<and> term_formed (f 5) \<and> term_formed (f 6) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and>
      term_formed (f 3) \<and> term_formed (f 4) \<and>
      t=Pair_Term (source_root_argument (f 0) (f 5) (f 6)) (Pair_Term (Pair_Term (f 1) (f 2)) (Pair_Term (f 3) (f 4)))"
      using family vars conclusion by (auto simp: extension_package_schema_defs schema_variables_def)
    consider "S=extension_added_site_schema" | "S=extension_given_site_schema"
      using family by (auto simp: extension_package_clauses_def)
    then show ?thesis
    proof cases
      case 1
      have lq: "term_formed (f 7)" "term_formed (f 8)"
        using vars by (auto simp: 1 extension_added_site_schema_def schema_variables_def)
      have calls: "(957,Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) (f 7))\<in>positive_meaning extension_package_system"
        "(79,citation_observation_argument (f 7) (f 3) (f 4) (f 8))\<in>positive_meaning root_family_reading_system"
        "(960,Pair_Term (Pair_Term (f 7) (source_root_argument (f 0) (f 5) (f 6))) (f 8))\<in>positive_meaning extension_package_system"
        using support by (auto simp: 1 extension_added_site_schema_def extension_package_components)
      show ?thesis using base lq calls by blast
    next
      case 2
      then show ?thesis using base support by (auto simp: extension_given_site_schema_def extension_package_components)
    qed
  qed
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g gu gr a b u r where t: "t=Pair_Term (source_root_argument g gu gr) (Pair_Term (Pair_Term a b) (Pair_Term u r))"
    and formed: "term_formed g" "term_formed gu" "term_formed gr" "term_formed a" "term_formed b" "term_formed u" "term_formed r"
    and calls: "(\<exists>l q. term_formed l \<and> term_formed q \<and>
       (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
       (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
       (960,Pair_Term (Pair_Term l (source_root_argument g gu gr)) q)\<in>positive_meaning extension_package_system) \<or>
     (80,source_root_argument g u r)\<in>positive_meaning package_admission_system" by blast
  from calls show ?lhs
  proof
    assume "\<exists>l q. term_formed l \<and> term_formed q \<and>
       (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
       (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
       (960,Pair_Term (Pair_Term l (source_root_argument g gu gr)) q)\<in>positive_meaning extension_package_system"
    then obtain l q where parts: "term_formed l" "term_formed q"
      "(957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
      "(79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system"
      "(960,Pair_Term (Pair_Term l (source_root_argument g gu gr)) q)\<in>positive_meaning extension_package_system" by blast
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then u else if n=4 then r
      else if n=5 then gu else if n=6 then gr else if n=7 then l else q"
    have "(961,evaluate_pattern ?f (schema_conclusion extension_added_site_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed parts in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t extension_added_site_schema_def)
  next
    assume call: "(80,source_root_argument g u r)\<in>positive_meaning package_admission_system"
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then u else if n=4 then r
      else if n=5 then gu else gr"
    have "(961,evaluate_pattern ?f (schema_conclusion extension_given_site_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed call in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t extension_given_site_schema_def)
  qed
qed

subsection \<open>The least environment's rows\<close>

lemma extension_row_at_values:
  assumes given: "environment_value_presents E g" and rows: "list_all2 environment_artifact_entry_presents xs ts"
  shows "(955,Pair_Term (Pair_Term g (data_list_term ts)) x)\<in>positive_meaning extension_package_system \<longleftrightarrow>
    x\<in>set ts \<or> (\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x)"
proof -
  have gf: "term_formed g" using environment_value_presents_formed[OF given] by blast
  have data: "data_elements ts" using list_all2_members[OF rows] environment_artifact_entry_formed by blast
  have af: "term_formed (data_list_term ts)" using data by (simp add: data_list_term_formed)
  have member: "(47,Pair_Term (Pair_Term x (Payload_Term [])) (data_list_term ts))\<in>positive_meaning data_subset_system \<longleftrightarrow>
      x\<in>set ts" using data_subset_lists[of "[x]" ts] data by auto
  have lookup: "(37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system \<longleftrightarrow>
      (\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x)"
  proof
    assume "(37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system"
    then obtain F e u R a where parts: "Pair_Term g x=artifact_lookup_argument e (use_data_term u) a"
      "environment_value_presents F e" "artifact_at F u R" "artifact_value_presents R a"
      unfolding artifact_lookup_exact by blast
    have "environment_value_presents F g" using parts(1,2) by simp
    then have same: "F=E" by (rule environment_value_presents_unique[OF _ given])
    show "\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x"
      using parts same by (intro bexI[of _ "(u,R)"]) (auto simp: artifact_at_def environment_artifact_entry_presents_def)
  next
    assume "\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x"
    then obtain u R v where row: "(u,R)\<in>environment_artifacts E" "artifact_value_presents R v"
      "x=Pair_Term (use_data_term u) v" by (auto simp: environment_artifact_entry_presents_def)
    show "(37,Pair_Term g x)\<in>positive_meaning artifact_lookup_system"
      unfolding artifact_lookup_exact
      by (intro exI[of _ E] exI[of _ g] exI[of _ u] exI[of _ R] exI[of _ v]) (use row given in \<open>auto simp: artifact_at_def\<close>)
  qed
  have xf: "term_formed x" if "x\<in>set ts \<or> (\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x)"
    using that data environment_artifact_entry_formed by blast
  show ?thesis unfolding extension_row_raw using gf af member lookup xf by auto
qed

lemma environment_rows_parts:
  assumes "environment_rows_presents (A,B) (Pair_Term a b)"
  shows "data_collection_presents environment_artifact_entry_presents A a"
    and "data_collection_presents (\<lambda>z v. v=binding_data z) B b"
  using assms unfolding environment_rows_presents_def by auto

theorem least_environment_sound:
  assumes given: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and holds: "(957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
  shows "\<exists>L. environment_value_presents L l \<and> environment_bindings L=B \<and>
    environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
proof -
  obtain w where l: "l=Pair_Term w b" and admitted: "\<exists>L. environment_value_presents L (Pair_Term w b)"
    and list: "(956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system"
    using holds unfolding least_environment_raw by auto
  obtain L where L: "environment_value_presents L (Pair_Term w b)" using admitted by blast
  obtain xs ts where enum: "set xs=A" "list_all2 environment_artifact_entry_presents xs ts" "a=data_list_term ts"
    using environment_rows_parts(1)[OF rows] unfolding data_collection_presents_def by blast
  have Lrows: "data_collection_presents environment_artifact_entry_presents (environment_artifacts L) w"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings L) b"
    using L unfolding environment_value_rows environment_rows_presents_def by auto
  have bindings: "environment_bindings L=B"
    by (rule data_collection_presents_unique[OF Lrows(2) environment_rows_parts(2)[OF rows]])
      (auto dest: injD[OF binding_data_injective])
  obtain ys vs where Lenum: "set ys=environment_artifacts L" "list_all2 environment_artifact_entry_presents ys vs"
    "w=data_list_term vs" using Lrows(1) unfolding data_collection_presents_def by blast
  obtain us where wlist: "w=data_list_term us"
    and each: "\<forall>v\<in>set us. (955,Pair_Term (Pair_Term g a) v)\<in>positive_meaning extension_package_system"
    using list unfolding extension_rows_lists.exact by auto
  have same: "us=vs" using wlist Lenum(3) by (simp add: data_list_term_injective)
  have artifacts: "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
  proof
    fix z assume member: "z\<in>environment_artifacts L"
    obtain v where v: "v\<in>set vs" "environment_artifact_entry_presents z v"
      using list_all2_members[OF Lenum(2)] member Lenum(1) by blast
    have "(955,Pair_Term (Pair_Term g (data_list_term ts)) v)\<in>positive_meaning extension_package_system"
      using each v(1) same enum(3) by simp
    then have "v\<in>set ts \<or> (\<exists>z'\<in>environment_artifacts E. environment_artifact_entry_presents z' v)"
      by (simp only: extension_row_at_values[OF given enum(2)])
    then show "z\<in>A\<union>environment_artifacts E"
    proof
      assume "v\<in>set ts"
      then obtain z' where "z'\<in>set xs" "environment_artifact_entry_presents z' v"
        using list_all2_members[OF enum(2)] by blast
      then show ?thesis using environment_artifact_entry_unique[OF v(2)] enum(1) by blast
    next
      assume "\<exists>z'\<in>environment_artifacts E. environment_artifact_entry_presents z' v"
      then show ?thesis using environment_artifact_entry_unique[OF v(2)] by blast
    qed
  qed
  show ?thesis using L l bindings artifacts by blast
qed

theorem least_environment_complete:
  assumes given: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and formed: "environment_formed L" and bindings: "environment_bindings L=B"
    and artifacts: "environment_artifacts L=A\<union>T" and part: "T\<subseteq>environment_artifacts E" and apart: "A\<inter>T={}"
  shows "\<exists>l. environment_value_presents L l \<and>
    (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
proof -
  obtain xs ts where enum: "distinct xs" "set xs=A" "list_all2 environment_artifact_entry_presents xs ts" "a=data_list_term ts"
    using environment_rows_parts(1)[OF rows] unfolding data_collection_presents_def by blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF given] by blast
  have finE: "finite (environment_artifacts E)" and valE: "\<And>u R. (u,R)\<in>environment_artifacts E \<Longrightarrow> exact_formed R"
    using ef unfolding environment_formed_def artifact_at_def by blast+
  have finT: "finite T" using part finE by (rule finite_subset)
  have valT: "\<forall>z\<in>T. \<exists>v. environment_artifact_entry_presents z v"
  proof
    fix z assume "z\<in>T"
    then have "exact_formed (snd z)" using part valE[of "fst z" "snd z"] by auto
    then obtain v where "artifact_value_presents (snd z) v" using artifact_value_presents_total by blast
    then show "\<exists>v. environment_artifact_entry_presents z v" unfolding environment_artifact_entry_presents_def by blast
  qed
  obtain xs2 ts2 where enum2: "distinct xs2" "set xs2=T" "list_all2 environment_artifact_entry_presents xs2 ts2"
    using data_collection_presents_total[OF finT valT] unfolding data_collection_presents_def by blast
  let ?w="data_list_term (ts@ts2)"
  have collection: "data_collection_presents environment_artifact_entry_presents (environment_artifacts L) ?w"
    unfolding data_collection_presents_def artifacts
    by (intro exI[of _ "xs@xs2"] exI[of _ "ts@ts2"]) (use enum enum2 apart in \<open>auto intro: list_all2_appendI\<close>)
  have present: "environment_value_presents L (Pair_Term ?w b)"
    unfolding environment_value_rows environment_rows_presents_def
    using formed collection environment_rows_parts(2)[OF rows] bindings by auto
  have gf: "term_formed g" using environment_value_presents_formed[OF given] by blast
  have af: "term_formed a"
    using list_all2_members[OF enum(3)] environment_artifact_entry_formed enum(4) by (auto simp: data_list_term_formed)
  have entries: "\<forall>v\<in>set (ts@ts2). (955,Pair_Term (Pair_Term g a) v)\<in>positive_meaning extension_package_system"
  proof
    fix v assume "v\<in>set (ts@ts2)"
    then consider "v\<in>set ts" | "v\<in>set ts2" by auto
    then show "(955,Pair_Term (Pair_Term g a) v)\<in>positive_meaning extension_package_system"
    proof cases
      case 1
      then show ?thesis by (simp only: enum(4) extension_row_at_values[OF given enum(3)]) simp
    next
      case 2
      obtain z where "z\<in>set xs2" "environment_artifact_entry_presents z v"
        using list_all2_members[OF enum2(3)] 2 by blast
      then show ?thesis using part enum2(2) by (simp only: enum(4) extension_row_at_values[OF given enum(3)]) blast
    qed
  qed
  have list: "(956,Pair_Term (Pair_Term g a) ?w)\<in>positive_meaning extension_package_system"
    by (rule extension_rows_lists.complete) (use gf af entries in simp_all)
  have bf: "term_formed b" and wf: "term_formed ?w" using environment_value_presents_formed[OF present] by simp_all
  have "(957,Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term ?w b))\<in>positive_meaning extension_package_system"
    unfolding least_environment_raw
    by (intro exI[of _ g] exI[of _ a] exI[of _ b] exI[of _ ?w]) (use gf af bf wf present list in auto)
  then show ?thesis using present by blast
qed

subsection \<open>The bounded closure's members and its bound\<close>

theorem bounded_member_at_values:
  assumes least: "environment_value_presents L l" and given: "environment_value_presents E g"
    and data: "data_elements ys" and site: "term_formed (source_root_argument g (use_data_term gu) (Payload_Term gr))"
  shows "(958,Pair_Term (Pair_Term (Pair_Term l (source_root_argument g (use_data_term gu) (Payload_Term gr)))
      (data_list_term ys)) x)\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (\<exists>u r p C. x=site_data_term u r \<and> native_definition_at L u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
    (\<exists>d. x=definition_site_value d \<and> native_package_formed E {d})" (is "?lhs \<longleftrightarrow> ?defined \<or> ?given")
proof -
  have lf: "term_formed l" using environment_value_presents_formed[OF least] by blast
  have kf: "term_formed (data_list_term ys)" using data by (simp add: data_list_term_formed)
  have added: "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
      \<in>positive_meaning definition_callee_list_system \<longleftrightarrow> ?defined"
    using definition_callee_list_on_values[OF least data, of "[x]"] by simp
  have member: "?given" if call: "(83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)
      \<in>positive_meaning package_membership_system"
  proof -
    obtain v a d P where parts: "x=definition_site_value d" "native_package_at E v a P" "d\<in>system_definitions P"
      using call[unfolded package_membership_at_source[OF given]] by blast
    have "native_package_formed E {d}" using native_package_support_formed(1)[OF parts(2), of "{d}"] parts(3) by blast
    then show ?thesis using parts(1) by blast
  qed
  have closure: "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system
      \<longleftrightarrow> ?given"
  proof
    assume "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    then obtain rs where rs: "Pair_Term x (Payload_Term [])=data_list_term (map (\<lambda>d. definition_site_value d) rs)"
      "native_package_formed E (set rs)" by (simp only: package_closure_admission_at_source[OF given]) blast
    have "data_list_term [x]=data_list_term (map (\<lambda>d. definition_site_value d) rs)" using rs(1) by simp
    then have "[x]=map (\<lambda>d. definition_site_value d) rs" by (simp only: data_list_term_injective)
    then obtain d where d: "rs=[d]" "x=definition_site_value d" by (cases rs) auto
    show ?given using d rs(2) by auto
  next
    assume ?given
    then obtain d where d: "x=definition_site_value d" "native_package_formed E {d}" by blast
    show "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      using package_closure_admission_on_values[OF given, of "[d]"] d by simp
  qed
  have xf1: "term_formed x" if ?defined using that native_definition_site_data_formed by blast
  have xf2: "term_formed x" if site_form: ?given
  proof -
    obtain d where d: "x=definition_site_value d" "native_package_formed E {d}" using site_form by blast
    obtain p C where "native_definition_at E (fst d) (snd d) p C"
      using d(2) native_definition_sites_self[of d E] by (auto simp: native_package_formed_def)
    then show ?thesis using d(1) native_definition_site_data_formed by blast
  qed
  show ?thesis
  proof
    assume ?lhs
    then have "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<or>
      (83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)\<in>positive_meaning package_membership_system \<or>
      (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      unfolding bounded_member_raw by auto
    then show "?defined \<or> ?given" using added member closure by blast
  next
    assume disjunction: "?defined \<or> ?given"
    have xf: "term_formed x" using disjunction xf1 xf2 by blast
    have "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<or>
      (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      using disjunction added closure by blast
    then show ?lhs unfolding bounded_member_raw using lf kf xf site by auto
  qed
qed

theorem bounded_closure_at_values:
  assumes least: "environment_value_presents L l" and given: "environment_value_presents E g"
    and site: "term_formed (source_root_argument g (use_data_term gu) (Payload_Term gr))"
  shows "(960,Pair_Term (Pair_Term l (source_root_argument g (use_data_term gu) (Payload_Term gr)))
      (data_list_term (map (\<lambda>d. definition_site_value d) ws)))\<in>positive_meaning extension_package_system \<longleftrightarrow>
    bounded_closure_formed L E (set ws)"
proof
  let ?s="source_root_argument g (use_data_term gu) (Payload_Term gr)"
  assume holds: "(960,Pair_Term (Pair_Term l ?s) (data_list_term (map (\<lambda>d. definition_site_value d) ws)))
    \<in>positive_meaning extension_package_system"
  obtain k where sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ws)) k)\<in>positive_meaning data_subset_system"
    and list: "(959,Pair_Term (Pair_Term (Pair_Term l ?s) k) k)\<in>positive_meaning extension_package_system"
    using holds unfolding bounded_closure_raw by auto
  obtain xs ys where bounds: "data_list_term (map (\<lambda>d. definition_site_value d) ws)=data_list_term xs"
    "k=data_list_term ys" "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
    using sub unfolding data_subset_exact by auto
  have xs: "xs=map (\<lambda>d. definition_site_value d) ws" using bounds(1) by (simp only: data_list_term_injective)
  have each: "\<forall>x\<in>set ys. (958,Pair_Term (Pair_Term (Pair_Term l ?s) (data_list_term ys)) x)\<in>positive_meaning extension_package_system"
    using list unfolding bounded_members_lists.exact bounds(2) by (auto simp: data_list_term_injective)
  have read: "\<forall>x\<in>set ys. \<exists>d. x=definition_site_value d \<and>
      ((\<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
       native_package_formed E {d})"
  proof
    fix x assume member: "x\<in>set ys"
    have "(\<exists>u r p C. x=site_data_term u r \<and> native_definition_at L u r p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
      (\<exists>d. x=definition_site_value d \<and> native_package_formed E {d})"
      using each member bounded_member_at_values[OF least given bounds(4) site, of x] by blast
    then show "\<exists>d. x=definition_site_value d \<and>
      ((\<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
       native_package_formed E {d})"
    proof
      assume "\<exists>u r p C. x=site_data_term u r \<and> native_definition_at L u r p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
      then obtain u r p C where parts: "x=site_data_term u r" "native_definition_at L u r p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by blast
      show ?thesis by (rule exI[of _ "(u,r)"]) (use parts in auto)
    next
      assume "\<exists>d. x=definition_site_value d \<and> native_package_formed E {d}"
      then show ?thesis by blast
    qed
  qed
  obtain ds where ds: "ys=map (\<lambda>d. definition_site_value d) ds"
    and dsP: "\<forall>d\<in>set ds. (\<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
       native_package_formed E {d}"
    using iffD1[OF list_range_restricted_witnesses read] by blast
  let ?U="{d\<in>set ds. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>set ds)}"
  let ?Y="{d\<in>set ds. native_package_formed E {d}}"
  have deps: "schema_dependencies S\<subseteq>set ds" if "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" for S
    using that ds by auto
  have cover: "set ds\<subseteq>?U\<union>?Y"
  proof
    fix d assume member: "d\<in>set ds"
    show "d\<in>?U\<union>?Y"
    proof (cases "native_package_formed E {d}")
      case True
      then show ?thesis using member by blast
    next
      case False
      then obtain p C where raw: "native_definition_at L (fst d) (snd d) p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
        using dsP member by blast
      have closed: "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>set ds"
      proof (intro allI impI)
        fix c S assume "(c,S)\<in>C"
        then show "schema_dependencies S\<subseteq>set ds" using raw(2) by (intro deps) blast
      qed
      show ?thesis using raw(1) closed member by blast
    qed
  qed
  have roots: "set ws\<subseteq>set ds" using bounds(5) xs ds by auto
  have "bounded_package_formed L (set ws) ?Y"
    unfolding bounded_package_formed_def
  proof (intro conjI exI[of _ ?U])
    show "environment_formed L" using environment_value_presents_formed[OF least] by blast
    show "finite ?U" by simp
    show "set ws\<subseteq>?U\<union>?Y" using roots cover by blast
    show "\<forall>d\<in>?U. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U\<union>?Y)" using cover by blast
  qed
  then show "bounded_closure_formed L E (set ws)" unfolding bounded_closure_formed_def by (intro exI[of _ ?Y]) auto
next
  let ?s="source_root_argument g (use_data_term gu) (Payload_Term gr)"
  assume "bounded_closure_formed L E (set ws)"
  then obtain Y U where finY: "finite Y" and givenY: "\<forall>y\<in>Y. native_package_formed E {y}" and finU: "finite U"
    and roots: "set ws\<subseteq>U\<union>Y"
    and defined: "\<forall>d\<in>U. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y)"
    unfolding bounded_closure_formed_def bounded_package_formed_def by blast
  obtain ds where ds: "set ds=U\<union>Y" using finite_list[of "U\<union>Y"] finU finY by blast
  let ?ys="map (\<lambda>d. definition_site_value d) ds"
  have siteformed: "term_formed (definition_site_value d)" if "d\<in>U\<union>Y" for d
  proof (cases "d\<in>U")
    case True
    then show ?thesis using defined native_definition_site_data_formed by blast
  next
    case False
    then have "native_package_formed E {d}" using that givenY by blast
    then obtain p C where "native_definition_at E (fst d) (snd d) p C"
      using native_definition_sites_self[of d E] by (auto simp: native_package_formed_def)
    then show ?thesis using native_definition_site_data_formed by blast
  qed
  have data: "data_elements ?ys" using siteformed ds by (auto simp: site_data_term_self_contained)
  have rdata: "data_elements (map (\<lambda>d. definition_site_value d) ws)"
    using siteformed roots by (auto simp: site_data_term_self_contained)
  have sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ws)) (data_list_term ?ys))
      \<in>positive_meaning data_subset_system"
    by (simp only: data_subset_lists) (use rdata data roots ds in auto)
  have each: "\<forall>x\<in>set ?ys. (958,Pair_Term (Pair_Term (Pair_Term l ?s) (data_list_term ?ys)) x)
      \<in>positive_meaning extension_package_system"
  proof
    fix x assume "x\<in>set ?ys"
    then obtain d where d: "d\<in>U\<union>Y" "x=definition_site_value d" using ds by auto
    show "(958,Pair_Term (Pair_Term (Pair_Term l ?s) (data_list_term ?ys)) x)\<in>positive_meaning extension_package_system"
    proof (cases "d\<in>U")
      case True
      obtain p C where raw: "native_definition_at L (fst d) (snd d) p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y" using defined True by blast
      have "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys" using raw(2) ds by auto
      then show ?thesis using bounded_member_at_values[OF least given data site, of x] raw(1) d(2) by (cases d) auto
    next
      case False
      then have "native_package_formed E {d}" using d(1) givenY by blast
      then show ?thesis using bounded_member_at_values[OF least given data site, of x] d(2) by blast
    qed
  qed
  have lf: "term_formed l" using environment_value_presents_formed[OF least] by blast
  have list: "(959,Pair_Term (Pair_Term (Pair_Term l ?s) (data_list_term ?ys)) (data_list_term ?ys))
      \<in>positive_meaning extension_package_system"
    by (rule bounded_members_lists.complete) (use lf site data each in \<open>simp_all add: data_list_term_formed\<close>)
  show "(960,Pair_Term (Pair_Term l ?s) (data_list_term (map (\<lambda>d. definition_site_value d) ws)))
    \<in>positive_meaning extension_package_system"
    unfolding bounded_closure_raw
    by (intro exI[of _ l] exI[of _ ?s] exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ws)"]
      exI[of _ "data_list_term ?ys"]) (use lf site rdata data least sub list in \<open>auto simp: data_list_term_formed\<close>)
qed

subsection \<open>G2: the package at a site of an extension, exact to package admission\<close>

theorem extension_package_at_values:
  assumes gvalue: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and formed: "term_formed (Pair_Term (source_root_argument g (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term a b) (site_data_term u r)))"
  shows "(961,Pair_Term (source_root_argument g (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term a b) (site_data_term u r)))\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (\<exists>P. native_package_at (environment_extension E A B) u r P)"
proof
  let ?F="environment_extension E A B" and ?s="source_root_argument g (use_data_term gu) (Payload_Term gr)"
  have sformed: "term_formed ?s" using formed by simp
  assume holds: "(961,Pair_Term ?s (Pair_Term (Pair_Term a b) (site_data_term u r)))\<in>positive_meaning extension_package_system"
  have "(\<exists>l q. (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
      (960,Pair_Term (Pair_Term l ?s) q)\<in>positive_meaning extension_package_system) \<or>
    (80,source_root_argument g (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
    using holds unfolding extension_package_raw by (auto simp: site_data_term_def)
  then show "\<exists>P. native_package_at ?F u r P"
  proof
    assume "\<exists>l q. (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
      (960,Pair_Term (Pair_Term l ?s) q)\<in>positive_meaning extension_package_system"
    then obtain l q where least: "(957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
      and family: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system"
      and closure: "(960,Pair_Term (Pair_Term l ?s) q)\<in>positive_meaning extension_package_system" by blast
    obtain L where L: "environment_value_presents L l" "environment_bindings L=B"
      "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
      using least_environment_sound[OF gvalue rows least] by blast
    obtain ds where q: "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
      using family by (simp only: root_family_reading_at_source[OF L(1)]) blast
    obtain Q where Q: "native_root_family_at L u r Q" "rel_ran Q=set ds"
      using root_family_reading_recovers[OF L(1) family[unfolded q]] by blast
    have bounded: "bounded_closure_formed L E (set ds)"
      using closure[unfolded q] bounded_closure_at_values[OF L(1) gvalue sformed] by blast
    have included: "environment_included L ?F" using L(2,3) by (auto simp: environment_included_def)
    show ?thesis
      by (rule bounded_closure_package[OF included environment_extension_included ff Q(1)]) (use bounded Q(2) in simp)
  next
    assume "(80,source_root_argument g (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
    then obtain P where "native_package_at E u r P" by (simp only: package_admission_on_values[OF gvalue]) blast
    then show ?thesis using native_package_included[OF _ environment_extension_included ff] by blast
  qed
next
  let ?F="environment_extension E A B" and ?s="source_root_argument g (use_data_term gu) (Payload_Term gr)"
  have sformed: "term_formed ?s" using formed by simp
  assume "\<exists>P. native_package_at ?F u r P"
  then obtain P where package: "native_package_at ?F u r P" by blast
  obtain Q where "native_root_family_at ?F u r Q" using package by (auto simp: native_package_at_def)
  then obtain R where "artifact_at ?F u R" by (auto simp: native_root_family_at_def)
  then have "u\<in>environment_uses ?F" using rel_domI[of u R] by (simp add: environment_uses_def artifact_at_def)
  then consider (given_site) "u\<in>environment_uses E" | (added_site) "u\<in>rel_dom A" by (auto simp: extension_uses)
  then show "(961,Pair_Term ?s (Pair_Term (Pair_Term a b) (site_data_term u r)))\<in>positive_meaning extension_package_system"
  proof cases
    case given_site
    have "native_package_at E u r P" using extension_given_package[OF additions ff given_site] package by blast
    then have "(80,source_root_argument g (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
      by (rule package_admission_complete[OF gvalue])
    then show ?thesis unfolding extension_package_raw using formed by (auto simp: site_data_term_def)
  next
    case added_site
    let ?L="additions_least_environment E A B" and ?T="{z\<in>environment_artifacts E. fst z\<in>snd ` B}"
    obtain Q where family: "native_root_family_at ?L u r Q" and bounded: "bounded_closure_formed ?L E (rel_ran Q)"
      using extension_added_package[OF additions ff added_site] package by blast
    have apart: "A\<inter>?T={}"
    proof -
      have "fst z\<in>rel_dom A" if "z\<in>A" for z using that rel_domI[of "fst z" "snd z" A] by simp
      moreover have "fst z\<in>environment_uses E" if "z\<in>environment_artifacts E" for z
        using that rel_domI[of "fst z" "snd z" "environment_artifacts E"] by (simp add: environment_uses_def)
      ultimately show ?thesis using additions_parts(2)[OF additions] by blast
    qed
    have part: "?T\<subseteq>environment_artifacts E" by blast
    obtain l where l: "environment_value_presents ?L l"
      "(957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
      using least_environment_complete[OF gvalue rows additions_least_formed[OF additions ff]
        additions_least_bindings[OF additions] additions_least_artifacts[OF additions] part apart] by blast
    obtain ds where read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r)
        (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
      and range: "rel_ran Q=set ds" using root_family_reading_total[OF l(1) family] by blast
    have closure: "(960,Pair_Term (Pair_Term l ?s) (data_list_term (map (\<lambda>d. definition_site_value d) ds)))
        \<in>positive_meaning extension_package_system"
      using bounded_closure_at_values[OF l(1) gvalue sformed] bounded range by simp
    have lq: "term_formed l" "term_formed (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
      using schema_call_formed_target[OF positive_meaning_formed[OF read]] by simp_all
    have "\<exists>l q. term_formed l \<and> term_formed q \<and>
       (957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system \<and>
       (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
       (960,Pair_Term (Pair_Term l ?s) q)\<in>positive_meaning extension_package_system"
      using lq l(2) read closure by blast
    then show ?thesis unfolding extension_package_raw using formed by (auto simp: site_data_term_def)
  qed
qed

corollary extension_package_exact:
  assumes gvalue: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and formed: "term_formed (Pair_Term (source_root_argument g (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term a b) (site_data_term u r)))"
    and extension: "environment_value_presents (environment_extension E A B) f"
  shows "(961,Pair_Term (source_root_argument g (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term a b) (site_data_term u r)))\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (80,source_root_argument f (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
  by (simp only: extension_package_at_values[OF gvalue rows additions ff formed] package_admission_on_values[OF extension])

section \<open>G2's relation is equivariant under permutations of uses\<close>

abbreviation extension_package_relation where
  "extension_package_relation x \<equiv> \<exists>P. native_package_at
    (environment_extension (fst x) (fst (fst (snd x))) (snd (fst (snd x)))) (fst (snd (snd x))) (snd (snd (snd x))) P"

theorem extension_package_equivariant:
  "renaming_equivariant bij (product_action rename_environment additions_renaming)
    (\<lambda>x. additions_pair_domain x \<and> environment_formed (environment_extension (fst x) (fst (fst (snd x))) (snd (fst (snd x)))))
    extension_package_relation"
proof (unfold renaming_equivariant_def, intro allI impI, goal_cases)
  case (1 h x)
  then have permutation: "bij h" by simp
  obtain E A B s where x: "x=(E,((A,B),s))" by (metis prod.collapse)
  have ff: "environment_formed (environment_extension E A B)" using 1 x by simp
  have renamed: "(\<exists>Q. native_package_at (rename_environment h (environment_extension E A B)) (h (fst s)) (snd s) Q) \<longleftrightarrow>
      (\<exists>P. native_package_at (environment_extension E A B) (fst s) (snd s) P)"
    using native_package_use_renaming[OF ff permutation, of "fst s" "snd s"] by blast
  show ?case using 1 renamed by (simp add: x environment_extension_renaming[symmetric])
qed

section \<open>The new programs state the empty payload alone\<close>

lemma extension_row_system_payloads [lineage_payloads]: "system_payloads extension_row_system\<subseteq>{[]}"
  unfolding extension_row_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps extension_row_clauses_def
    extension_row_added_schema_def extension_row_given_schema_def)

lemma extension_rows_system_payloads [lineage_payloads]: "system_payloads extension_rows_system\<subseteq>{[]}"
  unfolding extension_rows_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma least_environment_system_payloads [lineage_payloads]: "system_payloads least_environment_system\<subseteq>{[]}"
  unfolding least_environment_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps least_environment_schema_def)

lemma bounded_member_system_payloads [lineage_payloads]: "system_payloads bounded_member_system\<subseteq>{[]}"
  unfolding bounded_member_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps bounded_member_clauses_def
    bounded_member_added_schema_def bounded_member_package_schema_def bounded_member_closure_schema_def)

lemma bounded_members_system_payloads [lineage_payloads]: "system_payloads bounded_members_system\<subseteq>{[]}"
  unfolding bounded_members_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma bounded_closure_system_payloads [lineage_payloads]: "system_payloads bounded_closure_system\<subseteq>{[]}"
  unfolding bounded_closure_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps bounded_closure_schema_def)

lemma extension_package_system_payloads [lineage_payloads]: "system_payloads extension_package_system\<subseteq>{[]}"
  unfolding extension_package_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps extension_package_clauses_def
    extension_added_site_schema_def extension_given_site_schema_def)

end
