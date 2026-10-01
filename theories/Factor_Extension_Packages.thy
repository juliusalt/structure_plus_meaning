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
  Twelve ordinary definitions, at 955 to 966 above every numbered site of the library and views over package
  membership (83), read G2 at the pair of the given's site value and the additions. 955 and 956 check a
  proposed least environment's rows: each is an added row (47 over the added rows) or a row of the given (37 at
  the given's value). 957 admits the proposed least environment (26), its rows so checked and its binding rows any
  enumeration of the set of the added binding rows (47 both ways): the order of a finite relation belongs to no
  notion; and it checks the extension's formation (954), so that a least environment is one of a formed extension
  (task 961). 962 and 963 check that no binding row of the least environment has a given use as its source, by data
  inequality (3). 958 and 959 check a bounded closure's members: an added definition read in the least
  environment with its callees in the bound (76), or a given site at whose use the least environment binds nothing
  (963) and holds the given's row (5 selecting the row at the site's use from the least environment's artifact
  table, 37 finding it at the given's value), a member of the given's package (83 at the given's site) or a site
  whose closure is formed in the given (77 at the given's value); a site with bindings in the least environment
  passes only as an added definition, and a local edge from a given site stays in its closure in the given, each
  site there passing as given, so the reach over the least environment's edges from the roots is a bound whenever
  any is (task 934, @{text Factor_Extension_Registrations.extension_bound_reach_passes}). 960 checks the bound: the roots
  in it (47) and every member checked. 964 reads an added site in a least environment: its root family (79) and
  the bounded closure of its roots (960). 961 is G2: at an added site the least environment (957) and 964 at it; at
  a given site package admission at the given's value (80). The least environment is premise-only at 961, produced
  by 957 from the given and the additions alone; the roots are produced by 79; the bound is premise-only at 960.
  Each is handed in, never produced by these clauses. 965 reads a row of the least environment, at the given, the
  additions and the added site's use: a stored row (966: a member of the added rows, 47, or a row 5 selects from the
  given's artifact table) whose use is the site's or a source or a target of an added binding row (5 over the added
  binding rows); the least environment's rows are collected as its rows, each the stored row at its use.
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
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,26,Pattern_Pair data_w (Pattern_Variable 4)),(1,956,Pattern_Pair (Pattern_Pair data_x data_y) data_w),
     (2,47,Pattern_Pair data_z (Pattern_Variable 4)),(3,47,Pattern_Pair (Pattern_Variable 4) data_z),
     (4,954,Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Payload [])))}"

definition source_absence_schema :: "(nat,nat,nat) factor_schema" where
  "source_absence_schema=data_rule (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w))
    {(0,3,Pattern_Pair data_x data_y)}"

abbreviation bounded_member_pattern :: "nat term_pattern" where
  "bounded_member_pattern \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair data_x (source_root_pattern data_y data_z data_w))
    (Pattern_Variable 4)) (Pattern_Variable 5)"

definition bounded_member_added_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_added_schema=data_rule bounded_member_pattern
    {(0,76,Pattern_Pair (Pattern_Pair data_x (Pattern_Variable 4)) (Pattern_Pair (Pattern_Variable 5) (Pattern_Payload [])))}"

abbreviation bounded_given_pattern :: "nat term_pattern" where
  "bounded_given_pattern \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))
    (source_root_pattern data_y data_z data_w)) (Pattern_Variable 4)) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8))"

definition bounded_member_package_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_package_schema=data_rule bounded_given_pattern
    {(0,83,Pattern_Pair (source_root_pattern data_y data_z data_w) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8))),
     (1,963,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7)),
     (2,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9)) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 10))),
     (3,37,Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9)))}"

definition bounded_member_closure_schema :: "(nat,nat,nat) factor_schema" where
  "bounded_member_closure_schema=data_rule bounded_given_pattern
    {(0,77,Pattern_Pair data_y (Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8)) (Pattern_Payload []))),
     (1,963,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7)),
     (2,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9)) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 10))),
     (3,37,Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9)))}"

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

definition added_site_schema :: "(nat,nat,nat) factor_schema" where
  "added_site_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,79,citation_observation_pattern data_x data_z data_w (Pattern_Variable 4)),
     (1,960,Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 4))}"

definition extension_added_site_schema :: "(nat,nat,nat) factor_schema" where
  "extension_added_site_schema=data_rule extension_package_pattern
    {(0,957,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Variable 7)),
     (1,964,Pattern_Pair (Pattern_Pair (Pattern_Variable 7)
       (source_root_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6))) (Pattern_Pair data_w (Pattern_Variable 4)))}"

definition extension_given_site_schema :: "(nat,nat,nat) factor_schema" where
  "extension_given_site_schema=data_rule extension_package_pattern
    {(0,80,source_root_pattern data_x data_w (Pattern_Variable 4))}"

definition extension_package_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "extension_package_clauses={(0,extension_added_site_schema),(1,extension_given_site_schema)}"

definition stored_row_given_schema :: "(nat,nat,nat) factor_schema" where
  "stored_row_given_schema=data_rule (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_w) data_y) data_z)
    {(0,5,Pattern_Pair data_z (Pattern_Pair data_x (Pattern_Variable 4)))}"

definition stored_row_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "stored_row_clauses={(0,extension_row_added_schema),(1,stored_row_given_schema)}"

abbreviation least_row_pattern :: "nat term_pattern \<Rightarrow> nat term_pattern" where
  "least_row_pattern v \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    (Pattern_Pair v (Pattern_Variable 5))"

abbreviation least_row_premise :: "nat term_pattern \<Rightarrow> nat \<times> nat \<times> nat term_pattern" where
  "least_row_premise v \<equiv> (0,966,Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair v (Pattern_Variable 5)))"

definition least_row_site_schema :: "(nat,nat,nat) factor_schema" where
  "least_row_site_schema=data_rule (least_row_pattern data_w) {least_row_premise data_w}"

definition least_row_source_schema :: "(nat,nat,nat) factor_schema" where
  "least_row_source_schema=data_rule (least_row_pattern (Pattern_Variable 4)) {least_row_premise (Pattern_Variable 4),
    (1,5,Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 6)) (Pattern_Variable 7))
      (Pattern_Pair data_z (Pattern_Variable 8)))}"

definition least_row_target_schema :: "(nat,nat,nat) factor_schema" where
  "least_row_target_schema=data_rule (least_row_pattern (Pattern_Variable 4)) {least_row_premise (Pattern_Variable 4),
    (1,5,Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 4))
      (Pattern_Pair data_z (Pattern_Variable 8)))}"

definition least_row_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "least_row_clauses={(0,least_row_site_schema),(1,least_row_source_schema),(2,least_row_target_schema)}"

subsection \<open>The readers the program stands over: package membership and the extension's formation\<close>

text \<open>
  957 checks the extension's formation (AX1's reader, 954) beside the proposed least environment's rows and bindings,
  so that a least environment is one of a formed extension (task 961, the planner's q180): the program stands over
  package membership (83) and the formation reader together. The two agree where both define a site, each being a
  lineage of the complete data admission program where it defines one.
\<close>

lemma lookup_complete_definitions:
  "system_definitions artifact_lookup_system\<subseteq>system_definitions complete_data_admission_system"
  by (rule whole_agreement_definitions[OF complete_data_lookup_agreement])

lemma membership_complete_definitions:
  "system_definitions package_membership_system\<subseteq>system_definitions complete_data_admission_system"
  by (rule whole_agreement_definitions[OF membership_complete_data_agreement])

lemma lookup_formation_agreement:
  "systems_agree_on artifact_lookup_system extension_formation_system (system_definitions artifact_lookup_system)"
proof -
  note below=complete_below
  have fresh: "d\<notin>system_definitions artifact_lookup_system" if "390\<le>d" for d
    using lookup_complete_definitions below that by (meson lessThan_iff not_le subsetD)
  show ?thesis
    using fresh[of 950] fresh[of 951] fresh[of 952] fresh[of 953] fresh[of 954]
    by (simp add: systems_agree_on_added extension_formation_system_def added_bindings_system_def
      added_binding_system_def added_uses_fresh_system_def added_use_fresh_system_def)
qed

lemma complete_formation_agreement:
  "systems_agree_on complete_data_admission_system extension_formation_system
    (system_definitions complete_data_admission_system\<inter>system_definitions extension_formation_system)"
proof (rule systems_agree_on_subdomain[OF systems_agree_on_transitive[OF
    systems_agree_on_sym[OF complete_data_lookup_agreement] lookup_formation_agreement]])
  note below=complete_below
  show "system_definitions complete_data_admission_system\<inter>system_definitions extension_formation_system\<subseteq>
      system_definitions artifact_lookup_system"
    using below by auto
qed

lemma membership_formation_agreement:
  "systems_agree_on package_membership_system extension_formation_system
    (system_definitions package_membership_system\<inter>system_definitions extension_formation_system)"
proof (rule common_component_overlap_agreement[OF _ complete_formation_agreement])
  show "systems_agree_on complete_data_admission_system package_membership_system
      (system_definitions complete_data_admission_system\<inter>system_definitions package_membership_system)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF membership_complete_data_agreement]]) blast
  show "system_definitions package_membership_system\<inter>system_definitions extension_formation_system\<subseteq>
      system_definitions complete_data_admission_system"
    using membership_complete_definitions by blast
qed

definition extension_readers_base_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_readers_base_system=system_union package_membership_system extension_formation_system"

lemma extension_readers_base_formed [simp]: "schema_system_formed extension_readers_base_system"
  unfolding extension_readers_base_system_def
  by (rule system_union_agree_formed[OF package_membership_system_formed extension_formation_system_formed
    membership_formation_agreement])

lemma extension_readers_base_definitions [simp]:
  "system_definitions extension_readers_base_system=
    system_definitions package_membership_system\<union>system_definitions extension_formation_system"
  by (simp add: extension_readers_base_system_def)

lemma extension_readers_base_call:
  "schema_call_formed extension_readers_base_system d t \<longleftrightarrow>
    d\<in>system_definitions extension_readers_base_system \<and> term_formed t"
  unfolding extension_readers_base_system_def
  by (simp only: system_union_agree_call[OF package_membership_system_formed extension_formation_system_formed
    membership_formation_agreement] package_membership_call extension_formation_call system_union_definitions Un_iff) blast

lemma extension_readers_base_membership:
  assumes "d\<in>system_definitions package_membership_system"
  shows "(d,t)\<in>positive_meaning extension_readers_base_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
  unfolding extension_readers_base_system_def
  by (rule system_union_agree_left_locality(2)[OF package_membership_system_formed extension_formation_system_formed
    membership_formation_agreement assms])

lemma extension_readers_base_below: "system_definitions extension_readers_base_system\<subseteq>{..<955}"
proof -
  note below=complete_below
  show ?thesis using membership_complete_definitions lookup_complete_definitions below by auto
qed

lemma extension_readers_base_formation:
  assumes "d\<in>system_definitions extension_formation_system"
  shows "(d,t)\<in>positive_meaning extension_readers_base_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_formation_system"
  unfolding extension_readers_base_system_def
  by (rule system_union_agree_right_locality(2)[OF package_membership_system_formed extension_formation_system_formed
    membership_formation_agreement assms])

definition extension_row_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_row_system=add_view_definition extension_readers_base_system 955 data_x extension_row_clauses"

definition extension_rows_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_rows_system=add_view_definition extension_row_system 956 data_x (context_list_clauses 955 956)"

definition least_environment_system :: "(nat,nat,nat,nat) schema_system" where
  "least_environment_system=add_view_definition extension_rows_system 957 data_x {(0,least_environment_schema)}"

definition source_absence_system :: "(nat,nat,nat,nat) schema_system" where
  "source_absence_system=add_view_definition least_environment_system 962 data_x {(0,source_absence_schema)}"

definition source_absences_system :: "(nat,nat,nat,nat) schema_system" where
  "source_absences_system=add_view_definition source_absence_system 963 data_x (context_list_clauses 962 963)"

definition bounded_member_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_member_system=add_view_definition source_absences_system 958 data_x bounded_member_clauses"

definition bounded_members_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_members_system=add_view_definition bounded_member_system 959 data_x (context_list_clauses 958 959)"

definition bounded_closure_system :: "(nat,nat,nat,nat) schema_system" where
  "bounded_closure_system=add_view_definition bounded_members_system 960 data_x {(0,bounded_closure_schema)}"

definition added_site_system :: "(nat,nat,nat,nat) schema_system" where
  "added_site_system=add_view_definition bounded_closure_system 964 data_x {(0,added_site_schema)}"

definition stored_row_system :: "(nat,nat,nat,nat) schema_system" where
  "stored_row_system=add_view_definition added_site_system 966 data_x stored_row_clauses"

definition least_row_system :: "(nat,nat,nat,nat) schema_system" where
  "least_row_system=add_view_definition stored_row_system 965 data_x least_row_clauses"

definition extension_package_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_package_system=add_view_definition least_row_system 961 data_x extension_package_clauses"

lemmas extension_package_schema_defs = extension_row_clauses_def extension_row_added_schema_def
  extension_row_given_schema_def least_environment_schema_def source_absence_schema_def bounded_member_clauses_def
  bounded_member_added_schema_def bounded_member_package_schema_def bounded_member_closure_schema_def
  bounded_closure_schema_def extension_package_clauses_def added_site_schema_def extension_added_site_schema_def
  extension_given_site_schema_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
  least_row_clauses_def least_row_site_schema_def least_row_source_schema_def least_row_target_schema_def
  stored_row_clauses_def stored_row_given_schema_def

lemma extension_row_system_formed [simp]: "schema_system_formed extension_row_system"
  unfolding extension_row_system_def
  by (rule add_recursive_definition_formed[OF extension_readers_base_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_row_definitions [simp]:
  "system_definitions extension_row_system=insert 955 (system_definitions extension_readers_base_system)"
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

lemma source_absence_system_formed [simp]: "schema_system_formed source_absence_system"
  unfolding source_absence_system_def
  by (rule add_recursive_definition_formed[OF least_environment_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma source_absence_definitions [simp]:
  "system_definitions source_absence_system=insert 962 (system_definitions least_environment_system)"
  by (simp add: source_absence_system_def)

lemma source_absences_system_formed [simp]: "schema_system_formed source_absences_system"
  unfolding source_absences_system_def
  by (rule add_recursive_definition_formed[OF source_absence_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma source_absences_definitions [simp]:
  "system_definitions source_absences_system=insert 963 (system_definitions source_absence_system)"
  by (simp add: source_absences_system_def)

lemma bounded_member_system_formed [simp]: "schema_system_formed bounded_member_system"
  unfolding bounded_member_system_def
  by (rule add_recursive_definition_formed[OF source_absences_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma bounded_member_definitions [simp]:
  "system_definitions bounded_member_system=insert 958 (system_definitions source_absences_system)"
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

lemma added_site_system_formed [simp]: "schema_system_formed added_site_system"
  unfolding added_site_system_def
  by (rule add_recursive_definition_formed[OF bounded_closure_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma added_site_definitions [simp]:
  "system_definitions added_site_system=insert 964 (system_definitions bounded_closure_system)"
  by (simp add: added_site_system_def)

lemma stored_row_system_formed [simp]: "schema_system_formed stored_row_system"
  unfolding stored_row_system_def
  by (rule add_recursive_definition_formed[OF added_site_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma stored_row_definitions [simp]:
  "system_definitions stored_row_system=insert 966 (system_definitions added_site_system)"
  by (simp add: stored_row_system_def)

lemma least_row_system_formed [simp]: "schema_system_formed least_row_system"
  unfolding least_row_system_def
  by (rule add_recursive_definition_formed[OF stored_row_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma least_row_definitions [simp]:
  "system_definitions least_row_system=insert 965 (system_definitions stored_row_system)"
  by (simp add: least_row_system_def)

lemma extension_package_system_formed [simp]: "schema_system_formed extension_package_system"
  unfolding extension_package_system_def
  by (rule add_recursive_definition_formed[OF least_row_system_formed])
    (auto simp: extension_package_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_package_definitions [simp]:
  "system_definitions extension_package_system=insert 961 (system_definitions least_row_system)"
  by (simp add: extension_package_system_def)

lemma extension_row_call:
  "schema_call_formed extension_row_system d t \<longleftrightarrow> d\<in>system_definitions extension_row_system \<and> term_formed t"
  using added_variable_calls[OF extension_readers_base_formed
    extension_row_system_formed[unfolded extension_row_system_def] extension_readers_base_call]
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

lemma source_absence_call:
  "schema_call_formed source_absence_system d t \<longleftrightarrow> d\<in>system_definitions source_absence_system \<and> term_formed t"
  using added_variable_calls[OF least_environment_system_formed
    source_absence_system_formed[unfolded source_absence_system_def] least_environment_call]
  by (simp only: source_absence_system_def[symmetric])

lemma source_absences_call:
  "schema_call_formed source_absences_system d t \<longleftrightarrow> d\<in>system_definitions source_absences_system \<and> term_formed t"
  using added_variable_calls[OF source_absence_system_formed
    source_absences_system_formed[unfolded source_absences_system_def] source_absence_call]
  by (simp only: source_absences_system_def[symmetric])

lemma bounded_member_call:
  "schema_call_formed bounded_member_system d t \<longleftrightarrow> d\<in>system_definitions bounded_member_system \<and> term_formed t"
  using added_variable_calls[OF source_absences_system_formed
    bounded_member_system_formed[unfolded bounded_member_system_def] source_absences_call]
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

lemma added_site_call:
  "schema_call_formed added_site_system d t \<longleftrightarrow> d\<in>system_definitions added_site_system \<and> term_formed t"
  using added_variable_calls[OF bounded_closure_system_formed
    added_site_system_formed[unfolded added_site_system_def] bounded_closure_call]
  by (simp only: added_site_system_def[symmetric])

lemma stored_row_call:
  "schema_call_formed stored_row_system d t \<longleftrightarrow> d\<in>system_definitions stored_row_system \<and> term_formed t"
  using added_variable_calls[OF added_site_system_formed
    stored_row_system_formed[unfolded stored_row_system_def] added_site_call]
  by (simp only: stored_row_system_def[symmetric])

lemma least_row_call:
  "schema_call_formed least_row_system d t \<longleftrightarrow> d\<in>system_definitions least_row_system \<and> term_formed t"
  using added_variable_calls[OF stored_row_system_formed
    least_row_system_formed[unfolded least_row_system_def] stored_row_call]
  by (simp only: least_row_system_def[symmetric])

lemma extension_package_call:
  "schema_call_formed extension_package_system d t \<longleftrightarrow> d\<in>system_definitions extension_package_system \<and> term_formed t"
  using added_variable_calls[OF least_row_system_formed
    extension_package_system_formed[unfolded extension_package_system_def] least_row_call]
  by (simp only: extension_package_system_def[symmetric])

lemma extension_package_base_meaning:
  assumes old: "d\<in>system_definitions extension_readers_base_system"
  shows "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_readers_base_system"
proof -
  have step1: "(d,t)\<in>positive_meaning extension_row_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_readers_base_system"
    using added_definition_preserves_old(2)[OF extension_readers_base_formed
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
  have step3a: "(d,t)\<in>positive_meaning source_absence_system \<longleftrightarrow> (d,t)\<in>positive_meaning least_environment_system"
    using added_definition_preserves_old(2)[OF least_environment_system_formed
      source_absence_system_formed[unfolded source_absence_system_def], of d t] old
    by (auto simp: source_absence_system_def)
  have step3b: "(d,t)\<in>positive_meaning source_absences_system \<longleftrightarrow> (d,t)\<in>positive_meaning source_absence_system"
    using added_definition_preserves_old(2)[OF source_absence_system_formed
      source_absences_system_formed[unfolded source_absences_system_def], of d t] old
    by (auto simp: source_absences_system_def)
  have step4: "(d,t)\<in>positive_meaning bounded_member_system \<longleftrightarrow> (d,t)\<in>positive_meaning source_absences_system"
    using added_definition_preserves_old(2)[OF source_absences_system_formed
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
  have step6b: "(d,t)\<in>positive_meaning added_site_system \<longleftrightarrow> (d,t)\<in>positive_meaning bounded_closure_system"
    using added_definition_preserves_old(2)[OF bounded_closure_system_formed
      added_site_system_formed[unfolded added_site_system_def], of d t] old
    by (auto simp: added_site_system_def)
  have step6s: "(d,t)\<in>positive_meaning stored_row_system \<longleftrightarrow> (d,t)\<in>positive_meaning added_site_system"
    using added_definition_preserves_old(2)[OF added_site_system_formed
      stored_row_system_formed[unfolded stored_row_system_def], of d t] old
    by (auto simp: stored_row_system_def)
  have step6c: "(d,t)\<in>positive_meaning least_row_system \<longleftrightarrow> (d,t)\<in>positive_meaning stored_row_system"
    using added_definition_preserves_old(2)[OF stored_row_system_formed
      least_row_system_formed[unfolded least_row_system_def], of d t] old
    by (auto simp: least_row_system_def)
  have step7: "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning least_row_system"
    using added_definition_preserves_old(2)[OF least_row_system_formed
      extension_package_system_formed[unfolded extension_package_system_def], of d t] old
    by (auto simp: extension_package_system_def)
  show ?thesis using step1 step2 step3 step3a step3b step4 step5 step6 step6b step6s step6c step7 by simp
qed

lemma extension_package_old_meaning:
  assumes old: "d\<in>system_definitions package_membership_system"
  shows "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
proof -
  have base: "d\<in>system_definitions extension_readers_base_system"
    by (simp only: extension_readers_base_definitions Un_iff) (rule disjI1, rule old)
  show ?thesis using extension_package_base_meaning[OF base, of t] extension_readers_base_membership[OF old, of t]
    by (rule trans)
qed

lemma extension_package_formation_meaning:
  assumes formation: "d\<in>system_definitions extension_formation_system"
  shows "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_formation_system"
proof -
  have base: "d\<in>system_definitions extension_readers_base_system"
    by (simp only: extension_readers_base_definitions Un_iff) (rule disjI2, rule formation)
  show ?thesis using extension_package_base_meaning[OF base, of t] extension_readers_base_formation[OF formation, of t]
    by (rule trans)
qed

lemma extension_package_base_agreement:
  "systems_agree_on extension_readers_base_system extension_package_system (system_definitions extension_readers_base_system)"
proof -
  have fresh: "d\<notin>system_definitions extension_readers_base_system" if "955\<le>d" for d
    using extension_readers_base_below that by (meson lessThan_iff not_le subsetD)
  show ?thesis
    using fresh[of 955] fresh[of 956] fresh[of 957] fresh[of 958] fresh[of 959] fresh[of 960] fresh[of 961]
      fresh[of 962] fresh[of 963] fresh[of 964] fresh[of 965] fresh[of 966]
    by (simp add: systems_agree_on_added extension_package_system_def least_row_system_def stored_row_system_def
      added_site_system_def bounded_closure_system_def bounded_members_system_def bounded_member_system_def
      source_absences_system_def source_absence_system_def least_environment_system_def extension_rows_system_def
      extension_row_system_def)
qed

lemma extension_package_formation_component:
  "(954,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (954,t)\<in>positive_meaning extension_formation_system"
  by (rule extension_package_formation_meaning) simp

lemma extension_package_components:
  "(26,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
  "(37,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(47,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(77,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (77,t)\<in>positive_meaning package_closure_admission_system"
  "(79,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(80,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(83,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(3,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (3,t)\<in>positive_meaning data_comparison_system"
  "(5,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
proof -
  have pm: "(d,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_membership_system"
    if "d\<in>{3,5,26,37,47,76,77,79,80,83}" for d using that by (intro extension_package_old_meaning) auto
  have pa: "(d,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_admission_system"
    if "d\<in>{26,37,47,76,77}" for d using that by (intro package_membership_previous_meaning) auto
  have closure: "(d,t)\<in>positive_meaning package_admission_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning package_closure_admission_system"
    if "d\<in>{26,47,76}" for d using that by (intro package_admission_previous_meaning) auto
  have comparison: "(3,t)\<in>positive_meaning package_membership_system \<longleftrightarrow>
      (3,t)\<in>positive_meaning data_comparison_system"
    using whole_system_agreement_meaning[OF package_membership_system_formed complete_data_admission_system_formed
        membership_complete_data_agreement, of 3 t]
      whole_system_agreement_meaning[OF keyed_list_system_formed complete_data_admission_system_formed
        whole_agreement_transitive[OF row_values_keyed_agreement row_values_complete_data_agreement], of 3 t]
      keyed_list_previous_meaning[of 3 t] key_absence_base_meaning[of 3 t] bag_comparison_old_meaning[of 3 t]
    by simp
  have selection: "(5,t)\<in>positive_meaning package_membership_system \<longleftrightarrow>
      (5,t)\<in>positive_meaning bag_comparison_system"
    using whole_system_agreement_meaning[OF package_membership_system_formed complete_data_admission_system_formed
        membership_complete_data_agreement, of 5 t]
      whole_system_agreement_meaning[OF keyed_list_system_formed complete_data_admission_system_formed
        whole_agreement_transitive[OF row_values_keyed_agreement row_values_complete_data_agreement], of 5 t]
      keyed_list_previous_meaning[of 5 t] key_absence_base_meaning[of 5 t]
    by simp
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
    "(3,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (3,t)\<in>positive_meaning data_comparison_system"
    "(5,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    using pm[of 3] comparison pm[of 5] selection pm[of 26] pm[of 37] pm[of 47] pm[of 76] pm[of 77] pm[of 79] pm[of 80] pm[of 83]
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
  "((962,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=source_absence_schema"
  "((963,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 962 963"
  "((964,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=added_site_schema"
  "((965,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>least_row_clauses"
  "((966,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>stored_row_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses extension_readers_base_system \<Longrightarrow>
      d\<in>system_definitions extension_readers_base_system"
    for d c S using extension_readers_base_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses extension_readers_base_system"
    if d: "d\<in>{955,956,957,958,959,960,961,962,963,964,965,966}" for d c S
  proof
    assume "((d,c),S)\<in>system_clauses extension_readers_base_system"
    then have "d\<in>system_definitions extension_readers_base_system" by (rule owned)
    from subsetD[OF extension_readers_base_below this] have "d<955" by (simp only: lessThan_iff)
    then show False using d by auto
  qed
  show "((955,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_row_clauses"
    "((956,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 955 956"
    "((957,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=least_environment_schema"
    "((958,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>bounded_member_clauses"
    "((959,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 958 959"
    "((960,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=bounded_closure_schema"
    "((961,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>extension_package_clauses"
    "((962,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=source_absence_schema"
    "((963,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 962 963"
    "((964,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> c=0 \<and> S=added_site_schema"
    "((965,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>least_row_clauses"
    "((966,c),S)\<in>system_clauses extension_package_system \<longleftrightarrow> (c,S)\<in>stored_row_clauses"
    using absent by (auto simp: extension_package_system_def least_row_system_def stored_row_system_def added_site_system_def bounded_closure_system_def bounded_members_system_def
      bounded_member_system_def source_absences_system_def source_absence_system_def least_environment_system_def extension_rows_system_def extension_row_system_def)
qed

interpretation extension_rows_lists: context_list_profile extension_package_system 955 956
  by (rule context_list_profile.intro) (auto simp: extension_package_call extension_package_families)

interpretation bounded_members_lists: context_list_profile extension_package_system 958 959
  by (rule context_list_profile.intro) (auto simp: extension_package_call extension_package_families)

interpretation source_absences_lists: context_list_profile extension_package_system 962 963
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
  "(957,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g a b w c. t=Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term w c) \<and>
    term_formed g \<and> term_formed a \<and> term_formed b \<and> term_formed w \<and> term_formed c \<and>
    (\<exists>L. environment_value_presents L (Pair_Term w c)) \<and>
    (956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system \<and>
    (47,Pair_Term b c)\<in>positive_meaning data_subset_system \<and> (47,Pair_Term c b)\<in>positive_meaning data_subset_system \<and>
    (954,Pair_Term g (Pair_Term (Pair_Term a b) (Payload_Term [])))\<in>positive_meaning extension_formation_system)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((957,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have schema: "S=least_environment_schema" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
    t=Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) (Pair_Term (f 3) (f 4)) \<and>
    (\<exists>L. environment_value_presents L (Pair_Term (f 3) (f 4))) \<and>
    (956,Pair_Term (Pair_Term (f 0) (f 1)) (f 3))\<in>positive_meaning extension_package_system \<and>
    (47,Pair_Term (f 2) (f 4))\<in>positive_meaning data_subset_system \<and> (47,Pair_Term (f 4) (f 2))\<in>positive_meaning data_subset_system \<and>
    (954,Pair_Term (f 0) (Pair_Term (Pair_Term (f 1) (f 2)) (Payload_Term [])))\<in>positive_meaning extension_formation_system"
    using vars conclusion support
    by (auto simp: schema least_environment_schema_def schema_variables_def extension_package_components
      extension_package_formation_component)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g a b w c where t: "t=Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term w c)"
    and formed: "term_formed g" "term_formed a" "term_formed b" "term_formed w" "term_formed c"
    and admitted: "\<exists>L. environment_value_presents L (Pair_Term w c)"
    and rows: "(956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system"
    and sub: "(47,Pair_Term b c)\<in>positive_meaning data_subset_system" "(47,Pair_Term c b)\<in>positive_meaning data_subset_system"
    and formation: "(954,Pair_Term g (Pair_Term (Pair_Term a b) (Payload_Term [])))\<in>positive_meaning extension_formation_system"
    by blast
  let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then w else c"
  have "(957,evaluate_pattern ?f (schema_conclusion least_environment_schema))\<in>positive_meaning extension_package_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed admitted rows sub formation in \<open>auto simp: extension_package_families least_environment_schema_def
        schema_variables_def extension_package_call extension_package_components extension_package_formation_component\<close>)
  then show ?lhs by (simp add: t least_environment_schema_def)
qed

lemma source_absence_raw:
  "(962,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>x y z w. t=Pair_Term x (Pair_Term (Pair_Term y z) w) \<and>
    term_formed x \<and> term_formed y \<and> term_formed z \<and> term_formed w \<and>
    (3,Pair_Term x y)\<in>positive_meaning data_comparison_system)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((962,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have schema: "S=source_absence_schema" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and>
    t=Pair_Term (f 0) (Pair_Term (Pair_Term (f 1) (f 2)) (f 3)) \<and>
    (3,Pair_Term (f 0) (f 1))\<in>positive_meaning data_comparison_system"
    using vars conclusion support
    by (auto simp: schema source_absence_schema_def schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain x y z w where t: "t=Pair_Term x (Pair_Term (Pair_Term y z) w)"
    and formed: "term_formed x" "term_formed y" "term_formed z" "term_formed w"
    and differ: "(3,Pair_Term x y)\<in>positive_meaning data_comparison_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then x else if n=1 then y else if n=2 then z else w"
  have "(962,evaluate_pattern ?f (schema_conclusion source_absence_schema))\<in>positive_meaning extension_package_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed differ in \<open>auto simp: extension_package_families source_absence_schema_def
        schema_variables_def extension_package_call extension_package_components\<close>)
  then show ?lhs by (simp add: t source_absence_schema_def)
qed

lemma bounded_member_raw:
  "(958,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>l g gu gr k x.
    t=Pair_Term (Pair_Term (Pair_Term l (source_root_argument g gu gr)) k) x \<and>
    term_formed l \<and> term_formed g \<and> term_formed gu \<and> term_formed gr \<and> term_formed k \<and> term_formed x \<and>
    ((76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
     (\<exists>lw lb du dr R rest. l=Pair_Term lw lb \<and> x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
       (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
       (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
       (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
       ((83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
        (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((958,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>bounded_member_clauses" using clause by (simp add: extension_package_families)
  then consider "S=bounded_member_added_schema" | "S=bounded_member_package_schema" | "S=bounded_member_closure_schema"
    by (auto simp: bounded_member_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
      term_formed (f 5) \<and> t=Pair_Term (Pair_Term (Pair_Term (f 0) (source_root_argument (f 1) (f 2) (f 3))) (f 4)) (f 5) \<and>
      (76,Pair_Term (Pair_Term (f 0) (f 4)) (Pair_Term (f 5) (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
      using vars conclusion support
      by (auto simp: 1 bounded_member_added_schema_def schema_variables_def extension_package_components)
    then show ?thesis by blast
  next
    case 2
    have "term_formed (f 6) \<and> term_formed (f 7) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and>
      term_formed (f 4) \<and> term_formed (f 5) \<and> term_formed (f 8) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 6) (f 7)) (source_root_argument (f 1) (f 2) (f 3))) (f 4))
        (Pair_Term (f 5) (f 8)) \<and>
      (963,Pair_Term (f 5) (f 7))\<in>positive_meaning extension_package_system \<and>
      term_formed (f 9) \<and> term_formed (f 10) \<and>
      (5,Pair_Term (Pair_Term (f 5) (f 9)) (Pair_Term (f 6) (f 10)))\<in>positive_meaning bag_comparison_system \<and>
      (37,Pair_Term (f 1) (Pair_Term (f 5) (f 9)))\<in>positive_meaning artifact_lookup_system \<and>
      (83,package_subject_argument (f 1) (f 2) (f 3) (Pair_Term (f 5) (f 8)))\<in>positive_meaning package_membership_system"
      using vars conclusion support
      by (auto simp: 2 bounded_member_package_schema_def schema_variables_def extension_package_components)
    then show ?thesis by auto
  next
    case 3
    have "term_formed (f 6) \<and> term_formed (f 7) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and>
      term_formed (f 4) \<and> term_formed (f 5) \<and> term_formed (f 8) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 6) (f 7)) (source_root_argument (f 1) (f 2) (f 3))) (f 4))
        (Pair_Term (f 5) (f 8)) \<and>
      (963,Pair_Term (f 5) (f 7))\<in>positive_meaning extension_package_system \<and>
      term_formed (f 9) \<and> term_formed (f 10) \<and>
      (5,Pair_Term (Pair_Term (f 5) (f 9)) (Pair_Term (f 6) (f 10)))\<in>positive_meaning bag_comparison_system \<and>
      (37,Pair_Term (f 1) (Pair_Term (f 5) (f 9)))\<in>positive_meaning artifact_lookup_system \<and>
      (77,Pair_Term (f 1) (Pair_Term (Pair_Term (f 5) (f 8)) (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      using vars conclusion support
      by (auto simp: 3 bounded_member_closure_schema_def schema_variables_def extension_package_components)
    then show ?thesis by auto
  qed
next
  assume ?rhs
  then obtain l g gu gr k x where t: "t=Pair_Term (Pair_Term (Pair_Term l (source_root_argument g gu gr)) k) x"
    and formed: "term_formed l" "term_formed g" "term_formed gu" "term_formed gr" "term_formed k" "term_formed x"
    and calls: "(76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
     (\<exists>lw lb du dr R rest. l=Pair_Term lw lb \<and> x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
       (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
       (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
       (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
       ((83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
        (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))" by blast
  from calls show ?lhs
  proof
    assume call: "(76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
    let ?f="\<lambda>n::nat. if n=0 then l else if n=1 then g else if n=2 then gu else if n=3 then gr else if n=4 then k else x"
    have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_added_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed call in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t bounded_member_added_schema_def)
  next
    assume "\<exists>lw lb du dr R rest. l=Pair_Term lw lb \<and> x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
       (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
       (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
       (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
       ((83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
        (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system)"
    then obtain lw lb du dr R rest where parts: "l=Pair_Term lw lb" "x=Pair_Term du dr"
      and absent: "(963,Pair_Term du lb)\<in>positive_meaning extension_package_system"
      and row: "term_formed R" "term_formed rest"
        "(5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system"
        "(37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system"
      and given: "(83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
        (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system" by blast
    have pf: "term_formed lw" "term_formed lb" "term_formed du" "term_formed dr" using formed(1,6) parts by simp_all
    let ?f="\<lambda>n::nat. if n=1 then g else if n=2 then gu else if n=3 then gr else if n=4 then k else if n=5 then du
      else if n=6 then lw else if n=7 then lb else if n=8 then dr else if n=9 then R else rest"
    from given show ?thesis
    proof
      assume call: "(83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system"
      have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_package_schema))\<in>positive_meaning extension_package_system"
        by (rule ordinary_positive_valuation_step[where c=1])
          (use formed pf call absent row parts in \<open>auto simp: extension_package_families extension_package_schema_defs
            schema_variables_def extension_package_call extension_package_components\<close>)
      then show ?thesis by (simp add: t parts bounded_member_package_schema_def)
    next
      assume call: "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      have "(958,evaluate_pattern ?f (schema_conclusion bounded_member_closure_schema))\<in>positive_meaning extension_package_system"
        by (rule ordinary_positive_valuation_step[where c=2])
          (use formed pf call absent row parts in \<open>auto simp: extension_package_families extension_package_schema_defs
            schema_variables_def extension_package_call extension_package_components\<close>)
      then show ?thesis by (simp add: t parts bounded_member_closure_schema_def)
    qed
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

lemma added_site_raw:
  "(964,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>l s u r. t=Pair_Term (Pair_Term l s) (Pair_Term u r) \<and>
    term_formed l \<and> term_formed s \<and> term_formed u \<and> term_formed r \<and>
    (\<exists>q. term_formed q \<and> (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (960,Pair_Term (Pair_Term l s) q)\<in>positive_meaning extension_package_system))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((964,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have schema: "S=added_site_schema" using clause by (simp add: extension_package_families)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
    t=Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3)) \<and>
    (79,citation_observation_argument (f 0) (f 2) (f 3) (f 4))\<in>positive_meaning root_family_reading_system \<and>
    (960,Pair_Term (Pair_Term (f 0) (f 1)) (f 4))\<in>positive_meaning extension_package_system"
    using vars conclusion support
    by (auto simp: schema added_site_schema_def schema_variables_def extension_package_components)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain l s u r q where t: "t=Pair_Term (Pair_Term l s) (Pair_Term u r)"
    and formed: "term_formed l" "term_formed s" "term_formed u" "term_formed r" "term_formed q"
    and family: "(79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system"
    and closure: "(960,Pair_Term (Pair_Term l s) q)\<in>positive_meaning extension_package_system" by blast
  let ?f="\<lambda>n::nat. if n=0 then l else if n=1 then s else if n=2 then u else if n=3 then r else q"
  have "(964,evaluate_pattern ?f (schema_conclusion added_site_schema))\<in>positive_meaning extension_package_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed family closure in \<open>auto simp: extension_package_families added_site_schema_def
        schema_variables_def extension_package_call extension_package_components\<close>)
  then show ?lhs by (simp add: t added_site_schema_def)
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
      have lf: "term_formed (f 7)" using vars by (auto simp: 1 extension_added_site_schema_def schema_variables_def)
      have calls: "(957,Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) (f 7))\<in>positive_meaning extension_package_system"
        "(964,Pair_Term (Pair_Term (f 7) (source_root_argument (f 0) (f 5) (f 6))) (Pair_Term (f 3) (f 4)))
          \<in>positive_meaning extension_package_system"
        using support by (auto simp: 1 extension_added_site_schema_def)
      obtain q where q: "term_formed q" "(79,citation_observation_argument (f 7) (f 3) (f 4) q)\<in>positive_meaning root_family_reading_system"
        "(960,Pair_Term (Pair_Term (f 7) (source_root_argument (f 0) (f 5) (f 6))) q)\<in>positive_meaning extension_package_system"
        using calls(2) unfolding added_site_raw by auto
      show ?thesis using base lf calls(1) q by blast
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
    have site: "(964,Pair_Term (Pair_Term l (source_root_argument g gu gr)) (Pair_Term u r))\<in>positive_meaning extension_package_system"
      unfolding added_site_raw using formed parts by auto
    have "(961,evaluate_pattern ?f (schema_conclusion extension_added_site_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed parts site in \<open>auto simp: extension_package_families extension_package_schema_defs
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

lemma stored_row_raw:
  "(966,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g a x. t=Pair_Term (Pair_Term g a) x \<and>
    term_formed g \<and> term_formed a \<and> term_formed x \<and>
    ((47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system \<or>
     (\<exists>gw gb rest. g=Pair_Term gw gb \<and> term_formed rest \<and>
       (5,Pair_Term x (Pair_Term gw rest))\<in>positive_meaning bag_comparison_system)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((966,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>stored_row_clauses" using clause by (simp add: extension_package_families)
  then consider "S=extension_row_added_schema" | "S=stored_row_given_schema" by (auto simp: stored_row_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> t=Pair_Term (Pair_Term (f 0) (f 1)) (f 2) \<and>
      (47,Pair_Term (Pair_Term (f 2) (Payload_Term [])) (f 1))\<in>positive_meaning data_subset_system"
      using vars conclusion support
      by (auto simp: 1 extension_row_added_schema_def schema_variables_def extension_package_components)
    then show ?thesis by blast
  next
    case 2
    have parts: "term_formed (f 0)" "term_formed (f 1)" "term_formed (f 2)" "term_formed (f 3)" "term_formed (f 4)"
      "t=Pair_Term (Pair_Term (Pair_Term (f 0) (f 3)) (f 1)) (f 2)"
      "(5,Pair_Term (f 2) (Pair_Term (f 0) (f 4)))\<in>positive_meaning bag_comparison_system"
      using vars conclusion support
      by (auto simp: 2 stored_row_given_schema_def schema_variables_def extension_package_components)
    have given_row: "\<exists>gw gb rest. Pair_Term (f 0) (f 3)=Pair_Term gw gb \<and> term_formed rest \<and>
        (5,Pair_Term (f 2) (Pair_Term gw rest))\<in>positive_meaning bag_comparison_system"
      using parts(5,7) by blast
    have "term_formed (Pair_Term (f 0) (f 3))" using parts(1,4) by simp
    then show ?thesis using parts(2,3,6) given_row by blast
  qed
next
  assume ?rhs
  then obtain g a x where t: "t=Pair_Term (Pair_Term g a) x" and formed: "term_formed g" "term_formed a" "term_formed x"
    and calls: "(47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system \<or>
     (\<exists>gw gb rest. g=Pair_Term gw gb \<and> term_formed rest \<and>
       (5,Pair_Term x (Pair_Term gw rest))\<in>positive_meaning bag_comparison_system)" by blast
  from calls show ?lhs
  proof
    assume sub: "(47,Pair_Term (Pair_Term x (Payload_Term [])) a)\<in>positive_meaning data_subset_system"
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else x"
    have "(966,evaluate_pattern ?f (schema_conclusion extension_row_added_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed sub in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t extension_row_added_schema_def)
  next
    assume "\<exists>gw gb rest. g=Pair_Term gw gb \<and> term_formed rest \<and>
       (5,Pair_Term x (Pair_Term gw rest))\<in>positive_meaning bag_comparison_system"
    then obtain gw gb rest where g: "g=Pair_Term gw gb" and rf: "term_formed rest"
      and sel: "(5,Pair_Term x (Pair_Term gw rest))\<in>positive_meaning bag_comparison_system" by blast
    have gparts: "term_formed gw" "term_formed gb" using formed(1) g by simp_all
    let ?f="\<lambda>n::nat. if n=0 then gw else if n=1 then a else if n=2 then x else if n=3 then gb else rest"
    have "(966,evaluate_pattern ?f (schema_conclusion stored_row_given_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed gparts rf sel in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t g stored_row_given_schema_def)
  qed
qed

lemma least_row_raw:
  "(965,t)\<in>positive_meaning extension_package_system \<longleftrightarrow> (\<exists>g a b u v R.
    t=Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b u)) (Pair_Term v R) \<and>
    term_formed g \<and> term_formed a \<and> term_formed b \<and> term_formed u \<and> term_formed v \<and> term_formed R \<and>
    (966,Pair_Term (Pair_Term g a) (Pair_Term v R))\<in>positive_meaning extension_package_system \<and>
    (v=u \<or>
     (\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
       (5,Pair_Term (Pair_Term (Pair_Term v k) w) (Pair_Term b r))\<in>positive_meaning bag_comparison_system) \<or>
     (\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
       (5,Pair_Term (Pair_Term (Pair_Term s k) v) (Pair_Term b r))\<in>positive_meaning bag_comparison_system)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((965,c),S)\<in>system_clauses extension_package_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning extension_package_system"
    by (blast dest: extension_package_valuation)
  have family: "(c,S)\<in>least_row_clauses" using clause by (simp add: extension_package_families)
  then consider "S=least_row_site_schema" | "S=least_row_source_schema" | "S=least_row_target_schema"
    by (auto simp: least_row_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 5) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 3) (f 5)) \<and>
      (966,Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 3) (f 5)))\<in>positive_meaning extension_package_system"
      using vars conclusion support by (auto simp: 1 least_row_site_schema_def schema_variables_def)
    then show ?thesis by blast
  next
    case 2
    have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
      term_formed (f 5) \<and> term_formed (f 6) \<and> term_formed (f 7) \<and> term_formed (f 8) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 4) (f 5)) \<and>
      (966,Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 4) (f 5)))\<in>positive_meaning extension_package_system \<and>
      (5,Pair_Term (Pair_Term (Pair_Term (f 4) (f 6)) (f 7)) (Pair_Term (f 2) (f 8)))\<in>positive_meaning bag_comparison_system"
      using vars conclusion support
      by (auto simp: 2 least_row_source_schema_def schema_variables_def extension_package_components)
    then show ?thesis by blast
  next
    case 3
    have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
      term_formed (f 5) \<and> term_formed (f 6) \<and> term_formed (f 7) \<and> term_formed (f 8) \<and>
      t=Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 4) (f 5)) \<and>
      (966,Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 4) (f 5)))\<in>positive_meaning extension_package_system \<and>
      (5,Pair_Term (Pair_Term (Pair_Term (f 6) (f 7)) (f 4)) (Pair_Term (f 2) (f 8)))\<in>positive_meaning bag_comparison_system"
      using vars conclusion support
      by (auto simp: 3 least_row_target_schema_def schema_variables_def extension_package_components)
    then show ?thesis by blast
  qed
next
  assume ?rhs
  then obtain g a b u v R where t: "t=Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b u)) (Pair_Term v R)"
    and formed: "term_formed g" "term_formed a" "term_formed b" "term_formed u" "term_formed v" "term_formed R"
    and row: "(966,Pair_Term (Pair_Term g a) (Pair_Term v R))\<in>positive_meaning extension_package_system"
    and which: "v=u \<or>
     (\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
       (5,Pair_Term (Pair_Term (Pair_Term v k) w) (Pair_Term b r))\<in>positive_meaning bag_comparison_system) \<or>
     (\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
       (5,Pair_Term (Pair_Term (Pair_Term s k) v) (Pair_Term b r))\<in>positive_meaning bag_comparison_system)" by blast
  consider (site) "v=u"
    | (source) k w r where "term_formed k" "term_formed w" "term_formed r"
      "(5,Pair_Term (Pair_Term (Pair_Term v k) w) (Pair_Term b r))\<in>positive_meaning bag_comparison_system"
    | (target) s k r where "term_formed s" "term_formed k" "term_formed r"
      "(5,Pair_Term (Pair_Term (Pair_Term s k) v) (Pair_Term b r))\<in>positive_meaning bag_comparison_system"
    using which by blast
  then show ?lhs
  proof cases
    case site
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then u else R"
    have "(965,evaluate_pattern ?f (schema_conclusion least_row_site_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed row site in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t site least_row_site_schema_def)
  next
    case source
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then u else if n=4 then v
      else if n=5 then R else if n=6 then k else if n=7 then w else r"
    have "(965,evaluate_pattern ?f (schema_conclusion least_row_source_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed row source in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t least_row_source_schema_def)
  next
    case target
    let ?f="\<lambda>n::nat. if n=0 then g else if n=1 then a else if n=2 then b else if n=3 then u else if n=4 then v
      else if n=5 then R else if n=6 then s else if n=7 then k else r"
    have "(965,evaluate_pattern ?f (schema_conclusion least_row_target_schema))\<in>positive_meaning extension_package_system"
      by (rule ordinary_positive_valuation_step[where c=2])
        (use formed row target in \<open>auto simp: extension_package_families extension_package_schema_defs
          schema_variables_def extension_package_call extension_package_components\<close>)
    then show ?thesis by (simp add: t least_row_target_schema_def)
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

lemma binding_collection_list:
  assumes "data_collection_presents (\<lambda>z v. v=binding_data z) B b"
  obtains xs where "set xs=B" "b=data_list_term (map binding_data xs)"
proof -
  obtain xs ts where "set xs=B" "list_all2 (\<lambda>z v. v=binding_data z) xs ts" "b=data_list_term ts"
    using assms unfolding data_collection_presents_def by blast
  then show ?thesis using that by (simp add: list_all2_function)
qed

lemma data_list_elements:
  assumes "term_formed (data_list_term xs)" "self_contained_term (data_list_term xs)"
  shows "data_elements xs"
  using assms by (induction xs) auto

theorem least_environment_sound:
  assumes given: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and holds: "(957,Pair_Term (Pair_Term g (Pair_Term a b)) l)\<in>positive_meaning extension_package_system"
  shows "\<exists>L. environment_value_presents L l \<and> environment_bindings L=B \<and>
    environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
proof -
  obtain w c where l: "l=Pair_Term w c" and admitted: "\<exists>L. environment_value_presents L (Pair_Term w c)"
    and list: "(956,Pair_Term (Pair_Term g a) w)\<in>positive_meaning extension_package_system"
    and sub: "(47,Pair_Term b c)\<in>positive_meaning data_subset_system" "(47,Pair_Term c b)\<in>positive_meaning data_subset_system"
    using holds unfolding least_environment_raw by auto
  obtain L where L: "environment_value_presents L (Pair_Term w c)" using admitted by blast
  obtain xs ts where enum: "set xs=A" "list_all2 environment_artifact_entry_presents xs ts" "a=data_list_term ts"
    using environment_rows_parts(1)[OF rows] unfolding data_collection_presents_def by blast
  have Lrows: "data_collection_presents environment_artifact_entry_presents (environment_artifacts L) w"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings L) c"
    using L unfolding environment_value_rows environment_rows_presents_def by auto
  obtain ys where ys: "set ys=environment_bindings L" "c=data_list_term (map binding_data ys)"
    by (rule binding_collection_list[OF Lrows(2)])
  obtain zs where zs: "set zs=B" "b=data_list_term (map binding_data zs)"
    by (rule binding_collection_list[OF environment_rows_parts(2)[OF rows]])
  have "set (map binding_data zs)=set (map binding_data ys)" using sub ys(2) zs(2) by (auto simp: data_subset_lists)
  then have "binding_data ` B=binding_data ` environment_bindings L" using ys(1) zs(1) by simp
  then have bindings: "environment_bindings L=B" using inj_image_eq_iff[OF binding_data_injective] by auto
  obtain ys' vs where Lenum: "set ys'=environment_artifacts L" "list_all2 environment_artifact_entry_presents ys' vs"
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
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
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
  obtain zs where zs: "set zs=B" "b=data_list_term (map binding_data zs)"
    by (rule binding_collection_list[OF environment_rows_parts(2)[OF rows]])
  have bdata: "data_elements (map binding_data zs)"
    using environment_value_presents_formed[OF present] zs(2) by (intro data_list_elements) simp_all
  have same: "(47,Pair_Term b b)\<in>positive_meaning data_subset_system" using bdata zs(2) by (simp add: data_subset_lists)
  have formation: "(954,Pair_Term g (Pair_Term (Pair_Term a b) (Payload_Term [])))\<in>positive_meaning extension_formation_system"
    unfolding extension_formation_exact using given rows additions ff by (auto simp: octets_formed_def)
  have "(957,Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term ?w b))\<in>positive_meaning extension_package_system"
    unfolding least_environment_raw
    by (intro exI[of _ g] exI[of _ a] exI[of _ b] exI[of _ ?w] exI[of _ b]) (use gf af bf wf present list same formation in auto)
  then show ?thesis using present by blast
qed

text \<open>
  A stored row, read at the given's value and the added rows: a listed added row or a row of the given's artifact
  table as the given's value lists it.
\<close>

theorem stored_row_at_values:
  assumes given: "environment_value_presents E (Pair_Term (data_list_term gs) gb)"
    and rows: "list_all2 environment_artifact_entry_presents xs ts"
  shows "(966,Pair_Term (Pair_Term (Pair_Term (data_list_term gs) gb) (data_list_term ts)) x)
      \<in>positive_meaning extension_package_system \<longleftrightarrow> x\<in>set ts \<or> x\<in>set gs"
proof -
  have gformed: "term_formed (data_list_term gs)" "term_formed gb" "self_contained_term (data_list_term gs)"
    using environment_value_presents_formed[OF given] by simp_all
  have gdata: "data_elements gs" using gformed by (intro data_list_elements) simp_all
  have data: "data_elements ts" using list_all2_members[OF rows] environment_artifact_entry_formed by blast
  have af: "term_formed (data_list_term ts)" using data by (simp add: data_list_term_formed)
  have member: "(47,Pair_Term (Pair_Term x (Payload_Term [])) (data_list_term ts))\<in>positive_meaning data_subset_system \<longleftrightarrow>
      x\<in>set ts" using data_subset_lists[of "[x]" ts] data by auto
  have selection: "(\<exists>rest. term_formed rest \<and>
      (5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system) \<longleftrightarrow> x\<in>set gs"
  proof
    assume "\<exists>rest. term_formed rest \<and> (5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system"
    then have "selected_data_member x (data_list_term gs)" by blast
    then show "x\<in>set gs" by (auto simp: selected_data_member_exact data_list_term_injective)
  next
    assume "x\<in>set gs"
    then have "selected_data_member x (data_list_term gs)" using gdata
      by (auto simp: selected_data_member_exact data_list_term_injective)
    then obtain rest where sel: "(5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system"
      by blast
    have "term_formed rest" using schema_call_formed_target[OF positive_meaning_formed[OF sel]] by simp
    then show "\<exists>rest. term_formed rest \<and>
      (5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system" using sel by blast
  qed
  have xf: "term_formed x" if "x\<in>set ts \<or> x\<in>set gs" using that data gdata by blast
  show ?thesis
  proof
    assume "(966,Pair_Term (Pair_Term (Pair_Term (data_list_term gs) gb) (data_list_term ts)) x)
      \<in>positive_meaning extension_package_system"
    then have "(47,Pair_Term (Pair_Term x (Payload_Term [])) (data_list_term ts))\<in>positive_meaning data_subset_system \<or>
        (\<exists>rest. term_formed rest \<and> (5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system)"
      unfolding stored_row_raw by auto
    then show "x\<in>set ts \<or> x\<in>set gs" using member selection by blast
  next
    assume listed: "x\<in>set ts \<or> x\<in>set gs"
    then have "(47,Pair_Term (Pair_Term x (Payload_Term [])) (data_list_term ts))\<in>positive_meaning data_subset_system \<or>
        (\<exists>rest. term_formed rest \<and> (5,Pair_Term x (Pair_Term (data_list_term gs) rest))\<in>positive_meaning bag_comparison_system)"
      using member selection by blast
    then show "(966,Pair_Term (Pair_Term (Pair_Term (data_list_term gs) gb) (data_list_term ts)) x)
      \<in>positive_meaning extension_package_system"
      unfolding stored_row_raw using gformed af xf[OF listed] by auto
  qed
qed

text \<open>
  A row of the least environment, read at the given's value, the added rows, the added binding rows and the added
  site's use: a stored row, at the site's use or at a source or a target of an added binding row.
\<close>

theorem least_row_at_values:
  assumes given: "environment_value_presents E g" and table: "g=Pair_Term (data_list_term gs) gb"
    and rows: "list_all2 environment_artifact_entry_presents xs ts"
    and bindings: "data_elements (map binding_data zs)" and ukey: "term_formed (use_data_term u)"
  shows "(965,Pair_Term (Pair_Term (Pair_Term g (data_list_term ts))
      (Pair_Term (data_list_term (map binding_data zs)) (use_data_term u))) x)\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (x\<in>set ts \<or> x\<in>set gs) \<and>
    (\<exists>z. environment_artifact_entry_presents z x \<and>
      (fst z=u \<or> (\<exists>k w. ((fst z,k),w)\<in>set zs) \<or> (\<exists>s k. ((s,k),fst z)\<in>set zs)))"
  (is "?lhs \<longleftrightarrow> ?row \<and> ?needed")
proof -
  let ?a="data_list_term ts" and ?b="data_list_term (map binding_data zs)"
  have gf: "term_formed g" using environment_value_presents_formed[OF given] by blast
  have data: "data_elements ts" using list_all2_members[OF rows] environment_artifact_entry_formed by blast
  have af: "term_formed ?a" using data by (simp add: data_list_term_formed)
  have bf: "term_formed ?b" using bindings by (simp add: data_list_term_formed)
  have given': "environment_value_presents E (Pair_Term (data_list_term gs) gb)" using given table by simp
  have gtable: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) (data_list_term gs)"
    using given' unfolding environment_value_rows environment_rows_presents_def by auto
  obtain ys' gs' where genum: "list_all2 environment_artifact_entry_presents ys' gs'" "data_list_term gs=data_list_term gs'"
    using gtable unfolding data_collection_presents_def by blast
  have gsame: "gs'=gs" using genum(2) by (simp add: data_list_term_injective)
  have entry: "\<exists>z. environment_artifact_entry_presents z x" if ?row
    using that list_all2_members[OF rows] list_all2_members[OF genum(1)] gsame by blast
  have selected: "(\<exists>r. (5,Pair_Term y (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<longleftrightarrow>
      y\<in>binding_data ` set zs" for y
    using bindings by (auto simp: selected_data_member_exact data_list_term_injective)
  have binding_row: "(term_formed s \<and> term_formed k \<and> term_formed w \<and> (\<exists>r. term_formed r \<and>
      (5,Pair_Term (Pair_Term (Pair_Term s k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system)) \<longleftrightarrow>
    (\<exists>q j p. ((q,j),p)\<in>set zs \<and> s=use_data_term q \<and> k=Payload_Term j \<and> w=use_data_term p)" for s k w
  proof
    assume "term_formed s \<and> term_formed k \<and> term_formed w \<and> (\<exists>r. term_formed r \<and>
      (5,Pair_Term (Pair_Term (Pair_Term s k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system)"
    then have "Pair_Term (Pair_Term s k) w\<in>binding_data ` set zs" using selected by blast
    then obtain z where zin: "z\<in>set zs" and zeq: "Pair_Term (Pair_Term s k) w=binding_data z" by auto
    obtain q j p where zp: "z=((q,j),p)" by (metis prod.collapse)
    show "\<exists>q j p. ((q,j),p)\<in>set zs \<and> s=use_data_term q \<and> k=Payload_Term j \<and> w=use_data_term p"
      by (intro exI[of _ q] exI[of _ j] exI[of _ p]) (use zin zeq zp in \<open>simp add: binding_data_def\<close>)
  next
    assume "\<exists>q j p. ((q,j),p)\<in>set zs \<and> s=use_data_term q \<and> k=Payload_Term j \<and> w=use_data_term p"
    then obtain q j p where z: "((q,j),p)\<in>set zs" and parts: "s=use_data_term q" "k=Payload_Term j" "w=use_data_term p"
      by blast
    obtain r where sel: "(5,Pair_Term (binding_data ((q,j),p)) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system"
      using selected[of "binding_data ((q,j),p)"] z by blast
    have "term_formed (binding_data ((q,j),p))" using bindings z by auto
    then have fs: "term_formed s" "term_formed k" "term_formed w" using parts by (simp_all add: binding_data_def)
    have rf: "term_formed r" using schema_call_formed_target[OF positive_meaning_formed[OF sel]] by simp
    have "(5,Pair_Term (Pair_Term (Pair_Term s k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system"
      using sel parts by (simp add: binding_data_def)
    then show "term_formed s \<and> term_formed k \<and> term_formed w \<and> (\<exists>r. term_formed r \<and>
      (5,Pair_Term (Pair_Term (Pair_Term s k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system)"
      using fs rf by blast
  qed
  have use_formed: "term_formed (use_data_term v)" for v by simp
  have source: "(\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
      (5,Pair_Term (Pair_Term (Pair_Term (use_data_term v) k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<longleftrightarrow>
    (\<exists>k w. ((v,k),w)\<in>set zs)" for v
    using binding_row[of "use_data_term v"] use_formed[of v] by (blast dest: injD[OF use_data_term_injective])
  have target: "(\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
      (5,Pair_Term (Pair_Term (Pair_Term s k) (use_data_term v)) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<longleftrightarrow>
    (\<exists>s k. ((s,k),v)\<in>set zs)" for v
    using binding_row[of _ _ "use_data_term v"] use_formed[of v] by (blast dest: injD[OF use_data_term_injective])
  show ?thesis
  proof
    assume lhs_holds: ?lhs
    have "\<exists>v R. x=Pair_Term v R \<and>
        (966,Pair_Term (Pair_Term g ?a) (Pair_Term v R))\<in>positive_meaning extension_package_system \<and>
        (v=use_data_term u \<or>
         (\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
           (5,Pair_Term (Pair_Term (Pair_Term v k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<or>
         (\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
           (5,Pair_Term (Pair_Term (Pair_Term s k) v) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system))"
      using lhs_holds unfolding least_row_raw by (auto; blast)
    then obtain v R where x: "x=Pair_Term v R"
      and row: "(966,Pair_Term (Pair_Term g ?a) (Pair_Term v R))\<in>positive_meaning extension_package_system"
      and which: "v=use_data_term u \<or>
         (\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
           (5,Pair_Term (Pair_Term (Pair_Term v k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<or>
         (\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
           (5,Pair_Term (Pair_Term (Pair_Term s k) v) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system)"
      by blast
    have rowx: ?row using row x table by (simp add: stored_row_at_values[OF given' rows])
    obtain z where z: "environment_artifact_entry_presents z x" using entry[OF rowx] by blast
    have vz: "v=use_data_term (fst z)" using z x by (auto simp: environment_artifact_entry_presents_def)
    have needed: "use_data_term (fst z)=use_data_term u \<or> (\<exists>k w. ((fst z,k),w)\<in>set zs) \<or>
        (\<exists>s k. ((s,k),fst z)\<in>set zs)"
      using which by (simp only: vz source target)
    have "fst z=u \<or> (\<exists>k w. ((fst z,k),w)\<in>set zs) \<or> (\<exists>s k. ((s,k),fst z)\<in>set zs)"
      using needed by (auto dest: injD[OF use_data_term_injective])
    then show "?row \<and> ?needed" using rowx z by blast
  next
    assume both: "?row \<and> ?needed"
    then obtain z where z: "environment_artifact_entry_presents z x"
      and needed: "fst z=u \<or> (\<exists>k w. ((fst z,k),w)\<in>set zs) \<or> (\<exists>s k. ((s,k),fst z)\<in>set zs)" by blast
    obtain a' where za: "artifact_value_presents (snd z) a'" "x=Pair_Term (use_data_term (fst z)) a'"
      using z unfolding environment_artifact_entry_presents_def by blast
    have xf: "term_formed (use_data_term (fst z))" "term_formed a'"
      using environment_artifact_entry_formed[OF z] za(2) by simp_all
    have row: "(966,Pair_Term (Pair_Term g ?a) (Pair_Term (use_data_term (fst z)) a'))\<in>positive_meaning extension_package_system"
      using both za(2) table by (simp add: stored_row_at_values[OF given' rows])
    from needed consider (site) "fst z=u" | (source_row) "\<exists>k w. ((fst z,k),w)\<in>set zs"
      | (target_row) "\<exists>s k. ((s,k),fst z)\<in>set zs" by blast
    then have disj: "use_data_term (fst z)=use_data_term u \<or>
        (\<exists>k w r. term_formed k \<and> term_formed w \<and> term_formed r \<and>
          (5,Pair_Term (Pair_Term (Pair_Term (use_data_term (fst z)) k) w) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system) \<or>
        (\<exists>s k r. term_formed s \<and> term_formed k \<and> term_formed r \<and>
          (5,Pair_Term (Pair_Term (Pair_Term s k) (use_data_term (fst z))) (Pair_Term ?b r))\<in>positive_meaning bag_comparison_system)"
      by cases ((rule disjI1, rule arg_cong[where f=use_data_term], assumption),
        (rule disjI2, rule disjI1, rule iffD2[OF source], assumption),
        (rule disjI2, rule disjI2, rule iffD2[OF target], assumption))
    show ?lhs unfolding least_row_raw
      by (rule exI[of _ g], rule exI[of _ ?a], rule exI[of _ ?b], rule exI[of _ "use_data_term u"],
        rule exI[of _ "use_data_term (fst z)"], rule exI[of _ a'], intro conjI)
        (simp_all only: za(2) gf af bf ukey xf row disj)
  qed
qed

subsection \<open>The bounded closure's members and its bound\<close>

lemma source_absences_at_values:
  assumes least: "environment_value_presents L (Pair_Term lw lb)"
    and key: "term_formed (use_data_term v)" "self_contained_term (use_data_term v)"
  shows "(963,Pair_Term (use_data_term v) lb)\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>v)"
proof -
  have collection: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings L) lb"
    using least unfolding environment_value_rows environment_rows_presents_def by auto
  obtain xs where rows: "set xs=environment_bindings L" "lb=data_list_term (map binding_data xs)"
    by (rule binding_collection_list[OF collection])
  have data: "data_elements (map binding_data xs)"
    using environment_value_presents_formed[OF least] rows(2) by (intro data_list_elements) simp_all
  have element: "(962,Pair_Term (use_data_term v) (binding_data z))\<in>positive_meaning extension_package_system \<longleftrightarrow>
      fst (fst z)\<noteq>v" if member: "z\<in>set xs" for z
  proof -
    obtain u k w where z: "z=((u,k),w)" by (metis prod.collapse)
    have formed: "term_formed (use_data_term u)" "term_formed (Payload_Term k)" "term_formed (use_data_term w)"
      "self_contained_term (use_data_term u)"
      using data member z by (auto simp: binding_data_def)
    show ?thesis unfolding source_absence_raw data_comparison_exact
      using formed key z by (auto simp: binding_data_def dest: injD[OF use_data_term_injective])
  qed
  have "(963,Pair_Term (use_data_term v) lb)\<in>positive_meaning extension_package_system \<longleftrightarrow>
      (\<forall>y\<in>set (map binding_data xs). (962,Pair_Term (use_data_term v) y)\<in>positive_meaning extension_package_system)"
    using key by (auto simp: source_absences_lists.exact rows(2) data_list_term_injective)
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>set xs. fst (fst z)\<noteq>v)" using element by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>v)"
  proof
    assume all: "\<forall>z\<in>set xs. fst (fst z)\<noteq>v"
    show "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>v" using all rows(1) by (force simp: binds_slot_def)
  next
    assume all: "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>v"
    show "\<forall>z\<in>set xs. fst (fst z)\<noteq>v"
    proof
      fix z assume "z\<in>set xs"
      then have "binds_slot L (fst (fst z)) (snd (fst z)) (snd z)" using rows(1) by (simp add: binds_slot_def)
      then show "fst (fst z)\<noteq>v" using all by blast
    qed
  qed
  finally show ?thesis .
qed

theorem bounded_member_at_values:
  assumes least: "environment_value_presents L l" and given: "environment_value_presents E g"
    and data: "data_elements ys" and site: "term_formed (source_root_argument g (use_data_term gu) (Payload_Term gr))"
  shows "(958,Pair_Term (Pair_Term (Pair_Term l (source_root_argument g (use_data_term gu) (Payload_Term gr)))
      (data_list_term ys)) x)\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (\<exists>u r p C. x=site_data_term u r \<and> native_definition_at L u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<or>
    (\<exists>d. x=definition_site_value d \<and> native_package_formed E {d} \<and> (\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst d) \<and>
      (\<exists>R. artifact_at L (fst d) R \<and> artifact_at E (fst d) R))"
  (is "?lhs \<longleftrightarrow> ?defined \<or> ?given")
proof -
  let ?formed="\<exists>d. x=definition_site_value d \<and> native_package_formed E {d}"
  have lf: "term_formed l" using environment_value_presents_formed[OF least] by blast
  have kf: "term_formed (data_list_term ys)" using data by (simp add: data_list_term_formed)
  obtain lw lb where l: "l=Pair_Term lw lb" using least unfolding environment_value_rows environment_rows_presents_def by auto
  have added: "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
      \<in>positive_meaning definition_callee_list_system \<longleftrightarrow> ?defined"
    using definition_callee_list_on_values[OF least data, of "[x]"] by simp
  have member: "?formed" if call: "(83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)
      \<in>positive_meaning package_membership_system"
  proof -
    obtain v a d P where parts: "x=definition_site_value d" "native_package_at E v a P" "d\<in>system_definitions P"
      using call[unfolded package_membership_at_source[OF given]] by blast
    have "native_package_formed E {d}" using native_package_support_formed(1)[OF parts(2), of "{d}"] parts(3) by blast
    then show ?thesis using parts(1) by blast
  qed
  have closure: "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system
      \<longleftrightarrow> ?formed"
  proof
    assume "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    then obtain rs where rs: "Pair_Term x (Payload_Term [])=data_list_term (map (\<lambda>d. definition_site_value d) rs)"
      "native_package_formed E (set rs)" by (simp only: package_closure_admission_at_source[OF given]) blast
    have "data_list_term [x]=data_list_term (map (\<lambda>d. definition_site_value d) rs)" using rs(1) by simp
    then have "[x]=map (\<lambda>d. definition_site_value d) rs" by (simp only: data_list_term_injective)
    then obtain d where d: "rs=[d]" "x=definition_site_value d" by (cases rs) auto
    show ?formed using d rs(2) by auto
  next
    assume ?formed
    then obtain d where d: "x=definition_site_value d" "native_package_formed E {d}" by blast
    show "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      using package_closure_admission_on_values[OF given, of "[d]"] d by simp
  qed
  have absence: "(963,Pair_Term (use_data_term (fst d)) lb)\<in>positive_meaning extension_package_system \<longleftrightarrow>
      (\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst d)" if df: "term_formed (definition_site_value d)" for d
  proof -
    have key: "term_formed (use_data_term (fst d))" "self_contained_term (use_data_term (fst d))"
      using df site_data_term_self_contained[of "fst d" "snd d"] by (simp_all add: site_data_term_def)
    show ?thesis by (rule source_absences_at_values[OF least[unfolded l] key])
  qed
  have xf1: "term_formed x" if ?defined using that native_definition_site_data_formed by blast
  have xf2: "term_formed x" if site_form: ?formed
  proof -
    obtain d where d: "x=definition_site_value d" "native_package_formed E {d}" using site_form by blast
    obtain p C where "native_definition_at E (fst d) (snd d) p C"
      using d(2) native_definition_sites_self[of d E] by (auto simp: native_package_formed_def)
    then show ?thesis using d(1) native_definition_site_data_formed by blast
  qed
  have row: "(\<exists>R rest. term_formed R \<and> term_formed rest \<and>
      (5,Pair_Term (Pair_Term (use_data_term v) R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
      (37,Pair_Term g (Pair_Term (use_data_term v) R))\<in>positive_meaning artifact_lookup_system) \<longleftrightarrow>
    (\<exists>R. artifact_at L v R \<and> artifact_at E v R)" for v
  proof
    assume "\<exists>R rest. term_formed R \<and> term_formed rest \<and>
      (5,Pair_Term (Pair_Term (use_data_term v) R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
      (37,Pair_Term g (Pair_Term (use_data_term v) R))\<in>positive_meaning artifact_lookup_system"
    then obtain R rest where sel: "(5,Pair_Term (Pair_Term (use_data_term v) R) (Pair_Term lw rest))
        \<in>positive_meaning bag_comparison_system"
      and look: "(37,Pair_Term g (Pair_Term (use_data_term v) R))\<in>positive_meaning artifact_lookup_system" by blast
    obtain q R1 where q: "use_data_term v=use_data_term q" "artifact_at L q R1" "artifact_value_presents R1 R"
      using conjunct2[OF environment_artifact_selection[OF least[unfolded l]]] sel by blast
    obtain w R2 where w: "use_data_term v=use_data_term w" "artifact_at E w R2" "artifact_value_presents R2 R"
      using artifact_lookup_at_source[OF given] look by blast
    have "q=v" "w=v" using q(1) w(1) by (auto dest: injD[OF use_data_term_injective])
    moreover have "R1=R2" by (rule artifact_value_presents_unique[OF q(3) w(3)])
    ultimately show "\<exists>R. artifact_at L v R \<and> artifact_at E v R" using q(2) w(2) by blast
  next
    assume "\<exists>R. artifact_at L v R \<and> artifact_at E v R"
    then obtain R0 where at: "artifact_at L v R0" "artifact_at E v R0" by blast
    obtain a where member: "selected_data_member (Pair_Term (use_data_term v) a) lw"
      and a: "artifact_value_presents R0 a"
      using conjunct1[OF environment_artifact_selection[OF least[unfolded l]]] at(1) by blast
    from member obtain rest where sel: "(5,Pair_Term (Pair_Term (use_data_term v) a) (Pair_Term lw rest))
      \<in>positive_meaning bag_comparison_system" by blast
    have rf: "term_formed rest" using schema_call_formed_target[OF positive_meaning_formed[OF sel]] by simp
    have af: "term_formed a" using artifact_value_presents_formed[OF a] by simp
    have look: "(37,Pair_Term g (Pair_Term (use_data_term v) a))\<in>positive_meaning artifact_lookup_system"
      using artifact_lookup_at_source[OF given] at(2) a by blast
    show "\<exists>R rest. term_formed R \<and> term_formed rest \<and>
      (5,Pair_Term (Pair_Term (use_data_term v) R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
      (37,Pair_Term g (Pair_Term (use_data_term v) R))\<in>positive_meaning artifact_lookup_system"
      using sel look rf af by blast
  qed
  show ?thesis
  proof
    assume holds: ?lhs
    have xf: "term_formed x" using holds unfolding bounded_member_raw by auto
    have "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<or>
      (\<exists>du dr R rest. x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
        (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
        (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
        (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
        ((83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)\<in>positive_meaning package_membership_system \<or>
         (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))"
      using holds l unfolding bounded_member_raw by auto
    then show "?defined \<or> ?given"
    proof
      assume "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system"
      then show ?thesis using added by blast
    next
      assume "\<exists>du dr R rest. x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
        (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
        (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
        (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
        ((83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)\<in>positive_meaning package_membership_system \<or>
         (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system)"
      then obtain du dr R rest where parts: "x=Pair_Term du dr" "(963,Pair_Term du lb)\<in>positive_meaning extension_package_system"
        and rowcalls: "term_formed R" "term_formed rest"
          "(5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system"
          "(37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system"
        and calls: "(83,package_subject_argument g (use_data_term gu) (Payload_Term gr) x)\<in>positive_meaning package_membership_system \<or>
         (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system" by blast
      obtain d where d: "x=definition_site_value d" "native_package_formed E {d}" using calls member closure by blast
      have du: "du=use_data_term (fst d)" using parts(1) d(1) by (simp add: site_data_term_def)
      have "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst d"
        using absence[of d, OF xf[unfolded d(1)]] parts(2) du by simp
      moreover have "\<exists>R. artifact_at L (fst d) R \<and> artifact_at E (fst d) R"
        using row[of "fst d"] rowcalls du by blast
      ultimately show ?thesis using d by blast
    qed
  next
    assume disjunction: "?defined \<or> ?given"
    have xf: "term_formed x" using disjunction xf1 xf2 by blast
    show ?lhs
    proof (cases ?defined)
      case True
      have "(76,Pair_Term (Pair_Term l (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system" using True added by blast
      then show ?thesis unfolding bounded_member_raw using lf kf xf site by auto
    next
      case False
      then obtain d where d: "x=definition_site_value d" "native_package_formed E {d}"
        "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst d" "\<exists>R. artifact_at L (fst d) R \<and> artifact_at E (fst d) R"
        using disjunction by blast
      obtain R rest where rowcalls: "term_formed R" "term_formed rest"
        "(5,Pair_Term (Pair_Term (use_data_term (fst d)) R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system"
        "(37,Pair_Term g (Pair_Term (use_data_term (fst d)) R))\<in>positive_meaning artifact_lookup_system"
        using row[of "fst d"] d(4) by blast
      have call: "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
        using closure d(1,2) by blast
      have absent: "(963,Pair_Term (use_data_term (fst d)) lb)\<in>positive_meaning extension_package_system"
        using absence[of d, OF xf[unfolded d(1)]] d(3) by simp
      show ?thesis unfolding bounded_member_raw
        using lf kf xf site call absent l d(1) rowcalls by (auto simp: site_data_term_def)
    qed
  qed
qed

theorem bounded_closure_at_values:
  assumes least: "environment_value_presents L l" and given: "environment_value_presents E g"
    and site: "term_formed (source_root_argument g (use_data_term gu) (Payload_Term gr))"
    and apart: "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<notin>environment_uses E"
    and given_rows: "\<forall>u R. artifact_at L u R \<longrightarrow> u\<in>environment_uses E \<longrightarrow> artifact_at E u R"
    and root_uses: "\<forall>d\<in>set ws. fst d\<in>environment_uses L"
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
  then obtain Y0 U where finY0: "finite Y0" and givenY0: "\<forall>y\<in>Y0. native_package_formed E {y}" and finU: "finite U"
    and roots0: "set ws\<subseteq>U\<union>Y0"
    and defined0: "\<forall>d\<in>U. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y0)"
    unfolding bounded_closure_formed_def bounded_package_formed_def by blast
  define Y where "Y={y\<in>Y0. fst y\<in>environment_uses L}"
  have lformed: "environment_formed L" using environment_value_presents_formed[OF least] by blast
  have callee_use: "fst e\<in>environment_uses L"
    if raw: "native_definition_at L (fst d) (snd d) p C" and clause: "(c,S)\<in>C" and dep: "e\<in>schema_dependencies S"
    for d p C c S e
  proof -
    have "(d,e)\<in>native_definition_edges L" using raw clause dep unfolding native_definition_edges_def by blast
    then have edge: "fst d=fst e \<or> (fst d,fst e)\<in>environment_edges L" by (rule native_definition_edge_uses)
    obtain R where "artifact_at L (fst d) R" using raw by (auto simp: native_definition_at_def)
    then have "fst d\<in>environment_uses L" using rel_domI[of "fst d" R] by (simp add: environment_uses_def artifact_at_def)
    then show ?thesis using edge environment_edge_endpoints(2)[OF lformed] by auto
  qed
  have finY: "finite Y" using finY0 by (simp add: Y_def)
  have givenY: "\<forall>y\<in>Y. native_package_formed E {y}" using givenY0 by (simp add: Y_def)
  have roots: "set ws\<subseteq>U\<union>Y" using roots0 root_uses by (auto simp: Y_def)
  have defined: "\<forall>d\<in>U. \<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y)"
  proof
    fix d assume "d\<in>U"
    then obtain p C where raw: "native_definition_at L (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y0" using defined0 by blast
    have "schema_dependencies S\<subseteq>U\<union>Y" if clause: "(c,S)\<in>C" for c S
    proof
      fix e assume dep: "e\<in>schema_dependencies S"
      then have "e\<in>U\<union>Y0" using raw(2) clause by blast
      moreover have "fst e\<in>environment_uses L" by (rule callee_use[OF raw(1) clause dep])
      ultimately show "e\<in>U\<union>Y" by (auto simp: Y_def)
    qed
    then show "\<exists>p C. native_definition_at L (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U\<union>Y)" using raw(1) by blast
  qed
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
      then have formedd: "native_package_formed E {d}" using d(1) givenY by blast
      obtain p C where "native_definition_at E (fst d) (snd d) p C"
        using formedd native_definition_sites_self[of d E] by (auto simp: native_package_formed_def)
      then obtain R where "artifact_at E (fst d) R" by (auto simp: native_definition_at_def)
      then have useE: "fst d\<in>environment_uses E" using rel_domI[of "fst d" R] by (simp add: environment_uses_def artifact_at_def)
      have absent: "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst d" using useE apart by blast
      have inY: "d\<in>Y" using d(1) False by blast
      obtain R' where inL: "artifact_at L (fst d) R'"
        using inY by (auto simp: Y_def environment_uses_def artifact_at_def rel_dom_def)
      have given_row: "\<exists>R. artifact_at L (fst d) R \<and> artifact_at E (fst d) R" using inL given_rows useE by blast
      show ?thesis using bounded_member_at_values[OF least given data site, of x] d(2) formedd absent given_row by blast
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

lemma additions_bindings_apart:
  assumes additions: "environment_additions E A B" and bindings: "environment_bindings L=B"
  shows "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<notin>environment_uses E"
proof (intro allI impI)
  fix u k w assume "binds_slot L u k w"
  then have "((u,k),w)\<in>B" using bindings by (simp add: binds_slot_def)
  then have "u\<in>rel_dom A" using additions_parts(3)[OF additions, of "((u,k),w)"] by simp
  then show "u\<notin>environment_uses E" using additions_parts(2)[OF additions] by blast
qed

text \<open>
  At a least environment of the additions, a row at a given use is the given's row there, and a root read by a
  root family stands at a use of the environment reading it.
\<close>

lemma additions_rows_given:
  assumes additions: "environment_additions E A B" and artifacts: "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
  shows "\<forall>u R. artifact_at L u R \<longrightarrow> u\<in>environment_uses E \<longrightarrow> artifact_at E u R"
proof (intro allI impI)
  fix u R assume at: "artifact_at L u R" and given_use: "u\<in>environment_uses E"
  have "(u,R)\<in>A\<union>environment_artifacts E" using at artifacts by (auto simp: artifact_at_def)
  moreover have "(u,R)\<notin>A" using given_use additions rel_domI[of u R A] by (auto simp: environment_additions_def)
  ultimately show "artifact_at E u R" by (auto simp: artifact_at_def)
qed

lemma root_family_uses:
  assumes family: "native_root_family_at L u r Q"
  shows "\<forall>d\<in>rel_ran Q. fst d\<in>environment_uses L"
proof
  fix d assume "d\<in>rel_ran Q"
  then obtain s where "(s,d)\<in>Q" by (auto simp: rel_ran_def)
  then obtain R M a where "located_at L u a (fst d) (snd d)" using native_root_family_origin[OF family] by blast
  then show "fst d\<in>environment_uses L"
    by (auto dest!: located_at_has_artifact simp: environment_uses_def artifact_at_def rel_dom_def)
qed

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
      using closure[unfolded q] bounded_closure_at_values[OF L(1) gvalue sformed additions_bindings_apart[OF additions L(2)]
        additions_rows_given[OF additions L(3)] root_family_uses[OF Q(1), unfolded Q(2)]] by blast
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
        additions_least_bindings[OF additions] additions_least_artifacts[OF additions] part apart additions ff] by blast
    obtain ds where read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r)
        (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
      and range: "rel_ran Q=set ds" using root_family_reading_total[OF l(1) family] by blast
    have leastrows: "environment_artifacts ?L\<subseteq>A\<union>environment_artifacts E"
      using additions_least_artifacts[OF additions] by auto
    have closure: "(960,Pair_Term (Pair_Term l ?s) (data_list_term (map (\<lambda>d. definition_site_value d) ds)))
        \<in>positive_meaning extension_package_system"
      using bounded_closure_at_values[OF l(1) gvalue sformed
        additions_bindings_apart[OF additions additions_least_bindings[OF additions]]
        additions_rows_given[OF additions leastrows] root_family_uses[OF family, unfolded range]] bounded range by simp
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

lemma extension_readers_base_payloads [lineage_payloads]: "system_payloads extension_readers_base_system\<subseteq>{[]}"
  unfolding extension_readers_base_system_def by (intro lineage_payload_steps lineage_payloads)

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

lemma source_absence_system_payloads [lineage_payloads]: "system_payloads source_absence_system\<subseteq>{[]}"
  unfolding source_absence_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps source_absence_schema_def)

lemma source_absences_system_payloads [lineage_payloads]: "system_payloads source_absences_system\<subseteq>{[]}"
  unfolding source_absences_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

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

lemma added_site_system_payloads [lineage_payloads]: "system_payloads added_site_system\<subseteq>{[]}"
  unfolding added_site_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps added_site_schema_def)

lemma stored_row_system_payloads [lineage_payloads]: "system_payloads stored_row_system\<subseteq>{[]}"
  unfolding stored_row_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps stored_row_clauses_def
    extension_row_added_schema_def stored_row_given_schema_def)

lemma least_row_system_payloads [lineage_payloads]: "system_payloads least_row_system\<subseteq>{[]}"
  unfolding least_row_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps least_row_clauses_def
    least_row_site_schema_def least_row_source_schema_def least_row_target_schema_def)

lemma extension_package_system_payloads [lineage_payloads]: "system_payloads extension_package_system\<subseteq>{[]}"
  unfolding extension_package_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps extension_package_clauses_def
    extension_added_site_schema_def extension_given_site_schema_def)

end
