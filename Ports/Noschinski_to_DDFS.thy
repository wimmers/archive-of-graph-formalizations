theory Noschinski_to_DDFS
  imports 
    "../DDFS"
    Berge_to_DDFS
    Graph_Theory.Stuff
    Graph_Theory.Rtrancl_On
begin

section \<open>Theorems from Digraph_Summary (Noschinski)\<close>

type_synonym 'a awalk = "('a \<times> 'a) list"

fun awalk_verts :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a list" where
    "awalk_verts u [] = [u]"
  | "awalk_verts u ((t, h) # es) = t # awalk_verts h es"


abbreviation awhd :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a" where
  "awhd u p \<equiv> hd (awalk_verts u p)"

abbreviation awlast :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a" where
  "awlast u p \<equiv> last (awalk_verts u p)"

fun cas :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a \<Rightarrow> bool" where
    "cas u [] v = (u = v)"
  | "cas u ((t, h) # es) v = (u = t \<and> cas h es v)"

lemma cas_simp:
  assumes "es \<noteq> []"
  shows "cas u es v \<longleftrightarrow> fst (hd es) = u \<and> cas (snd (hd es)) (tl es) v"
  using assms by (cases es) auto

definition awalk :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "awalk E u p v \<equiv> u \<in> dVs E \<and> set p \<subseteq> E \<and> cas u p v"

definition trail :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "trail E u p v \<equiv> awalk E u p v \<and> distinct p"

definition apath :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "apath E u p v \<equiv> awalk E u p v \<and> distinct (awalk_verts u p)"

lemma awalk_verts_conv:
  "awalk_verts u p = (if p = [] then [u] else map fst p @ [snd (last p)])"
  by (induction p arbitrary: u) auto

lemma awalk_verts_conv':
  assumes "cas u p v"
  shows "awalk_verts u p = (if p = [] then [u] else fst (hd p) # map snd p)"
  using assms by (induction u p v rule: cas.induct) (auto simp: cas_simp)

lemma awalk_verts_non_Nil[simp]:
  "awalk_verts u p \<noteq> []"
  by (simp add: awalk_verts_conv)

lemma
  assumes "cas u p v"
  shows awhd_if_cas: "awhd u p = u" and awlast_if_cas: "awlast u p = v"
  using assms by (induction p arbitrary: u) auto

lemma awalk_verts_in_verts:
  assumes "u \<in> dVs E" "set p \<subseteq> E" "v \<in> set (awalk_verts u p)"
  shows "v \<in> dVs E"
  using assms
  by (induction p arbitrary: u) (auto simp: dVsI, auto dest: dVsI(2))

lemma
  assumes "u \<in> dVs E" "set p \<subseteq> E"
  shows awhd_in_verts: "awhd u p \<in> dVs E"
    and awlast_in_verts: "awlast u p \<in> dVs E"
  using assms by (auto elim: awalk_verts_in_verts)

lemma awalk_conv:
  "awalk E u p v = (set (awalk_verts u p) \<subseteq> dVs E
    \<and> set p \<subseteq> E
    \<and> awhd u p = u \<and> awlast u p = v \<and> cas u p v)"
  unfolding awalk_def using hd_in_set[OF awalk_verts_non_Nil, of u p]
  by (auto intro: awalk_verts_in_verts awhd_if_cas awlast_if_cas simp del: hd_in_set)

lemma awalkE[elim]:
  assumes "awalk E u p v"
  obtains "set (awalk_verts u p) \<subseteq> dVs E" "set p \<subseteq> E" "cas u p  v"
    "awhd u p = u" "awlast u p = v"
  using assms by (auto simp: awalk_conv)

lemma awalk_Nil_iff:
  "awalk E u [] v \<longleftrightarrow> u = v \<and> u \<in> dVs E"
  unfolding awalk_def by auto

lemma hd_in_awalk_verts:
  "awalk E u p v \<Longrightarrow> u \<in> set (awalk_verts u p)"
  by (cases p) auto

lemma awalk_Cons_iff:
  shows "awalk E u (e # es) w \<longleftrightarrow> e \<in> E \<and> fst e = u \<and> awalk E (snd e) es w"
  by (auto simp: awalk_def cas_simp dVsI')

lemmas awalk_simps = awalk_Nil_iff awalk_Cons_iff

lemma arc_implies_awalk:
  "e \<in> E \<Longrightarrow> e = (u, v) \<Longrightarrow> awalk E u [e] v"
  by (simp add: awalk_simps dVsI)

lemma awalkI_apath:
  assumes "apath E u p v" shows "awalk E u p v"
  using assms by (simp add: apath_def)

lemma
  awhd_of_awalk: "awalk E u p v \<Longrightarrow> awhd u p = u" and
  awlast_of_awalk: "awalk E u p v \<Longrightarrow> NOMATCH (awlast u p) v \<Longrightarrow> awlast u p = v"
  unfolding NOMATCH_def
  by auto
lemmas awends_of_awalk[simp] = awhd_of_awalk awlast_of_awalk

lemma cas_append_iff[simp]:
  "cas u (p @ q) v \<longleftrightarrow> cas u p (awlast u p) \<and> cas (awlast u p) q v"
  by (induction u p v rule: cas.induct) auto

lemma cas_ends:
  assumes "cas u p v" "cas u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
  using assms by (induction u p v arbitrary: u u' rule: cas.induct) auto

lemma awalk_ends:
  assumes "awalk E u p v" "awalk E u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
  using assms by (simp add: awalk_def cas_ends)

lemma awalk_ends_eqD:
  assumes "awalk E u p u" "awalk E v p w"
  shows "v = w"
  using awalk_ends[OF assms] by auto

lemma awalk_append_iff[simp]:
  "awalk E u (p @ q) v \<longleftrightarrow> awalk E u p (awlast u p) \<and> awalk E (awlast u p) q v"
  by (auto simp: awalk_def intro: awlast_in_verts)

declare awalkE[rule del]

lemma awalkE'[elim]:
  assumes "awalk E u p v"
  obtains "set (awalk_verts u p) \<subseteq> dVs E" "set p \<subseteq> E" "cas u p v"
    "awhd u p = u" "awlast u p = v" "u \<in> dVs E" "v \<in> dVs E"
proof -
  have "u \<in> set (awalk_verts u p)" "v \<in> set (awalk_verts u p)"
    using assms by (auto simp: hd_in_awalk_verts elim: awalkE)
  then show ?thesis using assms by (auto elim: awalkE intro: that)
qed

lemma awalk_appendI:
  assumes "awalk E u p v"
  assumes "awalk E v q w"
  shows "awalk E u (p @ q) w"
  using assms by auto

lemma cas_takeI:
  assumes "cas u p v" "awlast u (take n p) = v'"
  shows "cas u (take n p) v'"
proof -
  from assms have "cas u (take n p @ drop n p) v" by simp
  with assms show ?thesis unfolding cas_append_iff by simp
qed

lemma awalk_verts_take_conv:
  assumes "cas u p v"
  shows "awalk_verts u (take n p) = take (Suc n) (awalk_verts u p)"
proof -
  from assms have "cas u (take n p) (awlast u (take n p))" by (auto intro: cas_takeI)
  with assms show ?thesis
    by (cases n p rule: nat.exhaust[case_product list.exhaust])
       (auto simp: awalk_verts_conv' take_map simp del: awalk_verts.simps)
qed

lemma awalk_verts_drop_conv:
  assumes "cas u p v"
  shows "awalk_verts u' (drop n p) = (if n < length p then drop n (awalk_verts u p) else [u'])"
  using assms by (auto simp: awalk_verts_conv drop_map)

lemma awalk_decomp_verts:
  assumes cas: "cas u p v" and ev_decomp: "awalk_verts u p = xs @ y  # ys"
  obtains q r where "cas u q y" "cas y r v" "p = q @ r" "awalk_verts u q = xs @ [y]"
    "awalk_verts y r = y # ys"
proof -
  define q r where "q = take (length xs) p" and "r = drop (length xs) p"
  then have p: "p = q @ r" by simp
  moreover from p have "cas u q (awlast u q)" "cas (awlast u q) r v"
    using \<open>cas u p v\<close> by auto
  moreover have "awlast u q = y"
    using q_def and assms by (auto simp: awalk_verts_take_conv)
  moreover have *:"awalk_verts u q = xs @ [awlast u q]"
    using assms q_def by (auto simp: awalk_verts_take_conv)
  moreover from * have "awalk_verts y r = y # ys"
    unfolding q_def r_def using assms by (auto simp: awalk_verts_drop_conv not_less)
  ultimately show ?thesis by (intro that) auto
qed

lemma awalk_not_distinct_decomp:
  assumes "awalk E u p v"
  assumes "\<not>distinct (awalk_verts u p)"
  obtains q r s w where "p = q @ r @ s" 
    "distinct (awalk_verts u q)"
    "0 < length r"
    "awalk E u q w" "awalk E w r w" "awalk E w s v"
proof -
  from assms
  obtain xs ys zs y where
    pv_decomp: "awalk_verts u p = xs @ y # ys @ y # zs"
    and xs_y_props: "distinct xs" "y \<notin> set xs" "y \<notin> set ys"
    using not_distinct_decomp_min_prefix by blast

  obtain q p' where "cas u q y" "p = q @ p'" "awalk_verts u q = xs @ [y]"
    and p'_props: "cas y p' v" "awalk_verts y p' = (y # ys) @ y # zs"
    using assms pv_decomp by - (rule awalk_decomp_verts, auto)
  obtain r s where "cas y r y" "cas y s v" "p' = r @ s"
    "awalk_verts y r = y # ys @ [y]" "awalk_verts y s = y # zs"
    using p'_props by (rule awalk_decomp_verts) auto

  have "p =  q @ r @ s" using \<open>p = q @ p'\<close> \<open>p' = r @ s\<close> by simp
  moreover
  have "distinct (awalk_verts u q)" using \<open>awalk_verts u q = xs @ [y]\<close> xs_y_props by simp
  moreover
  have "0 < length r" using \<open>awalk_verts y r = y # ys @ [y]\<close> by auto
  moreover
  from pv_decomp assms have "y \<in> dVs E" by auto
  then have "awalk E u q y" "awalk E y r y" "awalk E y s v"
    using \<open>awalk E u p v\<close> \<open>cas u q y\<close> \<open>cas y r y\<close> \<open>cas y s v\<close> unfolding \<open>p = q @ r @ s\<close>
    by (auto simp: awalk_def)
  ultimately show ?thesis using that by blast
qed


definition closed_w :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
  "closed_w E p \<equiv> \<exists>u. awalk E u p u \<and> 0 < length p"


text \<open>Eliminating cycles from walks\<close>
fun is_awalk_cyc_decomp :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 
  (('a \<times> 'a) list \<times> ('a \<times> 'a) list \<times> ('a \<times> 'a) list) \<Rightarrow> bool" where
  "is_awalk_cyc_decomp E p (q, r, s) \<longleftrightarrow> p = q @ r @ s
    \<and> (\<exists>u v w. awalk E u q v \<and> awalk E v r v \<and> awalk E v s w)
    \<and> 0 < length r
    \<and> (\<exists>u. distinct (awalk_verts u q))"


definition awalk_cyc_decomp :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) list 
  \<Rightarrow> ('a \<times> 'a) list \<times> ('a \<times> 'a) list \<times> ('a \<times> 'a) list" where
  "awalk_cyc_decomp E p = (SOME qrs. is_awalk_cyc_decomp E p qrs)"


function awalk_to_apath :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "awalk_to_apath E p = (if \<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk E u p v)
    then (let (q,r,s) = awalk_cyc_decomp E p in awalk_to_apath E (q @ s))
    else p)"
  by auto


lemma awalk_cyc_decomp_has_prop:
  assumes "awalk E u p v" and "\<not>distinct (awalk_verts u p)"
  shows "is_awalk_cyc_decomp E p (awalk_cyc_decomp E p)"
proof -
  obtain q r s w where "p = q @ r @ s" "distinct (awalk_verts u q)"
      "0 < length r" "awalk E u q w" "awalk E w r w" "awalk E w s v"
    by (auto intro: awalk_not_distinct_decomp[OF assms])
  then have "\<exists>x. is_awalk_cyc_decomp E p x"
    by (auto intro: exI[where x="(q,r,s)"]) blast
  then show ?thesis unfolding awalk_cyc_decomp_def ..
qed

lemma awalk_cyc_decompE:
  assumes dec: "awalk_cyc_decomp E p = (q,r,s)"
  assumes p_props: "awalk E u p v" "\<not>distinct (awalk_verts u p)"
  obtains "p = q @ r @ s" "distinct (awalk_verts u q)" 
    "\<exists>w. awalk E u q w \<and> awalk E w r w \<and> awalk E w s v" "closed_w E r"
proof
  show "p = q @ r @ s" "distinct (awalk_verts u q)" "closed_w E r"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec
      imageI[of "(snd (last q), _)" "set q" fst]
    by (auto simp: closed_w_def awalk_verts_conv)
  then have "p \<noteq> []" by (auto simp: closed_w_def)

  obtain u' w' v' where obt_awalk: "awalk E u' q w'" "awalk E w' r w'" "awalk E w' s v'"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec by auto
  then have "awalk E u' p v'" 
    using \<open>p = q @ r @ s\<close> by simp
  then have "u = u'" and "v = v'" using \<open>p \<noteq> []\<close> \<open>awalk E u p v\<close> by (auto dest: awalk_ends)
  then have "awalk E u q w'" "awalk E w' r w'" "awalk E w' s v"
    using obt_awalk by auto
  then show "\<exists>w. awalk E u q w \<and> awalk E w r w \<and> awalk E w s v" by auto
qed

termination awalk_to_apath
proof (relation "measure (length \<circ> snd)")
  fix E p qrs rs q r s

  have X: "\<And>x y. closed_w E r \<Longrightarrow> awalk E x r y \<Longrightarrow> x = y"
    unfolding closed_w_def by (blast dest: awalk_ends)

  assume "\<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk E u p v)"
    and **: "qrs = awalk_cyc_decomp E p" "(q, rs) = qrs" "(r, s) = rs"
  then obtain u v where *: "awalk E u p v" "\<not>distinct (awalk_verts u p)"
    by (cases p) auto
  then have "awalk_cyc_decomp E p = (q, r, s)" using ** by simp
  then have "is_awalk_cyc_decomp E p (q, r, s)" using *
    by (auto intro: awalk_cyc_decomp_has_prop elim!: awalk_cyc_decompE simp: closed_w_def)
  then show "((E, q @ s), E, p) \<in> measure (length \<circ> snd)"
    by (auto simp: closed_w_def)
qed simp
declare awalk_to_apath.simps[simp del]

lemma awalk_to_apath_induct[consumes 1, case_names path decomp]:
  assumes awalk: "awalk E u p v"
  assumes dist: "\<And>p. awalk E u p v \<Longrightarrow> distinct (awalk_verts u p) \<Longrightarrow> P p"
  assumes dec: "\<And>p q r s. \<lbrakk>awalk E u p v; awalk_cyc_decomp E p = (q, r, s);
    \<not>distinct (awalk_verts u p); P (q @ s)\<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using awalk
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  then show ?case
  proof (cases "distinct (awalk_verts u p)")
    case True
    then show ?thesis by (auto intro: dist less.prems)
  next
    case False
    obtain q r s where p_cdecomp: "awalk_cyc_decomp E p = (q, r, s)"
      by (cases "awalk_cyc_decomp E p") auto
    then have "is_awalk_cyc_decomp E p (q, r, s)" "p = q @ r @ s"
      using awalk_cyc_decomp_has_prop[OF less.prems(1) False] by auto
    then have "length (q @ s) < length p" "awalk E u (q @ s) v"
      using less.prems by (auto dest!: awalk_ends_eqD)
    then have "P (q @ s)" by (auto intro: less)

    with p_cdecomp False show ?thesis by (auto intro: dec less.prems)
  qed
qed

lemma step_awalk_to_apath:
  assumes awalk: "awalk E u p v"
    and decomp: "awalk_cyc_decomp E p = (q, r, s)"
    and dist: "\<not>distinct (awalk_verts u p)"
  shows "awalk_to_apath E p = awalk_to_apath E (q @ s)"
proof -
  from dist have "\<not>(\<exists>u. distinct (awalk_verts u p))"
    by (auto simp: awalk_verts_conv)
  with awalk and decomp show "awalk_to_apath E p = awalk_to_apath E (q @ s)"
    by (auto simp: awalk_to_apath.simps)
qed

lemma apath_awalk_to_apath:
  assumes "awalk E u p v"
  shows "apath E u (awalk_to_apath E p) v"
  using assms
proof (induction rule: awalk_to_apath_induct)
  case (path p)
  then have "awalk_to_apath E p = p" by (auto simp: awalk_to_apath.simps)
  then show ?case using path by (auto simp: apath_def)
next
  case (decomp p q r s)
  then show ?case using step_awalk_to_apath[of _ _ p _ q r s] by simp
qed

text \<open>Vertex walks\<close>
lemma "awalk_imp_dpath":
  assumes "awalk E u p v" shows "dpath E (awalk_verts u p)"
  using assms
  by (induction p arbitrary: u rule: edges_of_dpath.induct)
     (auto simp: awalk_simps)

text \<open>Reachability\<close>

abbreviation dominates :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<index>_" [100,100] 40) where
  "dominates E u v \<equiv> (u,v) \<in> E"

abbreviation reachable1 :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>+\<index> _" [100,100] 40) where
  "reachable1 E u v \<equiv> (u,v) \<in> E\<^sup>+"

definition reachable :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>*\<index> _" [100,100] 40) where
  "reachable E u v \<equiv> (u,v) \<in> rtrancl_on (dVs E) E"

lemma reachableE[elim]:
  assumes "u \<rightarrow>\<^bsub>E\<^esub> v"
  obtains e where "e \<in> E" "e = (u, v)"
  using assms by auto

lemma adj_in_dVs:
  assumes "u \<rightarrow>\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (auto simp: dVsI)

lemma reachable_refl[intro!, Pure.intro!, simp]: "v \<in> dVs E \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def by auto

lemma reachable_induct[consumes 1, case_names base step]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "u \<in> dVs E \<Longrightarrow> P u"
      "\<And>x y. \<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> x; x \<rightarrow>\<^bsub>E\<^esub> y; P x\<rbrakk> \<Longrightarrow> P y"
  shows "P v"
  using assms unfolding reachable_def by (rule rtrancl_on_induct)

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "v \<in> dVs E \<Longrightarrow> P v"
      "\<And>x y. \<lbrakk>x \<rightarrow>\<^bsub>E\<^esub> y; y \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
    shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct)

lemma reachable_in_dVs:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: adj_in_dVs)

lemma reachable1_in_dVs:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: adj_in_dVs)


lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  unfolding reachable_def
  by (auto intro: rtrancl_consistent_rtrancl_on simp: adj_in_dVs reachable1_in_dVs)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
    and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w" 
  using assms
  unfolding reachable_def
  by (auto dest: rtrancl_on_rtranclI rtranclD)

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

lemma arc_implies_dominates: "e \<in> E \<Longrightarrow> fst e \<rightarrow>\<^bsub>E\<^esub> snd e" by auto

lemma reachable1_awalk:
  "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. awalk E u p v \<and> p \<noteq> [])"
proof
  assume "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v" then show "\<exists>p. awalk E u p v \<and> p \<noteq> []"
    by (induct rule: converse_trancl_induct)
       (auto intro: arc_implies_awalk awalk_appendI)
next
  assume "\<exists>p. awalk E u p v \<and> p \<noteq> []" then obtain p where "awalk E u p v" "p \<noteq> []" by auto
  thus "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  proof (induct p arbitrary: u)
    case (Cons a p)
    then show ?case 
      by (cases "p = []") 
         (auto simp: awalk_simps trancl_into_trancl2 simp del: prod.collapse dest: arc_implies_dominates)
  qed simp
qed

lemma reachable_awalk:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. awalk E u p v)"
proof cases
  assume "u = v"
  have "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> u \<longleftrightarrow> awalk E u [] u" by (auto simp: awalk_Nil_iff reachable_in_dVs)
  then show ?thesis using \<open>u = v\<close> by auto                 
next
  assume "u \<noteq> v"
  then have "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>p. awalk E u p v)" 
    using \<open>u \<noteq> v\<close> unfolding reachable1_awalk by force
  finally show ?thesis .
qed

definition cycle :: "('a \<times> 'a) set \<Rightarrow> 'a awalk \<Rightarrow> bool" where
  "cycle E p \<equiv> \<exists>u. awalk E u p u \<and> distinct (tl (awalk_verts u p)) \<and> p \<noteq> []"

definition subgraph :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "subgraph H G \<equiv> H \<subseteq> G"

lemma subgraphI:
  "H \<subseteq> G \<Longrightarrow> subgraph H G" by (simp add: subgraph_def)

lemma subgraph_dVs: "subgraph H G \<Longrightarrow> dVs H \<subseteq> dVs G"
  by (auto simp: subgraph_def dVs_subset)

lemma subgraph_dVs': "subgraph H G \<Longrightarrow> u \<in> dVs H \<Longrightarrow> u \<in> dVs G"
  by (auto dest: subgraph_dVs)

lemma subgraph_awalk_imp_awalk:
  assumes walk: "awalk H u p v"
  assumes sub: "subgraph H G"
  shows "awalk G u p v"
  using assms by (auto simp: awalk_def subgraph_dVs' subgraph_def)

lemma subgraph_apath_imp_apath:
  assumes path: "apath H u p v"
  assumes sub: "subgraph H G"
  shows "apath G u p v"
  using assms by (auto intro: subgraph_awalk_imp_awalk simp: apath_def)

lemma subgraph_cycle:
  assumes "subgraph H G" "cycle H p" shows "cycle G p"
  using assms
  by (auto intro: subgraph_awalk_imp_awalk simp: cycle_def)

lemma dpathI_subgraph:
  assumes "dpath H p"
  assumes "subgraph H G"
  shows "dpath G p"
  using assms dpath_subset subgraph_def by blast

lemma reachable_mono:
  assumes walk: "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" and sub: "subgraph H G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (meson reachable_awalk subgraph_awalk_imp_awalk)



end