theory Berge_to_DDFS
  imports 
    AGF.DDFS
    AGF.Berge
begin

term edges_of_path
fun edges_of_dpath where
"edges_of_dpath [] = []" |
"edges_of_dpath [v] = []" |
"edges_of_dpath (v#v'#l) = (v, v') # edges_of_dpath (v'#l)"

section\<open>Theorems from summary1 (Berge)\<close>
thm path_ball_edges
lemma dpath_ball_edges: "dpath E p \<Longrightarrow> b \<in> set (edges_of_dpath p) \<Longrightarrow> b \<in> E"
  by (induction p rule: edges_of_dpath.induct, auto)

thm edges_of_path_index
lemma edges_of_dpath_index:
  "Suc i < length p \<Longrightarrow> edges_of_dpath p ! i = (p ! i, p ! Suc i)"
proof (induction i arbitrary: p)
  case (Suc i)
  then obtain u v ps where "p = u#v#ps" by (auto dest!: Suc_leI simp: Suc_le_length_iff)
  hence "edges_of_dpath (v#ps) ! i = ((v#ps) ! i, (v#ps) ! Suc i)" using Suc.IH Suc.prems by simp
  then show ?case using \<open>p = u#v#ps\<close> by simp
qed (auto dest!: Suc_leI simp: Suc_le_length_iff)

thm edges_of_path_length
lemma edges_of_dpath_length: "length (edges_of_dpath p) = length p - 1"
  by (induction p rule: edges_of_dpath.induct, auto)


thm edges_of_path_for_inner
text \<open>With the given assumptions we can only obtain an outgoing edge from \<^term>\<open>v\<close>.\<close>
lemma edges_of_dpath_for_inner:
  assumes "v = p ! i" "Suc i < length p"
  obtains w where "(v, w) = edges_of_dpath p ! i"
  by (simp add: assms edges_of_dpath_index)


text \<open>For an incoming edge we need an additional assumption (\<^term>\<open>i > 0\<close>).\<close>
lemma edges_of_dpath_for_inner':
  assumes "v = p ! (Suc i)" "Suc i < length p"
  obtains u where "(u, v) = edges_of_dpath p ! i"
  using assms by (simp add: edges_of_dpath_index)

thm hd_edges_neq_last
lemma hd_edges_neq_last:
  assumes "(last p, hd p) \<notin> set (edges_of_dpath p)" "hd p \<noteq> last p" "p \<noteq> []"
  shows "hd (edges_of_dpath (last p # p)) \<noteq> last (edges_of_dpath (last p # p))"
  using assms
  by (induction p) (auto elim: edges_of_dpath.elims)

thm Vs_subset
lemma dVs_subset:
  assumes "E \<subseteq> E'"
  shows "dVs E \<subseteq> dVs E'"
  using assms
  unfolding dVs_def
  by blast

thm path_subset
lemma dpath_subset:
  assumes "dpath E p" "E \<subseteq> E'"
  shows "dpath E' p"
  using assms dVs_subset
  by (induction, auto)

thm path_edges_of_path_refl
lemma dpath_edges_of_dpath_refl: "length p \<ge> 2 \<Longrightarrow> dpath (set (edges_of_dpath p)) p"
proof (induction p rule: edges_of_dpath.induct)
  case (3 v v' l)
  thus ?case
    by (cases l) (auto intro: dpath_subset simp add: dpath2 dVs_def)
qed simp_all


thm v_in_edge_in_path
lemma v_in_edge_in_dpath: 
  assumes "(u, v) \<in> set (edges_of_dpath p)"
  shows "u \<in> set p" "v \<in> set p"
  using assms
  by (induction p rule: edges_of_dpath.induct, auto)

thm distinct_edges_of_vpath
lemma distinct_edges_of_dpath:
  assumes "distinct p"
  shows "distinct (edges_of_dpath p)"
  using assms
  by (induction p rule: edges_of_dpath.induct, auto dest: v_in_edge_in_dpath)

thm distinct_edges_of_paths_cons
lemma distinct_edges_of_dpath_cons:
  assumes "distinct (edges_of_dpath (v # p))"
  shows "distinct (edges_of_dpath p)"
  using assms
  by (cases p; simp)

thm tl_path_is_path
lemma tl_dpath_is_dpath: "dpath E p \<Longrightarrow> dpath E (tl p)"
  by (induction p rule: dpath.induct; simp)


thm path_concat
lemma dpath_concat:
  assumes "dpath E p" "dpath E q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "dpath E (p @ tl q)"
  using assms
  by (induction) (simp_all add: tl_dpath_is_dpath)

thm path_append
thm append_dpath

thm edges_of_path_append_2
lemma edges_of_dpath_append_2:
  assumes "p' \<noteq> []"
  shows "edges_of_dpath (p @ p') = edges_of_dpath (p @ [hd p']) @ edges_of_dpath p'"
  using assms
  by (induction p rule: induct_list012, auto intro: list.exhaust[of p'])


thm edges_of_path_append
lemma edges_of_dpath_append: obtains ep where "edges_of_dpath (p @ p') = ep @ edges_of_dpath p'"
  by (cases "p' = []") (auto dest: edges_of_dpath_append_2)

lemma append_butlast_last_cancel: "p \<noteq> [] \<Longrightarrow> butlast p @ last p # p' = p @ p'"
  by simp

thm edges_of_path_append_3
lemma edges_of_dpath_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_dpath (p @ p') = edges_of_dpath p @ edges_of_dpath (last p # p')"
  using assms
  by (auto simp flip: append_butlast_last_cancel simp: edges_of_dpath_append_2)

thm path_suff path_pref
thm append_dpath_suff append_dpath_pref

thm edges_of_path_rev rev_path_is_path \<comment> \<open>Don't generally hold for digraphs\<close>

thm path_vertex_has_edge
lemma dpath_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e u where "e \<in> set (edges_of_dpath p)" "e = (u, v) \<or> e = (v, u)"
proof -
  obtain i where idef: "v = p ! i" "i < length p" 
    using assms(2) by (auto simp: in_set_conv_nth)
  have eodplength': "Suc (length (edges_of_dpath p)) = length p"
    using assms(1) by (auto simp: edges_of_dpath_length)
  hence eodplength: "length (edges_of_dpath p) \<ge> 1" using assms(1) by simp

  from idef consider (nil) "i = 0" | (gt) "i > 0" "Suc i < length p" | (last) "Suc i = length p"
    by linarith
  thus ?thesis
  proof cases
    case nil
    hence "edges_of_dpath p ! 0 = (p ! 0, p ! 1)" using edges_of_dpath_index assms(1) by force
    then show ?thesis using that nil idef eodplength
      by (force simp: in_set_conv_nth)
  next
    case gt
    then obtain w where w: "(v, w) = edges_of_dpath p ! i"
      by (auto elim: edges_of_dpath_for_inner[OF idef(1) gt(2)])
    have "i < length (edges_of_dpath p)"
      using eodplength' gt(2) by auto
    then show ?thesis using that w[symmetric] nth_mem by blast
  next
    case last
    then obtain w where w: "(w, v) = edges_of_dpath p ! (i - 1)"
      using edges_of_dpath_for_inner'[of v p "i - 1"] eodplength' eodplength
      by (auto simp: idef)
    have "i - 1 < length (edges_of_dpath p)"
      using eodplength eodplength' last by linarith
    then show ?thesis using that w[symmetric] nth_mem by blast
  qed
qed


thm v_in_edge_in_path_inj
lemma v_in_edge_in_dpath_inj:
  assumes "e \<in> set (edges_of_dpath p)"
  obtains u v where "e = (u, v)"
  by fastforce

thm v_in_edge_in_path_gen
lemma v_in_edge_in_dpath_gen:
  assumes "e \<in> set (edges_of_dpath p)" "e = (u, v)"
  shows "u \<in> set p" "v \<in> set p"
  using assms v_in_edge_in_dpath by simp_all

thm mem_path_Vs
thm path_then_in_Vs

thm edges_of_path_Vs
lemma edges_of_dpath_dVs: "dVs (set (edges_of_dpath p)) \<subseteq> set p"
  by (auto intro: v_in_edge_in_dpath simp: dVs_def)

thm path_edges_subset
lemma dpath_edges_subset:
  assumes "dpath E p"
  shows "set (edges_of_dpath p) \<subseteq> E"
  using assms
  by (induction, simp_all)

thm last_v_in_last_e
lemma last_v_snd_last_e:
  assumes "length p \<ge> 2"
  shows "last p = snd (last (edges_of_dpath p))" \<comment> \<open>is this the best formulation for this?\<close>
  using assms
  by (induction p rule: induct_list012) 
     (auto split: if_splits elim: edges_of_dpath.elims simp: Suc_leI)

thm hd_v_in_hd_e
lemma hd_v_fst_hd_e:
  assumes "length p \<ge> 2"
  shows "hd p = fst (hd (edges_of_dpath p))"
  using assms
  by (auto dest: Suc_leI simp: Suc_le_length_iff numeral_2_eq_2)

thm last_in_edge
lemma last_in_edge:
   "p \<noteq> [] \<Longrightarrow> \<exists>u. (u, last p) \<in> set (edges_of_dpath (v # p)) \<and> u \<in> set (v # p)"
  by (induction p arbitrary: v) auto

thm edges_of_path_append_subset
lemma edges_of_dpath_append_subset:
  shows "set (edges_of_dpath p') \<subseteq> set (edges_of_dpath (p @ p'))"
  by (auto intro: edges_of_dpath_append[of p p'])

thm walk_betw_def
term dpath_bet

thm nonempty_path_walk_between
lemma nonempty_dpath_dpath_bet[intro?]:
  assumes "dpath E p" "p \<noteq> []" "hd p = u" "last p = v"
  shows "dpath_bet E p u v"
  using assms
  unfolding dpath_bet_def
  by blast

thm walk_nonempty
lemma dpath_bet_nonempty:
  assumes "dpath_bet E p u v"
  shows [simp]: "p \<noteq> []"
  using assms 
  unfolding dpath_bet_def by blast

thm walk_between_nonempty_path
lemma dpath_bet_nonempty_dpath[elim]:
  assumes "dpath_bet E p u v"
  shows "dpath E p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms 
  unfolding dpath_bet_def by blast+

thm walk_reflexive
lemma dpath_bet_reflexive:
  assumes "w \<in> dVs E"
  shows "dpath_bet E [w] w w"
  using assms 
  unfolding dpath_bet_def by simp

thm walk_symmetric \<comment> \<open>only for undirected/symmetric graphs\<close>

lemma singleton_hd_last: "q \<noteq> [] \<Longrightarrow> tl q = [] \<Longrightarrow> hd q = last q"
  by (cases q) simp_all

thm walk_transitive
lemma dpath_bet_transitive:
  assumes "dpath_bet E p u v" "dpath_bet E q v w"
  shows "dpath_bet E (p @ tl q) u w"
  using assms
  unfolding dpath_bet_def
  by (auto intro: dpath_concat simp: last_append singleton_hd_last last_tl)

thm walk_in_Vs
lemma dpath_bet_in_dVs:
  assumes "dpath_bet E p a b"
  shows "set p \<subseteq> dVs E"
  using assms path_then_in_Vs
  unfolding dpath_bet_def by fast

thm walk_endpoints
lemma dpath_bet_endpoints:
  assumes "dpath_bet E p u v"
  shows [simp]: "u \<in> dVs E"
  and   [simp]: "v \<in> dVs E"
  using assms path_then_in_Vs
  unfolding dpath_bet_def by fastforce+

thm walk_pref
lemma dpath_bet_pref:
  assumes "dpath_bet E (pr @ [x] @ su) u v"
  shows "dpath_bet E (pr @ [x]) u x"
  using assms
  unfolding dpath_bet_def
  by (auto simp: append_dpath_pref) (simp add: hd_append)

thm walk_suff
lemma dpath_bet_suff:
  assumes "dpath_bet E (pr @ [x] @ su) u v"
  shows "dpath_bet E (x # su) x v"
  using append_dpath_suff assms 
  unfolding dpath_bet_def by auto

thm edges_are_walks
lemma edges_are_dpath_bet:
  assumes "(v, w) \<in> E"
  shows "dpath_bet E [v, w] v w"
  using assms dVsI
  unfolding dpath_bet_def
  by fastforce

thm walk_subset
lemma dpath_bet_subset:
  assumes "E \<subseteq> E'"
  assumes "dpath_bet E p u v"
  shows "dpath_bet E' p u v"
  using assms dpath_subset 
  unfolding dpath_bet_def by blast

thm induct_walk_betw
lemma induct_dpath_bet[case_names path1 path2, consumes 1, induct set: dpath_bet]:
  assumes "dpath_bet E p a b"
  assumes Path1: "\<And>v. v \<in> dVs E \<Longrightarrow> P E [v] v v"
  assumes Path2: "\<And>v v' vs b. (v, v') \<in> E \<Longrightarrow> dpath_bet E (v' # vs) v' b \<Longrightarrow> P E (v' # vs) v' b \<Longrightarrow> P E (v # v' # vs) v b"
  shows "P E p a b"
proof -
  have "dpath E p" "p \<noteq> []" "hd p = a" "last p = b" using assms(1) by auto
  thus ?thesis
  proof (induction p arbitrary: a b)
    case dpath0
    then show ?case by simp
  next
    case dpath1
    then show ?case using Path1 by fastforce
  next
    case (dpath2 v v' vs a b)
    then have "dpath_bet E (v' # vs) v' b"
      by (simp add: dpath2.hyps(1) dpath_bet_def)
    then show ?case using dpath2 Path2
      by auto
  qed
qed

end
