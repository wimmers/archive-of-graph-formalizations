theory DDFS_Ports
  imports 
    "../DDFS"
    "../Undirected_Graphs/summary1"
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
  case 0
  then obtain u v ps where "p = u#v#ps" by (metis Suc_leI Suc_le_length_iff)
  then show ?case by simp
next
  case (Suc i)
  then obtain u v ps where "p = u#v#ps" by (metis Suc_leI Suc_le_length_iff)
  hence "edges_of_dpath (v#ps) ! i = ((v#ps) ! i, (v#ps) ! Suc i)" using Suc.IH Suc.prems by simp
  then show ?case using \<open>p = u#v#ps\<close> by simp
qed

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
  assumes "v = p ! (Suc i)" "Suc (Suc i) < length p"
  obtains u where "(u, v) = edges_of_dpath p ! i"
  using assms by (simp add: edges_of_dpath_index)

thm hd_edges_neq_last
lemma hd_edges_neq_last:
  assumes "(last p, hd p) \<notin> set (edges_of_dpath p)" "hd p \<noteq> last p" "p \<noteq> []"
  shows "hd (edges_of_dpath (last p # p)) \<noteq> last (edges_of_dpath (last p # p))"
  using assms
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    using edges_of_dpath.elims by auto
qed

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
  apply (induction p rule: edges_of_dpath.induct, simp_all)
  using v_in_edge_in_dpath by fastforce

thm distinct_edges_of_paths_cons
lemma distinct_edges_of_dpath_cons:
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path p)"
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
thm append_dpath \<comment> \<open>slightly weaker\<close>

thm edges_of_path_append_2
lemma edges_of_dpath_append_2:
  assumes "p' \<noteq> []"
  shows "edges_of_dpath (p @ p') = edges_of_dpath (p @ [hd p']) @ edges_of_dpath p'"
  using assms
proof (induction p rule: induct_list012)
  case 2
  obtain a p's where "p' = a # p's" using assms list.exhaust_sel by blast
  then show ?case by simp
qed simp_all

thm edges_of_path_append
lemma edges_of_dpath_append: "\<exists>ep. edges_of_dpath (p @ p') = ep @ edges_of_dpath p'"
proof (cases p')
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis using edges_of_dpath_append_2 by blast
qed

thm edges_of_path_append_3
lemma edges_of_dpath_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_dpath (p @ p') = edges_of_dpath p @ edges_of_dpath (last p # p')"
proof -
  from assms
  have "edges_of_dpath (p @ p') = edges_of_dpath (butlast p @ last p # p')"
    by (metis append_Cons append_Nil append_assoc snoc_eq_iff_butlast)
  also have "\<dots> = edges_of_dpath (butlast p @ [last p]) @ edges_of_dpath (last p # p')"
    using edges_of_dpath_append_2 by fastforce
  also have "\<dots> = edges_of_dpath p @ edges_of_dpath (last p # p')"
    by (simp add: assms)
  finally show ?thesis .
qed

thm path_suff path_pref
thm append_dpath_suff append_dpath_pref

thm edges_of_path_rev rev_path_is_path \<comment> \<open>Don't generally hold for digraphs\<close>

thm path_vertex_has_edge
lemma dpath_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e u where "e \<in> set (edges_of_dpath p)" "e = (u, v) \<or> e = (v, u)"
proof -
  obtain i where idef: "v = p ! i" "i < length p" by (metis assms(2) in_set_conv_nth)
  have eodplength': "Suc (length (edges_of_dpath p)) = length p"
    by (metis Suc_diff_1 assms(2) edges_of_dpath_length emptyE length_greater_0_conv list.set(1))
  hence eodplength: "length (edges_of_dpath p) \<ge> 1" using assms(1) by simp

  from idef consider (nil) "i = 0" | (gt) "i > 0" "Suc i < length p" | (last) "Suc i = length p"
    by linarith
  thus ?thesis
  proof cases
    case nil
    hence "edges_of_dpath p ! 0 = (p ! 0, p ! 1)" using edges_of_dpath_index assms(1) by force
    then show ?thesis using nil idef(1) eodplength
      by (metis One_nat_def Suc_le_eq nth_mem that)
  next
    case gt
    then show ?thesis using edges_of_dpath_for_inner idef(1)
      by (metis Suc_less_SucD eodplength' nth_mem that)
  next
    case last
    hence "edges_of_dpath p ! (i - 1) = (p ! (i - 1), p ! i)"
      by (metis Suc_diff_le diff_Suc_1 edges_of_dpath_index eodplength' eodplength idef(2))
    then show ?thesis using last eodplength eodplength' idef(1)
      by (metis One_nat_def Suc_inject Suc_le_lessD diff_less le_eq_less_or_eq nth_mem that)
  qed
qed

thm v_in_edge_in_path_inj
lemma v_in_edge_in_dpath_inj:
  assumes "e \<in> set (edges_of_dpath p)"
  obtains u v where "e = (u, v)"
  by fastforce

thm v_in_edge_in_path_gen
lemma v_in_edge_in_dpath_gen: \<comment> \<open>Not sure if this makes sense.\<close>
  assumes "e \<in> set (edges_of_dpath p)" "e = (u, v)"
  shows "u \<in> set p" "v \<in> set p"
  using assms v_in_edge_in_dpath by simp_all

thm mem_path_Vs
thm path_then_in_Vs

thm edges_of_path_Vs
lemma edges_of_dpath_dVs: "dVs (set (edges_of_dpath p)) \<subseteq> set p"
proof
  fix x
  assume "x \<in> dVs (set (edges_of_dpath p))"
  then obtain u where "(u, x) \<in> set (edges_of_dpath p) \<or> (x, u) \<in> set (edges_of_dpath p)"
    unfolding dVs_def by blast
  thus "x \<in> set p" using v_in_edge_in_dpath by auto
qed

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
proof (induction p rule: induct_list012)
  case (3 x y zs)
  then show ?case apply (auto split: if_splits)
    subgoal using edges_of_dpath.elims by blast
    subgoal by (simp add: Suc_leI)
    done
qed simp_all

thm hd_v_in_hd_e
lemma hd_v_fst_hd_e:
  assumes "length p \<ge> 2"
  shows "hd p = fst (hd (edges_of_dpath p))"
proof -
  obtain a b ps where "p = a # b # ps"
    by (metis Suc_le_length_iff assms numeral_2_eq_2)
  thus ?thesis by simp
qed

thm last_in_edge
lemma last_in_edge:
  assumes "p \<noteq> []"
  shows "\<exists>u. (u, last p) \<in> set (edges_of_dpath (v # p)) \<and> u \<in> set (v # p)"
  using assms
proof (induction p arbitrary: v)
  case (Cons a p)
  then show ?case
  proof (cases p)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    then show ?thesis
      using Cons.IH by fastforce
  qed
qed simp

thm walk_betw_def
term dpath_bet

thm nonempty_path_walk_between
lemma nonempty_dpath_dpath_bet[intro?]:
  assumes "dpath E p" "p \<noteq> []" "hd p = u" "last p = v"
  shows "dpath_bet E p u v"
  using assms
  by blast

thm walk_nonempty
lemma dpath_bet_nonempty:
  assumes "dpath_bet E p u v"
  shows [simp]: "p \<noteq> []"
  using assms by blast

thm walk_between_nonempty_path
lemma dpath_bet_nonempty_dpath[elim]:
  assumes "dpath_bet E p u v"
  shows "dpath E p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms by blast+

thm walk_reflexive
lemma dpath_bet_reflexive:
  assumes "w \<in> dVs E"
  shows "dpath_bet E [w] w w"
  using assms by simp

thm walk_symmetric \<comment> \<open>only for undirected/symmetric graphs\<close>

thm walk_transitive
lemma dpath_bet_transitive:
  assumes "dpath_bet E p u v" "dpath_bet E q v w"
  shows "dpath_bet E (p @ tl q) u w"
  using assms dpath_concat append_is_Nil_conv
  by (metis append_Nil2 append_butlast_last_id hd_Cons_tl hd_append2 last_appendR last_tl)

thm walk_in_Vs
lemma dpath_bet_in_dVs:
  assumes "dpath_bet E p a b"
  shows "set p \<subseteq> dVs E"
  using assms path_then_in_Vs by fast

thm walk_endpoints
lemma dpath_bet_endpoints:
  assumes "dpath_bet E p u v"
  shows [simp]: "u \<in> dVs E"
  and   [simp]: "v \<in> dVs E"
  using assms path_then_in_Vs by fastforce+

thm walk_pref
lemma dpath_bet_pref:
  assumes "dpath_bet E (pr @ [x] @ su) u v"
  shows "dpath_bet E (pr @ [x]) u x"
proof
  show "dpath E (pr @ [x])" using assms append_dpath_pref
    by (metis (full_types) append_eq_appendI)
  show "pr @ [x] \<noteq> [] \<and> hd (pr @ [x]) = u \<and> last (pr @ [x]) = x" using assms
    by (metis \<open>dpath E (pr @ [x])\<close> hd_append snoc_eq_iff_butlast split_dpath)
qed

thm walk_suff
lemma dpath_bet_suff:
  assumes "dpath_bet E (pr @ [x] @ su) u v"
  shows "dpath_bet E (x # su) x v"
  using append_dpath_suff assms by auto

thm edges_are_walks
lemma edges_are_dpath_bet:
  assumes "(v, w) \<in> E"
  shows "dpath_bet E [v, w] v w"
  using assms dVsI1
  by (metis append_butlast_last_id butlast.simps(2) dpath1 dpath_snoc_edge' last.simps list.sel(1) list.simps(3))

thm walk_subset
lemma dpath_bet_subset:
  assumes "E \<subseteq> E'"
  assumes "dpath_bet E p u v"
  shows "dpath_bet E' p u v"
  using assms dpath_subset by blast

thm induct_walk_betw
lemma induct_dpath_bet[case_names path1 path2, consumes 1, induct set: dpath_bet]:
  assumes "dpath_bet E p a b"
  assumes Path1: "\<And>v. v \<in> dVs E \<Longrightarrow> P [v] v v"
  assumes Path2: "\<And>v v' vs b. (v, v') \<in> E \<Longrightarrow> dpath_bet E (v' # vs) v' b \<Longrightarrow> P (v' # vs) v' b \<Longrightarrow> P (v # v' # vs) v b"
  shows "P p a b"
proof -
  have "dpath E p" "p \<noteq> []" "hd p = a" "last p = b" using assms(1) by auto
  thus ?thesis
  proof (induction p arbitrary: a b)
    case dpath0
    then show ?case by simp
  next
    case (dpath1 v dG) \<comment> \<open>how to get \<^term>\<open>dG\<close> "unfixed"?\<close>
    then show ?case using Path1 sorry
  next
    case (dpath2 v v' dG vs)
    then show ?case sorry
  qed
qed
end
