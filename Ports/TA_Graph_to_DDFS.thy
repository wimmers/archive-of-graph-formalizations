theory TA_Graph_to_DDFS
  imports 
    "../DDFS"
    Berge_to_DDFS \<comment> \<open>vertex walk (\<^term>\<open>dpath\<close>)\<close>
    Noschinski_to_DDFS \<comment> \<open>reachability (\<^term>\<open>reachable\<close>)\<close>
begin

lemma dpath_append:
  assumes "dpath E xs" "dpath E ys" "last xs = hd ys"
  shows "dpath E (xs @ tl ys)"
  using assms dpath_concat by fastforce

lemma dpath_append2:
  assumes "dpath E (xs @ [x])" "dpath E (x # ys)"
  shows "dpath E (xs @ x # ys)"
  using assms by (auto dest: dpath_append)

lemmas dpath_appendD1 = append_dpath_pref
lemmas dpath_appendD2 = append_dpath_suff

lemma dpath_appendD3:
  "dpath E (xs @ [x, y]) \<Longrightarrow> dpath E (xs @ [x])"
  by (simp add: dpath_appendD1)

lemma dpath_ConsD:
  "dpath E (x # xs) \<Longrightarrow> dpath E xs"
  by (auto dest: tl_dpath_is_dpath)

lemmas dpathD = dpath_ConsD dpath_appendD1 dpath_appendD2

lemma dpath_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "dpath E p"  "P []" "(\<And>x. P [x])"
    "\<And>y x xs. (y, x) \<in> E \<Longrightarrow> dpath E (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y, x])"
  shows "P p"
  using assms(1)
proof (induction rule: rev_induct)
  case Nil
  then show ?case by (simp add: assms)
next
  case (snoc x xs)
  then show ?case
    by (cases xs rule: rev_cases) (auto intro!: assms simp add: dpath_snoc_edge_2 dpath_appendD1)
qed

lemma dpath_append_single:
  assumes "dpath E p" "(last p, x) \<in> E"
  shows "dpath E (p @ [x])"
  using assms
  by (auto intro!: append_dpath dest: dVsI)

lemmas dpath_decomp = dpath_appendD1 dpath_appendD2 dpath_append_edge

lemma dpath_rotate:
  assumes "dpath E (x # xs @ y # ys @ [x])"
  shows "dpath E (y # ys @ x # xs @ [y])"
proof -
  from dpath_decomp[of E "x # xs" "y # ys @ [x]"] assms have
    "dpath E (x # xs)" "dpath E (y # ys @ [x])" "(last (x # xs), y) \<in> E"
    by auto
  then have "dpath E (x # xs @ [y])"
    by (auto dest: dpath_append_single)
  from dpath_append[OF \<open>dpath E (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma dpath_bet_nonempty'[simp]: "\<not> dpath_bet E [] u v" 
  unfolding dpath_bet_def by simp

lemma dpath_ConsE: 
  assumes "dpath E (a # p)" "p \<noteq> []"
  obtains e where "e \<in> E" "e = (a, hd p)" "dpath E p"
  using assms
  by (metis dpath_2 hd_Cons_tl)

lemma dpath_reachable:
  "p \<noteq> [] \<Longrightarrow> dpath E p \<Longrightarrow> hd p \<rightarrow>\<^sup>*\<^bsub>E\<^esub> last p"
  by (induction p rule: list_nonempty_induct)
     (auto elim!: dpath_ConsE simp: reachable_def converse_rtrancl_on_into_rtrancl_on dVsI)

lemma dpath_reachable':
  "dpath E p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> hd p = u \<Longrightarrow> last p = v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  by (auto dest: dpath_reachable)

lemma dpathI: "(x, hd p) \<in> E \<Longrightarrow> dpath E p \<Longrightarrow> dpath E (x#p)" 
  by (induction p) (auto simp: dVsI)

lemma reachable_dpath:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "\<exists>p. hd p = u \<and> last p = v \<and> dpath E p \<and> p \<noteq> []"
  using assms
  apply induction
   apply force
  apply clarsimp
  subgoal for x p
    by (auto intro!: exI[where x="x#p"] dpathI)
  done

lemma reachable_dpath_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. hd p = u \<and> last p = v \<and> dpath E p \<and> p \<noteq> [])"
  by (auto simp: dpath_reachable reachable_dpath)

lemma dpath_reachable1:
  "dpath E (u # p @ [v]) \<Longrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  by (induction p arbitrary: u) (auto simp add: trancl_into_trancl2)

lemma reachable1_dpath:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "\<exists>p. dpath E (u # p @ [v])"
proof -
  from assms obtain w where "u \<rightarrow>\<^bsub>E\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    by (meson converse_tranclE reachable1_in_dVs(2) reachable1_reachable reachable_refl)
  from reachable_dpath[OF this(2)] obtain p where *: "hd p = w" "last p = v" "dpath E p" "p \<noteq> []"
    by auto
  then obtain p' where [simp]: "p = p' @ [v]"
    by (auto intro!: append_butlast_last_id[symmetric])
  with \<open>u \<rightarrow>\<^bsub>E\<^esub> w\<close> * show ?thesis
    by (auto intro: dpathI)
qed

lemma reachable1_dpath_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. dpath E (u # p @ [v]))"
  by (auto simp: dpath_reachable1 reachable1_dpath)

lemma reachable_dpath_iff2:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (u = v \<and> u \<in> dVs E \<or> (\<exists>p. dpath E (u # p @ [v])))"
  by (auto dest: reachable1_dpath simp: reachable_in_dVs dpath_reachable1 reachable1_reachable)

lemma dpath_remove_cycleE:
  assumes "dpath E (u # p @ [v])"
  obtains p' where "dpath E (u # p' @ [v])" 
    "distinct p'" "u \<notin> set p'" "v \<notin> set p'" "set p' \<subseteq> set p"
  using assms
proof (induction "length p" arbitrary: p rule: less_induct)
  case less
  note prems = less.prems(2) and intro = less.prems(1) and IH = less.hyps
  consider
    "distinct p" "u \<notin> set p" "v \<notin> set p" | "u \<in> set p" | "v \<in> set  p" | "\<not> distinct p" by auto
  then consider (goal) ?case
    | (a) as bs where "p = as @ u # bs" | (b) as bs where "p = as @ v # bs"
    | (between) x as bs cs where "p = as @ x # bs @ x # cs"
    using prems
    by (cases, auto dest: not_distinct_decomp split_list intro: intro)
  then show ?case
  proof cases
    case a
    with prems show ?thesis
      by - (rule IH[where p = "bs"], auto 4 3 intro: intro dest: dpathD)
  next
    case b
    with prems have "dpath E (u # as @ v # [] @ (bs @ [v]))" by simp
    then have "dpath E (u # as @ [v])" by (auto simp: dpath_appendD1)
    with b show ?thesis
      by - (rule IH[where p = "as"], auto 4 3 intro: intro)
  next
    case between
    with prems have expanded: "dpath E ((u # as @ x # bs) @ x # cs @ [v])" by simp
    then have xv: "dpath E (x # cs @ [v])" by (rule dpath_appendD2)
    have ux: "dpath E ((u # as) @ [x])" using dpath_appendD1 expanded by force
    with xv have "dpath E ((u # as) @ x # cs @ [v])"
      using dpath_append2[OF ux xv] by auto
    with between show ?thesis
      by - (rule IH[where p = "as @ x # cs"], auto 4 3 intro: intro)
  qed
qed

lemmas subgraph_reachable = reachable_mono
lemma subgraph_reachable1:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  using assms
  by (simp add: subgraph_def trancl_mono)

end