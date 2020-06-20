theory Mitja_to_DDFS
  imports 
    TA_Graph_to_DDFS \<comment> \<open>includes all existing ports\<close>
    "../Undirected_Graphs/Mitja/Misc"
begin

text \<open>A walk in the Mitja representation corresponds to \<^term>\<open>dpath_bet\<close> in DDFS.\<close>

abbreviation closed_dpath_bet :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a  \<Rightarrow> bool" where
  "closed_dpath_bet E c v \<equiv> dpath_bet E c v v \<and> Suc 0 < length c"

lemma edge_iff_dpath_bet: "(u, v) \<in> E = dpath_bet E [u, v] u v"
  by (auto simp: edges_are_dpath_bet dpath_bet_def dVsI)

lemma "v \<in> dVs E \<Longrightarrow> dpath_bet E [v] v v"
  sorry

lemma dpath_bet_in_vertices: "dpath_bet E p u v \<Longrightarrow> w \<in> set p \<Longrightarrow> w \<in> dVs E"
  by (auto intro: path_then_in_Vs)

lemma "dpath_bet E p u v \<Longrightarrow> u \<in> dVs E"
  sorry

lemma dpath_bet_hd_neq_last_implies_edges_nonempty:
  assumes "dpath_bet E p u v"
  assumes "u \<noteq> v"
  shows "E \<noteq> {}"
  using assms
  by (induction p) (auto dest: path_then_edge)

lemma dpath_bet_edges_in_edges: "dpath_bet E p u v \<Longrightarrow> set (edges_of_dpath p) \<subseteq> E"
  by (simp add: dpath_bet_def dpath_edges_subset)

lemma dpath_bet_prefix_is_dpath_bet:
  assumes "p \<noteq> []"
  assumes "dpath_bet E (p @ q) u v"
  shows "dpath_bet E p u (last p)"
  using assms
  by (auto simp: dpath_bet_def dest: dpath_appendD1)

lemma dpath_bet_suffix_is_dpath_bet:
  assumes "q \<noteq> []"
  assumes "dpath_bet E (p @ q) u v"
  shows "dpath_bet E q (hd q) v"
  using assms
  by (auto simp: dpath_bet_def dest: dpath_appendD2)

lemma
  assumes "dpath_bet E p u v"
  assumes "dpath_bet E q v w"
  shows "dpath_bet E (p @ tl q) u w"
  sorry

lemma dpath_bet_append_append_is_dpath_bet:
  assumes "dpath_bet E p u v"
  assumes "dpath_bet E q v w"
  assumes "dpath_bet E r w x"
  shows "dpath_bet E (p @ tl q @ tl r) u x"
  using assms
  by (auto dest: dpath_bet_transitive)

lemma 
  assumes "p \<noteq> []"
  shows "edges_of_dpath (p @ q) = edges_of_dpath p @ edges_of_dpath ([last p] @ q)"
  using assms
  by (simp add: edges_of_dpath_append_3)

lemma
  assumes "q \<noteq> []"
  shows "edges_of_dpath (p @ q) = edges_of_dpath (p @ [hd q]) @ edges_of_dpath q"
  sorry

fun is_dpath_bet_vertex_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> bool" where
  "is_dpath_bet_vertex_decomp E p v (q, r) \<longleftrightarrow> p = q @ tl r \<and> (\<exists>u w. dpath_bet E q u v \<and> dpath_bet E r v w)"

definition dpath_bet_vertex_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list" where
  "dpath_bet_vertex_decomp E p v \<equiv> SOME qr. is_dpath_bet_vertex_decomp E p v qr"


lemma dpath_bet_vertex_decompE:
  assumes p_dpath: "dpath_bet E p u v"
  assumes p_decomp: "p = xs @ y # ys"
  obtains q r where
    "p = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "dpath_bet E q u y"
    "dpath_bet E r y v"
  using assms
  by (simp add: dpath_bet_pref split_dpath)

lemma dpath_bet_vertex_decomp_is_dpath_bet_vertex_decomp:
  assumes p_dpath: "dpath_bet E p u w"
  assumes v_in_p: "v \<in> set p"
  shows "is_dpath_bet_vertex_decomp E p v (dpath_bet_vertex_decomp E p v)"
proof -
  obtain xs ys where
    "p = xs @ v # ys"
    using v_in_p by (auto simp: in_set_conv_decomp)
  with p_dpath
  obtain q r where
    "p = q @ tl r"
    "dpath_bet E q u v"
    "dpath_bet E r v w"
    by (blast elim: dpath_bet_vertex_decompE)
  hence "is_dpath_bet_vertex_decomp E p v (q, r)"
    by (simp add: dpath_bet_def)
  hence "\<exists>qr. is_dpath_bet_vertex_decomp E p v qr"
    by blast
  thus ?thesis
    unfolding dpath_bet_vertex_decomp_def
    ..
qed

lemma dpath_bet_vertex_decompE_2:
  assumes p_dpath: "dpath_bet E p u w"
  assumes v_in_p: "v \<in> set p"
  assumes qr_def: "dpath_bet_vertex_decomp E p v = (q, r)"
  obtains
    "p = q @ tl r"
    "dpath_bet E q u v"
    "dpath_bet E r v w"
proof
  have *: "is_dpath_bet_vertex_decomp E p v (q, r)"
    using assms by (auto dest: dpath_bet_vertex_decomp_is_dpath_bet_vertex_decomp)
  then obtain u' w' where
    p_decomp: "p = q @ tl r" and
    q_dpath: "dpath_bet E q u' v" and
    r_dpath: "dpath_bet E r v w'"
    by auto
  hence "dpath_bet E p u' w'" by (simp add: dpath_bet_transitive)
  hence "u' = u" "w' = w" using p_dpath by (simp_all add: dpath_bet_def)
  thus
    "p = q @ tl r"
    "dpath_bet E q u v"
    "dpath_bet E r v w"
    using p_decomp q_dpath r_dpath by simp_all
qed

lemma dpath_bet_subgraph_is_dpath_bet_supergraph:
  "subgraph H G \<Longrightarrow> dpath_bet H p u v \<Longrightarrow> dpath_bet G p u v"
  by (simp add: dpath_bet_subset subgraph_def)

definition induced_subgraph :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "induced_subgraph H V G \<equiv> H = {(u, v) \<in> G. {u, v} \<subseteq> V}"

lemma induced_subgraphI[intro]:
  "H = {(u, v) \<in> G. {u, v} \<subseteq> V} \<Longrightarrow> induced_subgraph H V G" by (simp add: induced_subgraph_def)

lemma induced_subgraphE[elim]:
  assumes "induced_subgraph H V G"
  obtains "H = {(u, v) \<in> G. {u, v} \<subseteq> V}"
  using assms by (simp add: induced_subgraph_def)

lemma induced_subgraph_subgraph:
  "induced_subgraph H V G \<Longrightarrow> subgraph H G"
  by auto

lemma induced_subgraph_dVs_subset_V:
  "induced_subgraph H V G \<Longrightarrow> dVs H \<subseteq> V"
  unfolding induced_subgraph_def dVs_def
  by auto

lemma induced_subgraph_dVs_subset_Int:
  "induced_subgraph H V G \<Longrightarrow> dVs H \<subseteq> dVs G \<inter> V" \<comment> \<open>\<subseteq>: we may lose vertices when it gets disconnected\<close>
  by (simp add: induced_subgraph_dVs_subset_V induced_subgraph_subgraph subgraph_dVs)

lemma dpath_induced_subgraph_dpath:
  assumes "dpath G (u # p @ [v])" \<comment> \<open>vertices only are in the induced subgraph when they don't get disconnected\<close>
  assumes "induced_subgraph H V G"
  assumes "set (u # p @ [v]) \<subseteq> V"
  shows "dpath H (u # p @ [v])"
  using assms
  by (induction p arbitrary: u)
     (auto simp: adj_in_dVs)

lemma dpath_bet_induced_subgraph:
  assumes "dpath_bet G (u # p @ [v]) u v"
  assumes "induced_subgraph H V G"
  assumes "set (u # p @ [v]) \<subseteq> V"
  shows "dpath_bet H (u # p @ [v]) u v"
  using assms
  by (auto intro!: nonempty_dpath_dpath_bet simp: dpath_bet_def dpath_induced_subgraph_dpath)

definition vtrail :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where \<comment> \<open>\<^term>\<open>trail\<close> already defined for arc-walks\<close>
  "vtrail E p u v \<equiv> dpath_bet E p u v \<and> distinct (edges_of_dpath p)"

abbreviation closed_vtrail :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "closed_vtrail E c v \<equiv> vtrail E c v v \<and> Suc 0 < length c"

lemma closed_vtrail_implies_Cons:
  assumes "closed_vtrail E c v"
  shows "c = v # tl c"
  using assms
  by (auto simp add: vtrail_def dpath_bet_def)

lemma closed_vtrail_implies_tl_nonempty:
  assumes "closed_vtrail E c v"
  shows "tl c \<noteq> []"
  using assms
  by (simp add: tl_non_empty_conv)

lemma vtrail_in_vertices:
  "vtrail E p u v \<Longrightarrow> w \<in> set p \<Longrightarrow> w \<in> dVs E"
  by (auto simp add: vtrail_def intro: dpath_bet_in_vertices)

lemma
  assumes "vtrail E p u v"
  shows vtrail_hd_in_vertices: "u \<in> dVs E"
  and vtrail_last_in_vertices: "v \<in> dVs E"
  using assms
  by (auto intro: dpath_bet_endpoints simp: vtrail_def)

lemma closed_vtrail_hd_tl_in_vertices:
  assumes "closed_vtrail E c v"
  shows "hd (tl c) \<in> dVs E"
  using assms
  by (auto intro: vtrail_in_vertices simp flip: tl_non_empty_conv simp add: list_set_tl)

lemma vtrail_prefix_is_vtrail:
  notes vtrail_def [simp]
  assumes "p \<noteq> []"
  assumes "vtrail E (p @ q) u v"
  shows "vtrail E p u (last p)"
  using assms 
  by (auto simp: dpath_bet_prefix_is_dpath_bet edges_of_dpath_append_3)

lemma vtrail_suffix_is_vtrail:
  notes vtrail_def [simp]
  assumes "q \<noteq> []"
  assumes "vtrail E (p @ q) u v"
  shows "vtrail E q (hd q) v"
  using assms
  by (auto simp: dpath_bet_suffix_is_dpath_bet edges_of_dpath_append_2[OF \<open>q \<noteq> []\<close>])

definition distinct_dpath_bet :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_dpath_bet E p u v \<equiv> dpath_bet E p u v \<and> distinct p"

lemma dVs_eq: "dVs E = fst ` E \<union> snd ` E"
  by (induction E rule: infinite_finite_induct)
     (auto simp: dVs_def intro!: image_eqI, blast+)

lemma finite_vertices_iff: "finite (dVs E) \<longleftrightarrow> finite E" (is "?L \<longleftrightarrow> ?R")
proof
  show "?R \<Longrightarrow> ?L"
    by (induction E rule: finite_induct)
       (auto simp: dVs_eq)
  show "?L \<Longrightarrow> ?R"
  proof (rule ccontr)
    show "?L \<Longrightarrow> \<not>?R \<Longrightarrow> False"
      unfolding dVs_eq
      using finite_subset subset_fst_snd by fastforce
  qed
qed

lemma distinct_dpath_bet_length_le_card_vertices:
  assumes "distinct_dpath_bet E p u v"
  assumes "finite E"
  shows "length p \<le> card (dVs E)"
  using assms
  unfolding distinct_dpath_bet_def
  by (auto dest!: distinct_card[symmetric] intro!: card_mono simp: dpath_bet_in_vertices finite_vertices_iff)

lemma distinct_dpath_bet_triples_finite:
  assumes "finite E"
  shows "finite {(p, u, v). distinct_dpath_bet E p u v}"
proof (rule finite_subset)
  have "\<And>p u v. dpath_bet E p u v \<Longrightarrow> distinct p \<Longrightarrow> length p \<le> card (dVs E)"
    by (auto intro!: distinct_dpath_bet_length_le_card_vertices simp: distinct_dpath_bet_def assms)
  thus "{(p, u, v). distinct_dpath_bet E p u v} \<subseteq>
    {p. set p \<subseteq> dVs E \<and> length p \<le> card (dVs E)} \<times> dVs E \<times> dVs E"
    by (auto simp: distinct_dpath_bet_def dpath_bet_in_vertices)
  show "finite \<dots>"
    by (auto intro!: finite_cartesian_product finite_lists_length_le 
             simp: assms finite_vertices_iff)
qed

lemma distinct_dpath_bets_finite:
  "finite E \<Longrightarrow> finite {p. distinct_dpath_bet E p u v}"
  by (rule finite_surj[OF  distinct_dpath_bet_triples_finite]) auto

section\<open>Vwalks to paths (as opposed to arc walks (\<^term>\<open>awalk_to_apath\<close> before)\<close>
fun is_closed_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool" where
  "is_closed_decomp E p (q, r, s) \<longleftrightarrow>
    p = q @ tl r @ tl s \<and>
    (\<exists>u v w. dpath_bet E q u v \<and> closed_dpath_bet E r v \<and> dpath_bet E s v w) \<and>
    distinct q"

definition closed_dpath_bet_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "closed_dpath_bet_decomp E p \<equiv> SOME qrs. is_closed_decomp E p qrs"

lemma closed_dpath_bet_decompE:
  assumes p_dpath: "dpath_bet E p u v"
  assumes p_decomp: "p = xs @ y # ys @ y # zs"
  obtains q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "dpath_bet E q u y"
    "dpath_bet E r y y"
    "dpath_bet E s y v"
  using assms
  by auto (metis Cons_eq_appendI dpath_bet_vertex_decompE)

lemma closed_dpath_bet_decomp_is_closed_decomp:
  assumes p_dpath: "dpath_bet E p u v"
  assumes p_not_distinct: "\<not> distinct p"
  shows "is_closed_decomp E p (closed_dpath_bet_decomp E p)"
proof -
  obtain xs y ys zs where
    "p = xs @ y # ys @ y # zs" and
    xs_distinct: "distinct xs" and
    y_not_in_xs: "y \<notin> set xs"
    using p_not_distinct not_distinct_decomp
    by blast
  from p_dpath this(1)
  obtain q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "dpath_bet E q u y"
    "dpath_bet E r y y"
    "dpath_bet E s y v"
    by (erule closed_dpath_bet_decompE)
  moreover hence
    "distinct q"
    "Suc 0 < length r"
    using xs_distinct y_not_in_xs
    by simp+
  ultimately have
    "\<exists>q r s.
      p = q @ tl r @ tl s \<and>
      (\<exists>u v w. dpath_bet E q u v \<and> closed_dpath_bet E r v \<and> dpath_bet E s v w) \<and>
      distinct q"
    by blast
  hence "\<exists>qrs. is_closed_decomp E p qrs" by simp
  thus ?thesis unfolding closed_dpath_bet_decomp_def ..
qed

lemma closed_dpath_bet_decompE_2:
  assumes p_dpath: "dpath_bet E p u v"
  assumes p_not_distinct: "\<not> distinct p"
  assumes qrs_def: "closed_dpath_bet_decomp E p = (q, r, s)"
  obtains
    "p = q @ tl r @ tl s"
    "\<exists>w. dpath_bet E q u w \<and> closed_dpath_bet E r w \<and> dpath_bet E s w v"
    "distinct q"
proof -
  have "is_closed_decomp E p (q, r, s)"
    unfolding qrs_def[symmetric]
    using p_dpath p_not_distinct
    by (rule closed_dpath_bet_decomp_is_closed_decomp)
  then obtain u' w' v' where
    p_decomp: "p = q @ tl r @ tl s" and
    q_distinct: "distinct q" and
    dpaths: "dpath_bet E q u' w'"
    "closed_dpath_bet E r w'"
    "dpath_bet E s w' v'"
    by auto
  hence "dpath_bet E p u' v'"
    by (auto intro: dpath_bet_append_append_is_dpath_bet)
  hence "u' = u" "v' = v"
    using p_dpath
    by (simp_all add: dpath_bet_def)
  hence "\<exists>w. dpath_bet E q u w \<and> closed_dpath_bet E r w \<and> dpath_bet E s w v"
    using dpaths by blast
  with p_decomp q_distinct that
  show ?thesis by blast
qed

function dpath_bet_to_distinct :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "dpath_bet_to_distinct E p =
    (if (\<exists>u v. dpath_bet E p u v) \<and> \<not> distinct p
     then let (q, r, s) = closed_dpath_bet_decomp E p in dpath_bet_to_distinct E (q @ tl s)
     else p)"
  by auto

termination dpath_bet_to_distinct
proof (relation "measure (length \<circ> snd)")
  fix E p qrs rs q r s
  assume
    p_not_dpath: "(\<exists>u v. dpath_bet E p u v) \<and> \<not> distinct p" and
    assms: "qrs = closed_dpath_bet_decomp E p"
    "(q, rs) = qrs"
    "(r, s) = rs"
  then obtain u v where
    p_dpath: "dpath_bet E p u v"
    by blast
  hence "(q, r, s) = closed_dpath_bet_decomp E p"
    using assms
    by simp
  then obtain
    "p = q @ tl r @ tl s"
    "Suc 0 < length r"
    using p_dpath p_not_dpath
    by (elim closed_dpath_bet_decompE_2) auto
  thus "((E, (q @ tl s)), E, p) \<in> measure (length \<circ> snd)"
    by auto
qed simp

lemma dpath_bet_to_distinct_induct [consumes 1, case_names path decomp]:
  assumes "dpath_bet E p u v"
  assumes distinct: "\<And>p. \<lbrakk> dpath_bet E p u v; distinct p \<rbrakk> \<Longrightarrow> P p"
  assumes
    decomp: "\<And>p q r s. \<lbrakk> dpath_bet E p u v; \<not> distinct p;
      closed_dpath_bet_decomp E p = (q, r, s); P (q @ tl s) \<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using assms(1)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct p")
    case True
    with less.prems
    show ?thesis
      by (rule distinct)
  next
    case False
    obtain q r s where
      qrs_def: "closed_dpath_bet_decomp E p = (q, r, s)"
      by (cases "closed_dpath_bet_decomp E p")
    with less.prems False
    obtain
      "p = q @ tl r @ tl s"
      "\<exists>w. dpath_bet E q u w \<and> closed_dpath_bet E r w \<and> dpath_bet E s w v"
      by (elim closed_dpath_bet_decompE_2)
    hence
      "length (q @ tl s) < length p"
      "dpath_bet E (q @ tl s) u v"
      by (auto simp: tl_non_empty_conv intro: dpath_bet_transitive)
    hence "P (q @ tl s)"
      by (rule less.hyps)
    with less.prems False qrs_def
    show ?thesis
      by (rule decomp)
  qed
qed

lemma dpath_bet_to_distinct_is_distinct_dpath_bet:
  assumes "dpath_bet E p u v"
  shows "distinct_dpath_bet E (dpath_bet_to_distinct E p) u v"
  using assms
  by (induction rule: dpath_bet_to_distinct_induct) (auto simp: distinct_dpath_bet_def)

end