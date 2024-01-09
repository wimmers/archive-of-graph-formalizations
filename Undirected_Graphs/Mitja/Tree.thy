theory Tree
  imports Shortest_Path
begin

section \<open>Trees\<close>

locale tree = graph T for T +
  assumes unique_trail: "\<lbrakk> u \<in> vertices T; v \<in> vertices T \<rbrakk> \<Longrightarrow> \<exists>!p. trail T u p v"

theorem (in tree) no_closed_trail:
  shows "\<nexists>v c. closed_trail T v c"
proof (rule ccontr)
  assume "\<not> (\<nexists>v c. closed_trail T v c)"
  then obtain v c where
    c_closed_trail: "closed_trail T v c"
    by blast

  have v_in_vertices: "v \<in> vertices T"
    using c_closed_trail
    by (blast intro: trail_hd_in_vertices)
  have c_tl_hd_in_vertices: "hd (tl c) \<in> vertices T"
    using c_closed_trail
    by (rule closed_trail_tl_hd_in_vertices)

  have "trail T v [v, hd (tl c)] (hd (tl c))"
    using c_closed_trail
    by (rule closed_trail_hd_tl_hd_is_trail)
  moreover have "trail T v (rev (tl c)) (hd (tl c))"
    using c_closed_trail
    by (rule closed_trail_tl_rev_is_trail)
  moreover have "[v, hd (tl c)] \<noteq> rev (tl c)"
    using c_closed_trail
    by (rule closed_trail_hd_tl_hd_neq_tl_rev)
  ultimately show "False"
    using unique_trail[OF v_in_vertices c_tl_hd_in_vertices]
    by blast
qed

theorem (in tree) connected:
  shows "Walk.connected T"
  using unique_trail
  by (fastforce simp add: Walk.connected_def reachable_def trail_def)

section \<open>Rooted trees\<close>

locale rooted_tree = tree T for T +
  fixes root :: 'a
  assumes root_in_vertices: "root \<in> vertices T"

lemma (in rooted_tree) non_empty:
  shows "vertices T \<noteq> {}"
  using root_in_vertices
  by blast

section \<open>Spanning trees\<close>

locale spanning_tree = subgraph G T + tree T for G T +
  assumes spanning: "vertices T = vertices G"

section \<open>Rooted spanning trees\<close>

locale rooted_spanning_tree = spanning_tree G T + rooted_tree T root for G T root

lemmas (in rooted_spanning_tree) spanning = spanning

end