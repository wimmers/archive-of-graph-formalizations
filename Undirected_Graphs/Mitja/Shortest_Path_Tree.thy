theory Shortest_Path_Tree
  imports Tree
begin

locale shortest_path_tree = rooted_spanning_tree G T root for G T root +
  fixes f :: "'a cost_fun"
  assumes cost_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes "v \<in> vertices T \<Longrightarrow> shortest_walk_cost T f root v = shortest_walk_cost G f root v"

lemmas (in shortest_path_tree) spanning = spanning

lemma (in shortest_path_tree) shortest_path:
  shows "shortest_walk_cost T f root v = shortest_walk_cost G f root v"
proof (cases)
  assume v_in_vertices: "v \<in> vertices T"
  have "shortest_path_tree_axioms G T root f"
    using shortest_path_tree_axioms
    by (rule shortest_path_tree.axioms(2))
  thus ?thesis
    using v_in_vertices
    by (simp add: shortest_path_tree_axioms_def)
next
  assume v_not_in_vertices_T: "v \<notin> vertices T"
  hence v_not_in_vertices_G: "v \<notin> vertices G"
    by (simp add: spanning)

  have "shortest_walk_cost T f root v = \<infinity>"
    using v_not_in_vertices_T
    by (rule subgraph.shortest_walk_cost_infinite_if_not_in_vertices)
  moreover have "shortest_walk_cost G f root v = \<infinity>"
    using v_not_in_vertices_G
    by (rule supergraph.shortest_walk_cost_infinite_if_not_in_vertices)
  ultimately show ?thesis
    by simp
qed

end