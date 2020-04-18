theory BFS_Tree
  imports Shortest_Path_Tree
begin

locale bfs_tree = shortest_path_tree G T root f for G T root f +
  assumes cost_uniform: "\<And>e. e \<in> edges G \<Longrightarrow> f e = 1"

end