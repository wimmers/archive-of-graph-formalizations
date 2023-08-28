theory Tree_Defs
  imports Pair_Graph
begin

locale tree =
fixes
  root :: 'a
assumes
  root_in_T: "root \<in> dVs T" and
  unique_awalk: "v \<in> dVs T \<Longrightarrow> \<exists>!p. Vwalk.vwalk root p v"
begin

end
