theory Pair_Graph_Specs
(*Should call Pair_Graph_Specs *)
  imports Awalk "HOL-Data_Structures.Map_Specs" "HOL-Data_Structures.Set_Specs"
 begin

section \<open>Locale for Executable Functions on Directed Graphs\<close>

text \<open>We develop a locale modelling an abstract data type (ADT) which abstractly models a graph as an
      adjacency map: i.e.\ every vertex is mapped to a \<open>set\<close> of adjacent vertices, and this latter
      set is again modelled using the ADT of sets provided in Isabelle/HOL's distribution.

      We then show that this ADT can be implemented using existing implementations of the \<open>set\<close> ADT.
\<close>

locale Set_Choose = Set empty insert delete isin t_set invar
for empty insert delete isin t_set invar +
fixes sel ::"'m \<Rightarrow> 'a"
assumes choose: "t_set m \<noteq> {} \<Longrightarrow> sel m \<in> t_set m"

locale Adj_Map_Specs = 
 adj: Map adj_empty adj_update adj_delete adj_lookup adj_inv +

 neighb: Set_Choose neighb_empty neighb_insert neighb_delete neighb_isin neighb_set neighb_inv neighb_sel

 for adj_empty :: "'adj" and adj_update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and
     adj_delete :: "'a \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_lookup :: "'adj \<Rightarrow> 'a \<Rightarrow> 'neighb option" and
     adj_inv :: "'adj \<Rightarrow> bool"  and

     neighb_empty :: "'neighb" and neighb_insert :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_delete :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and neighb_isin :: "'neighb \<Rightarrow> 'a \<Rightarrow> bool" and
     neighb_set :: "'neighb \<Rightarrow> 'a set" and neighb_inv :: "'neighb \<Rightarrow> bool" and neighb_sel::"'neighb \<Rightarrow> 'a" +

fixes adj_foreach :: "('a \<Rightarrow> 'neighb \<Rightarrow> 'neighb) \<Rightarrow> 'adj \<Rightarrow> 'neighb \<Rightarrow> 'neighb"
assumes 
   adj_foreach[simp]: "adj_inv adj_map \<Longrightarrow> (\<exists>xs. adj_foreach f adj_map a0 =  fold f xs a0 \<and> set xs = dom (adj_lookup adj_map))"
   \<comment> \<open>Every folding function that is needed for the domain of the map or the elements of the set
       can be added explicitly like this. There is no need to fix the function, but we need to fix
       its type.\<close>

locale Pair_Graph_Specs = 
  Adj_Map_Specs adj_empty adj_update adj_delete adj_lookup adj_inv neighb_empty neighb_insert neighb_delete neighb_isin neighb_set neighb_inv neighb_sel adj_foreach

 for adj_empty :: "'adj" and adj_update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and
     adj_delete :: "'a \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_lookup :: "'adj \<Rightarrow> 'a \<Rightarrow> 'neighb option" and
     adj_inv :: "'adj \<Rightarrow> bool"  and

     neighb_empty :: "'neighb" and neighb_insert :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_delete :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and neighb_isin :: "'neighb \<Rightarrow> 'a \<Rightarrow> bool" and
     neighb_set :: "'neighb \<Rightarrow> 'a set" and neighb_inv :: "'neighb \<Rightarrow> bool" and neighb_sel::"'neighb \<Rightarrow> 'a"
     and neighb_foreach :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'neighb \<Rightarrow> 'b \<Rightarrow> 'b" and

     adj_foreach :: "('a \<Rightarrow> 'neighb \<Rightarrow> 'neighb) \<Rightarrow> 'adj \<Rightarrow> 'neighb \<Rightarrow> 'neighb" +

fixes digraph::"'adj" 
assumes digraph_invar[simp]:
   "adj_inv digraph" and
   \<comment> \<open>This is because in the abstract graph model we have no disconnected vertices.\<close>
   neighbourhood_invars[intro]:
   "(adj_lookup digraph v = Some neighb) \<Longrightarrow> set (neighb_inorder neighb) \<noteq> {}"
   "adj_lookup digraph v = Some neighb \<Longrightarrow> neighb_invar neighb"

begin

declare adj.map_empty[simp] adj.map_update[simp] adj.map_delete[simp] adj.invar_empty[simp]
        adj.invar_update[simp] adj.invar_delete[simp]

declare neighb.set_empty[simp] neighb.set_isin[simp] neighb.set_insert[simp] neighb.set_delete[simp]
        neighb.invar_empty[simp] neighb.invar_insert[simp] neighb.invar_delete[simp] neighb.choose[simp]

definition neighbourhood::"'a \<Rightarrow> 'neighb option" where "neighbourhood v \<equiv> adj_lookup digraph v"

definition neighbourhood_abs::"'a \<Rightarrow> 'a set" where
 "neighbourhood_abs u \<equiv> case neighbourhood u of Some neighb \<Rightarrow> (neighb_set neighb) | _ \<Rightarrow> {}"

definition vertices::"'neighb" where
  "vertices \<equiv> adj_foreach (\<lambda>v. neighb_insert v) digraph neighb_empty"

definition vertices_abs::"'a set" where
  "vertices_abs \<equiv> neighb_set vertices"

definition are_connected::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "are_connected u v = (case (neighbourhood u) of Some neighb \<Rightarrow> neighb_isin neighb v | _ \<Rightarrow> False)"

definition "digraph_abs \<equiv> {(u,v). v \<in> (neighbourhood_abs u) \<and> u \<in> vertices_abs}"

subsection \<open>Abstraction lemmas\<close>

text \<open>The idea here is use these lemmas in automation to transform all proof obligations to 
      abstract data structures.\<close>

lemma are_connected_abs[simp]: 
  "are_connected u v \<longleftrightarrow> (u,v) \<in> digraph_abs"
  by(auto simp: are_connected_def digraph_abs_def neighbourhood_abs_def neighbourhood_def
                   vertices_abs_def option.discI
             split: option.split)

lemma neighbourhood_abs_fold: 
  "set vs = dom (adj_lookup digraph) \<Longrightarrow>
         neighb_set (fold (\<lambda>v. neighb_insert v) vs neighb_empty) = dVs digraph_abs"
  by (induction vs arbitrary: )
     (auto simp: dVs_def digraph_abs_def neighbourhood_abs_def neighbourhood_def vertices_abs_def
                 vertices_def
           split: option.splits)

lemma neighbourhood_abs: "neighb_set vertices = dVs digraph_abs"
  apply(simp add: vertices_def)
  by (metis adj_foreach digraph_invar neighbourhood_abs_fold)


lemma neighbourhood_inv_fold: 
  "set vs = dom (adj_lookup digraph) \<Longrightarrow>
         neighb_inv (fold (\<lambda>v. neighb_insert v) vs neighb_empty)"
  by (induction vs arbitrary: ) auto

lemma inv_vertices: "neighb_inv (vertices)"
  apply(simp add: vertices_def)        
  by (metis adj_foreach digraph_invar neighbourhood_inv_fold)

lemma neighbourhood_abs_in: "neighb_isin vertices v \<longleftrightarrow> v \<in> dVs digraph_abs"
  by(auto simp add: neighbourhood_abs inv_vertices)

end  

locale Pair_Graph_Specs_by_Ordered = 
 adj: Map_by_Ordered adj_empty adj_update adj_delete adj_lookup adj_inorder adj_inv +

 neighb: Set_by_Ordered neighb_empty neighb_insert neighb_delete neighb_isin neighb_inorder neighb_inv 

 for adj_empty :: "'adj" and adj_update :: "'a::linorder \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and
     adj_delete :: "'a \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_lookup :: "'adj \<Rightarrow> 'a \<Rightarrow> 'neighb option" and
     adj_inorder :: "'adj \<Rightarrow> ('a * 'neighb) list" and adj_inv :: "'adj \<Rightarrow> bool" and

     neighb_empty :: "'neighb" and neighb_insert :: "'a::linorder \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_delete :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and neighb_isin :: "'neighb \<Rightarrow> 'a \<Rightarrow> bool" and
     neighb_inorder :: "'neighb \<Rightarrow> 'a list" and neighb_inv :: "'neighb \<Rightarrow> bool" +

fixes digraph::"'adj"

assumes digraph_invar[simp]:
   "adj_inv digraph" and
   \<comment> \<open>This is because in the abstract graph model we have no disconnected vertices.\<close>
   neighbourhood_invars[intro]:
   "(adj_lookup digraph v = Some neighb) \<Longrightarrow> set (neighb_inorder neighb) \<noteq> {}"
   "adj_lookup digraph v = Some neighb \<Longrightarrow> neighb_invar neighb"

begin

declare adj.inorder_empty[simp] adj.inorder_lookup[simp] adj.inorder_update[simp]
        adj.inorder_delete[simp] adj.inorder_inv_empty[simp] adj.inorder_inv_update[simp]
        adj.inorder_inv_delete[simp]

declare neighb.inorder_empty[simp] neighb.isin[simp] neighb.inorder_insert[simp]
        neighb.inorder_delete[simp] neighb.inorder_inv_empty[simp] neighb.inorder_inv_insert[simp]
        neighb.inorder_inv_delete[simp]


definition neighbourhood::"'a \<Rightarrow> 'neighb option" where "neighbourhood v \<equiv> adj_lookup digraph v"

definition neighbourhood_abs::"'a \<Rightarrow> 'a set" where
 "neighbourhood_abs u \<equiv> case neighbourhood u of Some neighb \<Rightarrow> set (neighb_inorder neighb) | _ \<Rightarrow> {}"

definition vertices::"'neighb" where
  "vertices \<equiv> fold (\<lambda>(v,neighb). neighb_insert v) (adj_inorder digraph) neighb_empty"

definition vertices_abs::"'a set" where
  "vertices_abs \<equiv> set (neighb_inorder vertices)"

definition are_connected::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "are_connected u v = (case (neighbourhood u) of Some neighb \<Rightarrow> neighb_isin neighb v | _ \<Rightarrow> False)"

definition "digraph_abs \<equiv> {(u,v). v \<in> (neighbourhood_abs u) \<and> u \<in> vertices_abs}"

subsection \<open>Abstraction lemmas\<close>

text \<open>The idea here is use these lemmas in automation to transform all proof obligations to 
      abstract data structures.\<close>

lemma are_connected_abs[simp]: 
  "are_connected u v \<longleftrightarrow> (u,v) \<in> digraph_abs"
  by(auto simp: are_connected_def digraph_abs_def neighbourhood_abs_def neighbourhood_def
                   vertices_abs_def option.discI
             split: option.split)

lemma "vertices_abs = dVs digraph_abs" 
  sorry


end  



end