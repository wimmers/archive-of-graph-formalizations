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

locale Set_Choose = Set 
  where set = t_set for t_set +
fixes sel ::"'m \<Rightarrow> 'a"
assumes choose: "s \<noteq> empty \<Longrightarrow> isin s (sel s)"
begin

declare set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
        invar_empty[simp] invar_insert[simp] invar_delete[simp] choose[simp]

subsection \<open>Abstraction lemmas\<close>

text \<open>These are lemmas for automation. Their purpose is to remove any mention of the locale set ADT
      constructs and replace it with Isabelle's native sets.\<close>

lemma choose'[simp, intro,dest]:
  "s \<noteq> empty \<Longrightarrow> invar s \<Longrightarrow> sel s \<in> t_set s"
  by(auto simp flip: set_isin)

lemma choose''[intro]:
  "invar s \<Longrightarrow> s \<noteq> empty \<Longrightarrow> t_set s \<subseteq> s' \<Longrightarrow> sel s \<in> s'"
  by(auto simp flip: set_isin)

lemma emptyD[dest]:
           "s = empty \<Longrightarrow> t_set s = {}"
           "s \<noteq> empty \<Longrightarrow> invar s \<Longrightarrow> t_set s \<noteq> {}"
           "empty = s \<Longrightarrow> t_set s = {}"
           "empty \<noteq> s \<Longrightarrow> invar s \<Longrightarrow> t_set s \<noteq> {}"
 using local.set_empty
 by auto

end

locale Adj_Map_Specs = 
 adj: Map 
 where update = update and invar = adj_inv +

 neighb: Set_Choose
 where empty = neighb_empty and delete = neighb_delete and insert = neighb_insert and invar = neighb_inv
      and isin = isin

 for update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj" and adj_inv :: "'adj \<Rightarrow> bool"  and

     neighb_empty :: "'neighb"  ("\<emptyset>\<^sub>N") and neighb_delete :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'neighb" and
     neighb_insert and neighb_inv and isin

  \<comment> \<open>Why do we need ann efficient neghbourhood test?\<close>

begin

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"

definition "set_of_map (m::'adj) \<equiv> {(u,v). case (lookup m u) of Some vs \<Rightarrow> v \<in>\<^sub>G vs}"

end

no_notation digraph ("digraph")

locale Pair_Graph_Specs = 
  Adj_Map_Specs where update = update
for update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj"  (*+
fixes graph_inv:: "'adj \<Rightarrow> bool"

assumes neighbourhood_invars:
 "graph_inv G \<Longrightarrow> adj_inv G"
 "\<lbrakk>graph_inv G; lookup G v = Some neighb\<rbrakk> \<Longrightarrow> neighb_inv neighb"

   "adj_inv digraph" and
   \<comment> \<open>This is because in the abstract graph model we have no disconnected vertices.\<close>
   neighbourhood_invars:
   "(lookup digraph v = Some neighb)"
   "lookup digraph v = Some neighb \<Longrightarrow> neighb_inv neighb"*)

begin

definition "graph_inv G \<equiv> (adj_inv G \<and> (\<forall>v neighb. lookup G v = Some neighb \<longrightarrow> neighb_inv neighb))"

lemma graph_invE[elim]: 
  "graph_inv G \<Longrightarrow> (\<lbrakk>adj_inv G; (\<And>v neighb. lookup G v = Some neighb \<Longrightarrow> neighb_inv neighb)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: graph_inv_def)

lemma graph_invI[intro]: 
  "\<lbrakk>adj_inv G; (\<And>v neighb. lookup G v = Some neighb \<Longrightarrow> neighb_inv neighb)\<rbrakk> \<Longrightarrow> graph_inv G"
  by (auto simp: graph_inv_def)

declare adj.map_empty[simp] adj.map_update[simp] adj.map_delete[simp] adj.invar_empty[simp]
        adj.invar_update[simp] adj.invar_delete[simp]

declare neighb.set_empty[simp] neighb.set_isin[simp] neighb.set_insert[simp] neighb.set_delete[simp]
        neighb.invar_empty[simp] neighb.invar_insert[simp] neighb.invar_delete[simp] neighb.choose[simp]

definition neighbourhood::"'adj \<Rightarrow> 'a \<Rightarrow> 'neighb" where
  "neighbourhood G v \<equiv> (case (lookup G v) of Some neighb \<Rightarrow> neighb | _ \<Rightarrow> neighb_empty)"

notation "neighbourhood" ("\<N>\<^sub>G _ _" 100)

lemma neighbourhood_invars'[simp,dest]:
   "graph_inv G \<Longrightarrow> neighb_inv (\<N>\<^sub>G G v)"
  by (auto simp add: graph_inv_def neighbourhood_def split: option.splits)

definition "digraph_abs G \<equiv> {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G G u)}"

subsection \<open>Abstraction lemmas\<close>

text \<open>These are lemmas for automation. Their purpose is to remove any mention of the neighbourhood
      concept implemented using the locale constructs and replace it with abstract terms
      on pair graphs.\<close>

lemma are_connected_abs[simp]: 
  "graph_inv G \<Longrightarrow> v \<in> t_set (\<N>\<^sub>G G u) \<longleftrightarrow> (u,v) \<in> digraph_abs G"
  by(auto simp: digraph_abs_def neighbourhood_def option.discI graph_inv_def
          split: option.split)

lemma are_connected_absD[dest]: 
  "\<lbrakk>v \<in> t_set (\<N>\<^sub>G G u); graph_inv G\<rbrakk> \<Longrightarrow> (u,v) \<in> digraph_abs G"
  by (auto simp: are_connected_abs)

lemma are_connected_absI[intro]: 
  "\<lbrakk>(u,v) \<in> digraph_abs G; graph_inv G\<rbrakk> \<Longrightarrow> v \<in> t_set (\<N>\<^sub>G G u)"
  by (auto simp: are_connected_abs)

lemma neighbourhood_absD[dest!]:
  "\<lbrakk>t_set (\<N>\<^sub>G G x) \<noteq> {}; graph_inv G\<rbrakk> \<Longrightarrow> x \<in> dVs (digraph_abs G)"
  by (auto simp: dVs_def dest!: neighb.emptyD)

lemma neighbourhood_abs[simp]:
  "graph_inv G \<Longrightarrow> t_set (\<N>\<^sub>G G u) = Pair_Graph.neighbourhood (digraph_abs G) u"
  by(auto simp: digraph_abs_def neighbourhood_def Pair_Graph.neighbourhood_def option.discI graph_inv_def
          split: option.split)

definition "add_edge G u v \<equiv> 
( 
  case (lookup G u) of Some neighb \<Rightarrow> 
  let
    neighb = the (lookup G u);
    neighb' = neighb_insert v neighb;
    digraph' = update u neighb' G
  in
    digraph'
  | _ \<Rightarrow>
  let
    neighb' = neighb_insert v neighb_empty;
    digraph' = update u neighb' G
  in
    digraph'
 
)"

lemma adj_inv_insert[intro]: "graph_inv G \<Longrightarrow> graph_inv (add_edge G u v)"
  by (auto simp: add_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_insert[simp]: "graph_inv G \<Longrightarrow> digraph_abs (add_edge G u v) = insert (u,v) (digraph_abs G)"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def add_edge_def split: option.splits if_splits)

definition "delete_edge G u v \<equiv> 
( 
  case (lookup G u) of Some neighb \<Rightarrow> 
  let
    neighb = the (lookup G u);
    neighb' = neighb_delete v neighb;
    digraph' = update u neighb' G
  in
    digraph'
  | _ \<Rightarrow> G 
)"

lemma adj_inv_delete[intro]: "graph_inv G \<Longrightarrow> graph_inv (delete_edge G u v)"
  by (auto simp: delete_edge_def graph_inv_def split: option.splits)

lemma digraph_abs_delete[simp]:  "graph_inv G \<Longrightarrow> digraph_abs (delete_edge G u v) = (digraph_abs G) - {(u,v)}"
  by (fastforce simp add: digraph_abs_def set_of_map_def neighbourhood_def delete_edge_def split: option.splits if_splits)

end  

end