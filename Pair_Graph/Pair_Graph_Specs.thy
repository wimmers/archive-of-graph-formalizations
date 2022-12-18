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
     neighb_insert and neighb_inv and isin +

fixes adj_foreach :: "('a \<Rightarrow> 'a set \<Rightarrow> 'a set) \<Rightarrow> 'adj \<Rightarrow> 'a set \<Rightarrow> 'a set"
assumes
   adj_foreach[simp]:
    "adj_inv adj_map \<Longrightarrow> (\<exists>xs. adj_foreach f adj_map a0 =  fold f xs a0 \<and> set xs = dom (lookup adj_map))"
   \<comment> \<open>Every folding function that is needed for the domain of the map or the elements of the set
       can be added explicitly like this. There is no need to fix the function, but we need to fix
       its type.\<close>
  \<comment> \<open>Why do we need ann efficient neghbourhood test?\<close>

begin

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"


end

locale Pair_Graph_Specs = 
  Adj_Map_Specs where update = update
for update :: "'a \<Rightarrow> 'neighb \<Rightarrow> 'adj \<Rightarrow> 'adj"  +

fixes digraph::"'adj" 
assumes digraph_invar:
   "adj_inv digraph" and
   \<comment> \<open>This is because in the abstract graph model we have no disconnected vertices.\<close>
   neighbourhood_invars:
   "(lookup digraph v = Some neighb)"
   "lookup digraph v = Some neighb \<Longrightarrow> neighb_inv neighb"

begin


declare adj.map_empty[simp] adj.map_update[simp] adj.map_delete[simp] adj.invar_empty[simp]
        adj.invar_update[simp] adj.invar_delete[simp]

declare neighb.set_empty[simp] neighb.set_isin[simp] neighb.set_insert[simp] neighb.set_delete[simp]
        neighb.invar_empty[simp] neighb.invar_insert[simp] neighb.invar_delete[simp] neighb.choose[simp]

definition neighbourhood::"'a \<Rightarrow> 'neighb" where "neighbourhood v \<equiv> the (lookup digraph v)"

notation "neighbourhood" ("\<N>\<^sub>G _" 100)

lemma neighbourhood_invars'[simp]:
   "neighb_inv (\<N>\<^sub>G v)"
  by (auto simp add: neighbourhood_def neighbourhood_invars)

definition "digraph_abs \<equiv> {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G u)}"

subsection \<open>Abstraction lemmas\<close>

text \<open>These are lemmas for automation. Their purpose is to remove any mention of the neighbourhood
      concept implemented using the locale constructs and replace it with abstract terms
      on pair graphs.\<close>

lemma are_connected_abs: 
  "v \<in> t_set (\<N>\<^sub>G u) \<longleftrightarrow> (u,v) \<in> digraph_abs"
  by(auto simp: digraph_abs_def neighbourhood_def option.discI neighbourhood_invars
          split: option.split)

lemma are_connected_absD[dest!]: 
  "v \<in> t_set (\<N>\<^sub>G u) \<Longrightarrow> (u,v) \<in> digraph_abs"
  by (auto simp: are_connected_abs)

lemma are_connected_absI[intro!]: 
  "(u,v) \<in> digraph_abs \<Longrightarrow> v \<in> t_set (\<N>\<^sub>G u)"
  by (auto simp: are_connected_abs)


lemma neighbourhood_absD[dest!]:
  "t_set (\<N>\<^sub>G x) \<noteq> {} \<Longrightarrow> x \<in> dVs digraph_abs"
  by (auto simp: digraph_abs_def dVs_def dest!: neighb.emptyD)

end  

end