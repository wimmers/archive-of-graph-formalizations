theory BFS_2
  imports Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools"
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun fold_tree where
"fold_tree f Leaf a = a"
| "fold_tree f (Node l x r) a = fold_tree f r (fold_tree f l a)" 

definition "invar P I f \<equiv> (\<forall>s. (P s \<and> I s) \<longrightarrow> I (f s))"

lemma invarI: "(\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)

lemma invarE: "invar P I f \<Longrightarrow> ((\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto simp: invar_def)

lemma invarD: "invar P I f \<Longrightarrow> (\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s))"
  by (auto simp: invar_def)


definition "valid_fold set_of fold_fun \<equiv> \<forall>dom f a0. (\<exists>xs. fold_fun f dom a0 = foldr f xs a0 \<and> set xs = set_of dom)"

lemma valid_foldE:
  "valid_fold set_of fold_fun \<Longrightarrow> 
    (\<And>xs. \<lbrakk>fold_fun f domain a0 = foldr f xs a0; set_of domain = set xs\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (fastforce simp: valid_fold_def)

lemma invar_fold_conjI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x)"
  shows "invar P I (fold_fun f domain)"
proof-
  have "P (foldr f xs s) \<and> I (foldr f xs s)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" "P s" "I s" for xs s
    using that
  proof(induction xs)
    case (Cons x xs)
    hence "P (foldr f xs s)" "I (foldr f xs s)"
      by auto 
    thus ?case
      using Cons(2)[of x]
      by (auto elim!: invarE)
  qed auto
  hence "invar P I (foldr f xs)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" for xs
    using that
    by (auto intro!: invarI)
  thus ?thesis
    using assms
    by (smt (verit) invarE invarI valid_foldE)
qed

method elim_valid_fold for  f::"'a \<Rightarrow> 'b \<Rightarrow> 'b" = 
  ((match conclusion in "P (fold_fun f domain a0)" for a0::'b and fold_fun domain and P 
      \<Rightarrow> \<open>elim valid_foldE[where f = f and domain = domain and ?a0.0 = a0], match premises in a[thin]: 
           "fold_fun f domain a0 = foldr _ _ _"
              \<Rightarrow> \<open>subst  a\<close>\<close>))

lemma invar_foldI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) I (f x)"
  shows "invar (\<lambda>_. True) I (fold_fun f domain)"
  using assms(2)
  by(auto intro!: invar_fold_conjI[OF assms(1), where P = "\<lambda>_. True"])

lemma invar_foldI':
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x s. \<lbrakk>x \<in> set_of domain; I s\<rbrakk> \<Longrightarrow> I (f x s)"
    "I s"
  shows "I (fold_fun f domain s)"
  using invar_foldI[simplified invar_def, OF assms(1)] assms
  by metis

lemma invar_foldI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) I (f s x)"
  shows "invar (\<lambda>_. True) I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_foldI[OF assms(1)] assms(2-)
  by (metis (no_types, lifting) invar_def)

lemma invar_fold_conjI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f s x)"
  shows "invar P I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_fold_conjI[OF assms(1)] assms(2-)
  by (smt (verit, ccfv_SIG) invar_def)

lemma invar_conjI: "\<lbrakk>J; invar P (\<lambda>s. J \<and> I s) f\<rbrakk> \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)

record ('parents, 'neighb) BFS_state = parents:: "'parents" current:: "'neighb" visited:: "'neighb" 

locale BFS =
  (*set_ops: Set2 where empty = empty and insert = neighb_insert and isin = neighb_isin +*)
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv neighb_insert
  
for lookup :: "'adj \<Rightarrow> 'ver \<Rightarrow> 'neighb option" +

fixes  G::"'adj" and expand_tree::"'adj \<Rightarrow> 'neighb \<Rightarrow> 'neighb \<Rightarrow> 'adj" and
next_frontier::"'neighb \<Rightarrow> 'neighb \<Rightarrow> 'neighb" 


assumes
   graph_inv[simp]:
     "Graph.graph_inv G" and
   expand_tree[simp]:
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis\<rbrakk> \<Longrightarrow> Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> {(u,v) | u v. u \<in> t_set (frontier) \<and> v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u - t_set vis)}" and
   next_frontier[simp]:
    "\<lbrakk>neighb_inv frontier; neighb_inv vis\<rbrakk> \<Longrightarrow>  neighb_inv (next_frontier frontier vis)"
    "\<lbrakk>neighb_inv frontier; neighb_inv vis\<rbrakk> \<Longrightarrow>
       t_set (next_frontier frontier vis) =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"
    

begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

notation "inter" (infixl "\<inter>\<^sub>G" 100)

notation "diff" (infixl "-\<^sub>G" 100)

notation "union" (infixl "\<union>\<^sub>G" 100)

declare set_ops.set_union[simp] set_ops.set_inter[simp] set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]


function (domintros) BFS::"('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state" where
  "BFS BFS_state = 
     (if (current BFS_state) \<noteq> \<emptyset>\<^sub>N then
        let
          parents' = expand_tree (parents BFS_state) (current BFS_state) (visited BFS_state);
          current' =  next_frontier (current BFS_state) (visited BFS_state);
          visited' = visited BFS_state \<union>\<^sub>G current'
        in 
          BFS (BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>)
       else
        BFS_state)"
  by pat_completeness auto

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

definition "BFS_call_1_conds bfs_state \<equiv> (current bfs_state) \<noteq> \<emptyset>\<^sub>N"

lemma DFS_call_1_conds[call_cond_elims]: 
  "BFS_call_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_call_1_conds_def split: list.splits option.splits if_splits)


definition "BFS_upd1 BFS_state \<equiv>
(        let
          parents' = expand_tree (parents BFS_state) (current BFS_state) (visited BFS_state);
          current' =  next_frontier (current BFS_state) (visited BFS_state);
          visited' = visited BFS_state \<union>\<^sub>G current'
        in 
          BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>

)" 


definition "BFS_ret_1_conds bfs_state \<equiv> (current bfs_state) = \<emptyset>\<^sub>N"

lemma BFS_ret_1_conds[call_cond_elims]:
  "BFS_ret_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>current bfs_state = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> BFS_ret_1_conds bfs_state"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

abbreviation "BFS_ret1 dfs_state \<equiv> dfs_state"

lemma BFS_cases:
  assumes "BFS_call_1_conds bfs_state \<Longrightarrow> P"
      "BFS_ret_1_conds bfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BFS_call_1_conds bfs_state \<or>
        BFS_ret_1_conds bfs_state"
    by (auto simp add: BFS_call_1_conds_def
                        BFS_ret_1_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma BFS_simps:
  assumes "BFS_dom BFS_state" 
  shows"BFS_call_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS (BFS_upd1 BFS_state)"
      "BFS_ret_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS_ret1 BFS_state"
  by (auto simp add: BFS.psimps[OF assms]
                     BFS_call_1_conds_def BFS_upd1_def 
                     BFS_ret_1_conds_def Let_def
            split: list.splits option.splits if_splits)

lemma BFS_induct: 
  assumes "BFS_dom bfs_state"
  assumes "\<And>bfs_state. \<lbrakk>BFS_dom bfs_state;
                        BFS_call_1_conds bfs_state \<Longrightarrow> P (BFS_upd1 bfs_state)\<rbrakk>
              \<Longrightarrow> P bfs_state"
  shows "P bfs_state"
  apply(rule BFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: BFS_call_1_conds_def BFS_upd1_def Let_def
           split: list.splits option.splits if_splits)

definition "invar_1 bfs_state \<equiv>
              neighb_inv (visited bfs_state) \<and> neighb_inv (current bfs_state) \<and>
              Graph.graph_inv (parents bfs_state)"

lemma invar_1_props[elim]: 
  "invar_1 bfs_state \<Longrightarrow> 
  (\<lbrakk>neighb_inv (visited bfs_state) ; neighb_inv (current bfs_state) ;
    Graph.graph_inv (parents bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>neighb_inv (visited bfs_state); neighb_inv (current bfs_state);
    Graph.graph_inv (parents bfs_state)\<rbrakk> 
    \<Longrightarrow> invar_1 bfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_upd1 bfs_state)"
  by(auto elim!: call_cond_elims simp: Let_def BFS_upd1_def BFS_call_1_conds_def intro!: invar_props_intros invarI)

lemma invar_1_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

definition "invar_2 bfs_state \<equiv> 
  Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G \<and> 
  t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<and>
  t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)"

lemma invar_2_props[elim]: 
  "invar_2 bfs_state \<Longrightarrow> 
  (\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
    t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
    dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state);
    t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
   "\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
     t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
     dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state);
     t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)\<rbrakk>
     \<Longrightarrow> invar_2 bfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_upd1 bfs_state)"
  apply(auto elim!: call_cond_elims invar_1_props invar_2_props intro!: invar_props_intros simp: BFS_upd1_def Let_def)

  apply(auto elim!: call_cond_elims invar_1_props invar_2_props intro!: invar_props_intros simp: BFS_upd1_def dVs_def)


  apply blast
  apply blast
  done


lemma invar_2_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
   shows "invar_2 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


definition "invar_3 bfs_state \<equiv> 
  (\<forall>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))).
    \<forall>u. (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u) \<longrightarrow> 
      ((v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u) 
       \<or> (\<exists>w\<in>t_set (current bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u))))"

lemma invar_3_props[elim]: 
  "invar_3 bfs_state \<Longrightarrow> 
  \<lbrakk>\<lbrakk>\<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))); (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
          (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u)\<rbrakk>
           \<Longrightarrow> P;
   \<lbrakk>\<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))); (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
           (\<exists>w\<in>t_set (current bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u))\<rbrakk>
           \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
   "(\<And>v u. \<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))); (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
       (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u) \<or>
       (\<exists>w\<in>t_set (current bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)))
    \<Longrightarrow> invar_3 bfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_upd1[invar_holds_intros]: 
  assumes "BFS_call_1_conds bfs_state" "invar_1 bfs_state" "invar_2 bfs_state" "invar_3 bfs_state"
  shows "invar_3 (BFS_upd1 bfs_state)"
proof(rule invar_props_intros, goal_cases)
  case (1 v u)
  then show ?case 
    using assms
  proof(elim invar_3_props[where u = u and v = v], goal_cases)
    case 1
    find_theorems dVs "_\<union>_"
    from \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
    have "dVs (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) \<subseteq>
            dVs (Graph.digraph_abs (parents bfs_state)) \<union> {v | u v. u \<in> t_set (current bfs_state) \<and> v \<in> Pair_Graph.neighbourhood (Graph.digraph_abs G) u}"
      apply (auto simp: BFS_upd1_def Let_def elim!: in_dVsE invar_1_props invar_2_props)

      apply (auto simp: BFS_upd1_def Let_def dVs_def elim!: in_dVsE invar_1_props invar_2_props)
      sledgehammer
      apply (metis insertI1)





    then show ?case
      apply(auto s imp: BFS_upd1_def)
  next
    case 2
    then show ?case sorry
  qed

  apply(subst BFS_upd1_def)
  apply(rule invar_props_intros)
  apply simp
  apply(subst expand_tree(2))
  apply (auto elim!: call_cond_elims invar_1_props invar_2_props invar_3_props  intro!: invar_props_intros)
  subgoal sorry
 
lemma invar_3_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_3 bfs_state"
   shows "invar_3 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed


\<comment> \<open>Example of funciton package bad ind ppcl?\<close>

definition "invar_3 dfs_state = (\<forall>v \<in> t_set (visited dfs_state). (\<nexists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) )"

lemma invar_3_props[elim!]: "invar_3 dfs_state \<Longrightarrow> (\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow> \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]: "\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow>  \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> invar_3 dfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def dest!: append_vwalk_pref intro!: invar_props_intros)

lemma invar_3_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd2 dfs_state)"
  by (force simp: DFS_upd2_def dest!: append_vwalk_pref intro!: invar_props_intros elim!: DFS_call_2_conds)

lemma invar_3_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_3 dfs_state"
   shows "invar_3 (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

abbreviation "seen_verts dfs_state \<equiv> (set (stack dfs_state) \<union> t_set (visited dfs_state))"

definition "state_rel_1 dfs_state_1 dfs_state_2 
              \<equiv> seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2"

lemma state_rel_1_props[elim!]: "state_rel_1 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  (seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2 \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]: "\<lbrakk>seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "\<lbrakk>state_rel_1 dfs_state_1 dfs_state_2; state_rel_1 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_1 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def intro!: state_rel_intros)

lemma state_rel_1_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro!: state_rel_intros elim: call_cond_elims)

lemma state_rel_1_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state"
   shows "state_rel_1 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

definition "state_rel_2 dfs_state_1 dfs_state_2 
              \<equiv> (\<forall>v \<in> set (stack dfs_state_1). ((\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t) \<longrightarrow> v \<in> set (stack dfs_state_2))"

lemma state_rel_2_props[elim!]: "state_rel_2 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  \<lbrakk>\<lbrakk>\<And>v.\<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (auto simp: state_rel_2_def)

lemma state_rel_2_intro[state_rel_intros]: "\<lbrakk>\<And>v. \<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_2_def)

lemma state_rel_2_trans:
  "\<lbrakk>state_rel_2 dfs_state_1 dfs_state_2; state_rel_2 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_2 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_2_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def intro!: state_rel_intros)

lemma state_rel_2_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_upd2 dfs_state)"
  by (force simp: DFS_upd2_def intro!: state_rel_intros elim!: DFS_call_2_conds)

lemma state_rel_2_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_3 dfs_state"
   shows "state_rel_2 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_2_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_1[ret_holds_intros]: "DFS_ret_1_conds (dfs_state) \<Longrightarrow> DFS_ret_1_conds (DFS_ret1 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = NotReachable"
   shows "DFS_ret_1_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_2[ret_holds_intros]: "DFS_ret_2_conds (dfs_state) \<Longrightarrow> DFS_ret_2_conds (DFS_ret2 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret2_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = Reachable"
   shows "DFS_ret_2_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

end
                                                               
end
