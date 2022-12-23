theory DFS
  imports Pair_Graph_Specs
begin

datatype return = Reachable | NotReachable

record ('ver, 'neighb) DFS_state = stack:: "'ver list" visited:: "'neighb" return:: return

locale DFS =
  (*set_ops: Set2 where empty = empty and insert = neighb_insert and isin = neighb_isin +*)
  Graph: Pair_Graph_Specs
    where lookup = lookup +
 set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv neighb_insert


for lookup :: "'adj \<Rightarrow> 'a \<Rightarrow> 'neighb option" +

fixes G::"'adj" and t::"'a"
assumes finite_neighbourhoods:
          "finite (t_set N)" and
        graph_inv[simp,intro]:
          "Graph.graph_inv G"
begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"

notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

notation "inter" (infixl "\<inter>\<^sub>G" 100)

notation "diff" (infixl "-\<^sub>G" 100)

notation "union" (infixl "\<union>\<^sub>G" 100)

declare set_ops.set_union[simp] set_ops.set_inter[simp] set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]

function (domintros) DFS::"('a, 'neighb) DFS_state \<Rightarrow> ('a, 'neighb) DFS_state" where
  "DFS dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          (dfs_state \<lparr>return := Reachable\<rparr>)
        else ((if (\<N>\<^sub>G v -\<^sub>G (visited dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  DFS (dfs_state \<lparr>stack := (sel ((\<N>\<^sub>G v) -\<^sub>G (visited dfs_state))) # (stack dfs_state)\<rparr>)
                 else DFS (dfs_state \<lparr>stack := stack_tl, visited := neighb_insert v (visited dfs_state)\<rparr>))
              )
      )
     | _ \<Rightarrow> (dfs_state \<lparr>return := NotReachable\<rparr>)
    )"
  by pat_completeness auto

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

definition "DFS_call_1_conds dfs_state \<equiv> 
    (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else ((if ((\<N>\<^sub>G v) -\<^sub>G (visited dfs_state)) \<noteq> (\<emptyset>\<^sub>N) then
                  True
                 else False)
              )
      )
     | _ \<Rightarrow> False
    )"

lemma DFS_call_1_conds[call_cond_elims]: 
  "DFS_call_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (visited dfs_state) \<noteq> (\<emptyset>\<^sub>N)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_upd1 dfs_state \<equiv> (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_state)))
    in
      dfs_state \<lparr>stack := (sel ((N -\<^sub>G (visited dfs_state)))) # (stack dfs_state)\<rparr>)" 

definition "DFS_call_2_conds dfs_state \<equiv>
(case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else (
                (if ((\<N>\<^sub>G v) -\<^sub>G (visited dfs_state)) \<noteq> (\<emptyset>\<^sub>N) then
                  False
                 else True)
              )
      )
     | _ \<Rightarrow> False
    )"

term "{}"

lemma DFS_call_2_conds[call_cond_elims]: 
  "DFS_call_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (visited dfs_state) = (\<emptyset>\<^sub>N)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_upd2 dfs_state \<equiv> 
  ((dfs_state \<lparr>stack := tl (stack dfs_state), visited := neighb_insert (hd (stack dfs_state)) (visited dfs_state)\<rparr>))"


definition "DFS_ret_1_conds dfs_state \<equiv>
   (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else (
                (if ((\<N>\<^sub>G v) -\<^sub>G (visited dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  False
                 else False)                     
              )
      )
     | _ \<Rightarrow> True
   )"

lemma DFS_ret_1_conds[call_cond_elims]:
  "DFS_ret_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma DFS_call_4_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_ret_1_conds dfs_state"
  by(auto simp: DFS_ret_1_conds_def split: list.splits option.splits if_splits)

abbreviation "DFS_ret1 dfs_state \<equiv> (dfs_state \<lparr>return := NotReachable\<rparr>)"

definition "DFS_ret_2_conds dfs_state \<equiv>
   (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          True
        else (
                (if (\<N>\<^sub>G v -\<^sub>G (visited dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  False
                 else False)
              )
      )
     | _ \<Rightarrow> False
   )"


lemma DFS_ret_2_conds[call_cond_elims]:
  "DFS_ret_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl;
    (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_ret_2_conds_def split: list.splits option.splits if_splits)

lemma DFS_ret_2_condsI[call_cond_intros]:
  "\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl; (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow> DFS_ret_2_conds dfs_state"
  by(auto simp: DFS_ret_2_conds_def split: list.splits option.splits if_splits)

abbreviation "DFS_ret2 dfs_state \<equiv> (dfs_state \<lparr>return := Reachable\<rparr>)"

lemma DFS_cases:
  assumes "DFS_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_call_1_conds dfs_state \<or> DFS_call_2_conds dfs_state \<or>
        DFS_ret_1_conds dfs_state \<or> DFS_ret_2_conds dfs_state"
    by (auto simp add: DFS_call_1_conds_def DFS_call_2_conds_def
                        DFS_ret_1_conds_def DFS_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma DFS_simps:
  assumes "DFS_dom dfs_state" 
  shows"DFS_call_1_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS (DFS_upd1 dfs_state)"
      "DFS_call_2_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS (DFS_upd2 dfs_state)"
      "DFS_ret_1_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS_ret1 dfs_state"
      "DFS_ret_2_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS_ret2 dfs_state"
  by (auto simp add: DFS.psimps[OF assms]
                       DFS_call_1_conds_def DFS_upd1_def DFS_call_2_conds_def DFS_upd2_def
                       DFS_ret_1_conds_def
                       DFS_ret_2_conds_def
            split: list.splits option.splits if_splits)

lemma DFS_induct: 
  assumes "DFS_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_dom dfs_state;
                        DFS_call_1_conds dfs_state \<Longrightarrow> P (DFS_upd1 dfs_state);
                        DFS_call_2_conds dfs_state \<Longrightarrow> P (DFS_upd2 dfs_state)\<rbrakk> \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: DFS_call_1_conds_def DFS_upd1_def DFS_call_2_conds_def DFS_upd2_def
           split: list.splits option.splits if_splits)

definition "invar_1 dfs_state \<equiv> neighb_inv (visited dfs_state)"

term DFS.invar_1

lemma invar_1_props[dest!]: "invar_1 dfs_state \<Longrightarrow> neighb_inv (visited dfs_state)"
  by (auto simp: invar_1_def)




lemma invar_1_intro[invar_props_intros]: "neighb_inv (visited dfs_state) \<Longrightarrow> invar_1 dfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]: "\<lbrakk>DFS_call_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def intro: invar_props_intros)

lemma invar_1_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro: invar_props_intros)

lemma invar_1_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

declare[[simp_trace_depth_limit=1000]]

lemma invar_1_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state"
   shows "invar_1 (DFS dfs_state)"
  using assms(2)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros  simp: DFS_simps[OF IH(1)])
qed

definition "invar_2 dfs_state = (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)))"

lemma invar_2_props[dest!]: "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)))"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]: "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (DFS_upd1 dfs_state)"
    using assms
    by (fastforce simp: DFS_upd1_def elim!: call_cond_elims
                intro!: invar_props_intros Vwalk.vwalk_append2)


lemma invar_2_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def dest!: append_vwalk_pref intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_2 dfs_state"
   shows "invar_2 (DFS dfs_state)"
  using assms(2-3)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

\<comment> \<open>Example of funciton package bad ind ppcl?\<close>

definition "invar_3 dfs_state = (\<forall>v \<in> t_set (visited dfs_state). (\<nexists>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t) )"

lemma invar_3_props[elim!]: "invar_3 dfs_state \<Longrightarrow> (\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow> \<not> (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]: "\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow>  \<not> (Vwalk.vwalk_bet (Graph.digraph_abs G) v p t)\<rbrakk> \<Longrightarrow> invar_3 dfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def dest!: append_vwalk_pref intro!: invar_props_intros)

lemma invar_3_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def elim: vwalk_betE  dest!: Graph.neighb.emptyD append_vwalk_pref intro!: invar_props_intros elim!: DFS_call_2_conds; erule vwalk_betE)+

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
              \<equiv> (\<forall>v \<in> set (stack dfs_state_1). ((\<exists>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t) \<or> v = t) \<longrightarrow> v \<in> set (stack dfs_state_2))"

lemma state_rel_2_props[elim!]: "state_rel_2 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  \<lbrakk>\<lbrakk>\<And>v.\<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (auto simp: state_rel_2_def)

lemma state_rel_2_intro[state_rel_intros]: "\<lbrakk>\<And>v. \<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p t) \<or> v = t\<rbrakk>
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
  by (auto simp: DFS_upd2_def elim: vwalk_betE  dest!: Graph.neighb.emptyD append_vwalk_pref intro!: state_rel_intros elim!: DFS_call_2_conds; erule vwalk_betE)+

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
