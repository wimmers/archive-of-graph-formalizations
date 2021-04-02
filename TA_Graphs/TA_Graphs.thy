(*
  Author: Simon Wimmer 
*)

theory TA_Graphs
  imports
    More_List
    "HOL-Library.Rewrite"
begin

chapter \<open>Graphs\<close>

section \<open>Basic Definitions and Theorems\<close>

locale Graph_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive steps where
  Single: "steps [x]" |
  Cons: "steps (x # y # xs)" if "E x y" "steps (y # xs)"

lemmas [intro] = steps.intros

lemma steps_append:
  "steps (xs @ tl ys)" if "steps xs" "steps ys" "last xs = hd ys"
  using that by induction (auto 4 4 elim: steps.cases)

lemma steps_append':
  "steps xs" if "steps as" "steps bs" "last as = hd bs" "as @ tl bs = xs"
  using steps_append that by blast

lemma steps_appendD1:
  "steps xs" if "steps (xs @ ys)" "xs \<noteq> []"
  using that proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by - (cases xs; auto elim: steps.cases)
qed

lemma steps_appendD2:
  "steps ys" if "steps (xs @ ys)" "ys \<noteq> []"
  using that by (induction xs) (auto elim: steps.cases)

lemma steps_appendD3:
  "steps (xs @ [x]) \<and> E x y" if "steps (xs @ [x, y])"
  using that proof (induction xs)
  case Nil
  then show ?case by (auto elim!: steps.cases)
next
  case prems: (Cons a xs)
  then show ?case by (cases xs) (auto elim: steps.cases)
qed

lemma steps_ConsD:
  "steps xs" if "steps (x # xs)" "xs \<noteq> []"
  using that by (auto elim: steps.cases)

lemmas stepsD = steps_ConsD steps_appendD1 steps_appendD2

lemma steps_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "steps x" "(\<And>x. P [x])"
    "\<And>y x xs. E y x \<Longrightarrow> steps (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y,x])"
  shows "P x"
  using assms(1)
  proof (induction rule: rev_induct)
    case Nil
    then show ?case by (auto elim: steps.cases)
  next
    case prems: (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) (auto intro: assms(2,3) dest!: steps_appendD3)
  qed

lemma steps_appendI:
  "steps (xs @ [x, y])" if "steps (xs @ [x])" "E x y"
  using that
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by (cases xs; auto elim: steps.cases)
qed

lemma steps_append_single:
  assumes
    "steps xs" "E (last xs) x" "xs \<noteq> []"
  shows "steps (xs @ [x])"
  using assms(3,1,2) by (induction xs rule: list_nonempty_induct) (auto 4 4 elim: steps.cases)

lemma steps_decomp:
  assumes "steps (xs @ ys)" "xs \<noteq> []" "ys \<noteq> []"
  shows "steps xs \<and> steps ys \<and> E (last xs) (hd ys)"
using assms(2,1,3) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: steps.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: steps.cases)
qed

lemma steps_rotate:
  assumes "steps (x # xs @ y # ys @ [x])"
  shows "steps (y # ys @ x # xs @ [y])"
proof -
  from steps_decomp[of "x # xs" "y # ys @ [x]"] assms have
    "steps (x # xs)" "steps (y # ys @ [x])" "E (last (x # xs)) y"
    by auto
  then have "steps ((x # xs) @ [y])" by (blast intro: steps_append_single)
  from steps_append[OF \<open>steps (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma steps_non_empty[simp]:
  "\<not> steps []"
  by (auto elim: steps.cases)

lemma steps_non_empty'[simp]:
  "xs \<noteq> []" if "steps xs"
  using that by auto

(* XXX Generalize *)
lemma steps_replicate:
  "steps (hd xs # concat (replicate n (tl xs)))" if "last xs = hd xs" "steps xs" "n > 0"
  using that
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems show ?thesis by (cases xs; auto)
  next
    case prems: (Suc nat)
    from Suc.prems have [simp]: "hd xs # tl xs @ ys = xs @ ys" for ys
      by (cases xs; auto)
    from Suc.prems have **: "tl xs @ ys = tl (xs @ ys)" for ys
      by (cases xs; auto)
    from prems Suc show ?thesis
      by (fastforce intro: steps_append')
  qed
qed

notation E ("_ \<rightarrow> _" [100, 100] 40)

abbreviation reaches ("_ \<rightarrow>* _" [100, 100] 40) where "reaches x y \<equiv> E\<^sup>*\<^sup>* x y"

abbreviation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40) where "reaches1 x y \<equiv> E\<^sup>+\<^sup>+ x y"

lemma steps_reaches:
  "hd xs \<rightarrow>* last xs" if "steps xs"
  using that by (induction xs) auto

lemma steps_reaches':
  "x \<rightarrow>* y" if "steps xs" "hd xs = x" "last xs = y"
  using that steps_reaches by auto

lemma reaches_steps:
  "\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs" if "x \<rightarrow>* y"
  using that
  apply (induction)
   apply force
  apply clarsimp
  subgoal for z xs
    by (inst_existentials "xs @ [z]", (cases xs; simp), auto intro: steps_append_single)
  done

lemma reaches_steps_iff:
  "x \<rightarrow>* y \<longleftrightarrow> (\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs)"
  using steps_reaches reaches_steps by fast

lemma steps_reaches1:
  "x \<rightarrow>\<^sup>+ y" if "steps (x # xs @ [y])"
  by (metis list.sel(1,3) rtranclp_into_tranclp2 snoc_eq_iff_butlast steps.cases steps_reaches that)

lemma stepsI:
  "steps (x # xs)" if "x \<rightarrow> hd xs" "steps xs"
  using that by (cases xs) auto

lemma reaches1_steps:
  "\<exists> xs. steps (x # xs @ [y])" if "x \<rightarrow>\<^sup>+ y"
proof -
  from that obtain z where "x \<rightarrow> z" "z \<rightarrow>* y"
    by atomize_elim (simp add: tranclpD)
  from reaches_steps[OF this(2)] obtain xs where *: "hd xs = z" "last xs = y" "steps xs"
    by auto
  then obtain xs' where [simp]: "xs = xs' @ [y]"
    by atomize_elim (auto 4 3 intro: append_butlast_last_id[symmetric])
  with \<open>x \<rightarrow> z\<close> * show ?thesis
    by (auto intro: stepsI)
qed

lemma reaches1_steps_iff:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> xs. steps (x # xs @ [y]))"
  using steps_reaches1 reaches1_steps by fast

lemma reaches_steps_iff2:
  "x \<rightarrow>* y \<longleftrightarrow> (x = y \<or> (\<exists>vs. steps (x # vs @ [y])))"
  by (simp add: Nitpick.rtranclp_unfold reaches1_steps_iff)

lemma reaches1_reaches_iff1:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow> z \<and> z \<rightarrow>* y)"
  by (auto dest: tranclpD)

lemma reaches1_reaches_iff2:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow>* z \<and> z \<rightarrow> y)"
  apply safe
   apply (metis Nitpick.rtranclp_unfold tranclp.cases)
  by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>* y" "y \<rightarrow>\<^sup>+ z"
  using that by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>\<^sup>+ y" "y \<rightarrow>* z"
  using that by auto

lemma steps_append2:
  "steps (xs @ x # ys)" if "steps (xs @ [x])" "steps (x # ys)"
  using that by (auto dest: steps_append)

lemma reaches1_steps_append:
  assumes "a \<rightarrow>\<^sup>+ b" "steps xs" "hd xs = b"
  shows "\<exists> ys. steps (a # ys @ xs)"
  using assms by (fastforce intro: steps_append' dest: reaches1_steps)

lemma steps_last_step:
  "\<exists> a. a \<rightarrow> last xs" if "steps xs" "length xs > 1"
  using that by induction auto

lemma steps_remove_cycleE:
  assumes "steps (a # xs @ [b])"
  obtains ys where "steps (a # ys @ [b])" "distinct ys" "a \<notin> set ys" "b \<notin> set ys" "set ys \<subseteq> set xs"
  using assms
proof (induction "length xs" arbitrary: xs rule: less_induct)
  case less
  note prems = less.prems(2) and intro = less.prems(1) and IH = less.hyps
  consider
    "distinct xs" "a \<notin> set xs" "b \<notin> set xs" | "a \<in> set xs" | "b \<in> set xs" | "\<not> distinct xs"
    by auto
  then consider (goal) ?case
    | (a) as bs where "xs = as @ a # bs" | (b) as bs where "xs = as @ b # bs"
    | (between) x as bs cs where "xs = as @ x # bs @ x # cs"
    using prems by (cases; fastforce dest: not_distinct_decomp simp: split_list intro: intro)
  then show ?case
  proof cases
    case a
    with prems show ?thesis
      by - (rule IH[where xs = bs], auto 4 3 intro: intro dest: stepsD)
  next
    case b
    with prems have "steps (a # as @ b # [] @ (bs @ [b]))"
      by simp
    then have "steps (a # as @ [b])"
      by (metis Cons_eq_appendI Graph_Defs.steps_appendD1 append_eq_appendI neq_Nil_conv)
    with b show ?thesis
      by - (rule IH[where xs = as], auto 4 3 dest: stepsD intro: intro)
  next
    case between
    with prems have "steps (a # as @ x # cs @ [b])"
      by simp (metis
          stepsI append_Cons list.distinct(1) list.sel(1) list.sel(3) steps_append steps_decomp)
    with between show ?thesis
      by - (rule IH[where xs = "as @ x # cs"], auto 4 3 intro: intro dest: stepsD)
  qed
qed

lemma reaches1_stepsE:
  assumes "a \<rightarrow>\<^sup>+ b"
  obtains xs where "steps (a # xs @ [b])" "distinct xs" "a \<notin> set xs" "b \<notin> set xs"
proof -
  from assms obtain xs where "steps (a # xs @ [b])"
    by (auto dest: reaches1_steps)
  then show ?thesis
    by - (erule steps_remove_cycleE, rule that)
qed

lemma reaches_stepsE:
  assumes "a \<rightarrow>* b"
  obtains "a = b" | xs where "steps (a # xs @ [b])" "distinct xs" "a \<notin> set xs" "b \<notin> set xs"
proof -
  from assms consider "a = b" | xs where "a \<rightarrow>\<^sup>+ b"
    by (meson rtranclpD)
  then show ?thesis
    by cases ((erule reaches1_stepsE)?; rule that; assumption)+
qed

definition sink where
  "sink a \<equiv> \<nexists>b. a \<rightarrow> b"

lemma sink_or_cycle:
  assumes "finite {b. reaches a b}"
  obtains b where "reaches a b" "sink b" | b where "reaches a b" "reaches1 b b"
proof -
  let ?S = "{b. reaches1 a b}"
  have "?S \<subseteq> {b. reaches a b}"
    by auto
  then have "finite ?S"
    using assms by (rule finite_subset)
  then show ?thesis
    using that
  proof (induction ?S arbitrary: a rule: finite_psubset_induct)
    case psubset
    consider (empty) "Collect (reaches1 a) = {}" | b where "reaches1 a b"
      by auto
    then show ?case
    proof cases
      case empty
      then have "sink a"
        unfolding sink_def by auto
      with psubset.prems show ?thesis
        by auto
    next
      case 2
      show ?thesis
      proof (cases "reaches b a")
        case True
        with \<open>reaches1 a b\<close> have "reaches1 a a"
          by auto
        with psubset.prems show ?thesis
          by auto
      next
        case False
        show ?thesis
        proof (cases "reaches1 b b")
          case True
          with \<open>reaches1 a b\<close> psubset.prems show ?thesis
            by (auto intro: tranclp_into_rtranclp)
        next
          case False
          with \<open>\<not> reaches b a\<close> \<open>reaches1 a b\<close> have "Collect (reaches1 b) \<subset> Collect (reaches1 a)"
            by (intro psubsetI) auto
          then show ?thesis
            using \<open>reaches1 a b\<close> psubset.prems
            by - (erule psubset.hyps; meson tranclp_into_rtranclp tranclp_rtranclp_tranclp)
        qed
      qed
    qed
  qed
qed

text \<open>
  A directed graph where every node has at least one ingoing edge, contains a directed cycle.
\<close>
lemma directed_graph_indegree_ge_1_cycle':
  assumes "finite S" "S \<noteq> {}" "\<forall> y \<in> S. \<exists> x \<in> S. E x y"
  shows "\<exists> x \<in> S. \<exists> y. E x y \<and> E\<^sup>*\<^sup>* y x"
  using assms
proof (induction arbitrary: E rule: finite_ne_induct)
  case (singleton x)
  then show ?case by auto
next
  case (insert x S E)
  from insert.prems obtain y where "y \<in> insert x S" "E y x"
    by auto
  show ?case
  proof (cases "y = x")
    case True
    with \<open>E y x\<close> show ?thesis by auto
  next
    case False
    with \<open>y \<in> _\<close> have "y \<in> S" by auto
    define E' where "E' a b \<equiv> E a b \<or> (a = y \<and> E x b)" for a b
    have E'_E: "\<exists> c. E a c \<and> E\<^sup>*\<^sup>* c b" if "E' a b" for a b
      using that \<open>E y x\<close> unfolding E'_def by auto
    have [intro]: "E\<^sup>*\<^sup>* a b" if "E' a b" for a b
      using that \<open>E y x\<close> unfolding E'_def by auto
    have [intro]: "E\<^sup>*\<^sup>* a b" if "E'\<^sup>*\<^sup>* a b" for a b
      using that by (induction; blast intro: rtranclp_trans)
    have "\<forall>y\<in>S. \<exists>x\<in>S. E' x y"
    proof (rule ballI)
      fix b assume "b \<in> S"
      with insert.prems obtain a where "a \<in> insert x S" "E a b"
        by auto
      show "\<exists>a\<in>S. E' a b"
      proof (cases "a = x")
        case True
        with \<open>E a b\<close> have "E' y b" unfolding E'_def by simp
        with \<open>y \<in> S\<close> show ?thesis ..
      next
        case False
        with \<open>a \<in> _\<close> \<open>E a b\<close> show ?thesis unfolding E'_def by auto
      qed
    qed
    from insert.IH[OF this] guess x y by safe
    then show ?thesis by (blast intro: rtranclp_trans dest: E'_E)
    qed
  qed

lemma directed_graph_indegree_ge_1_cycle:
  assumes "finite S" "S \<noteq> {}" "\<forall> y \<in> S. \<exists> x \<in> S. E x y"
  shows "\<exists> x \<in> S. \<exists> y. x \<rightarrow>\<^sup>+ x"
  using directed_graph_indegree_ge_1_cycle'[OF assms] reaches1_reaches_iff1 by blast


text \<open>Vertices of a graph\<close>

definition "vertices = {x. \<exists>y. E x y \<or> E y x}"

lemma reaches1_verts:
  assumes "x \<rightarrow>\<^sup>+ y"
  shows "x \<in> vertices" and "y \<in> vertices"
  using assms reaches1_reaches_iff2 reaches1_reaches_iff1 vertices_def by blast+


lemmas graphI =
  steps.intros
  steps_append_single
  steps_reaches'
  stepsI

end (* Graph Defs *)


section \<open>Graphs with a Start Node\<close>

locale Graph_Start_Defs = Graph_Defs +
  fixes s\<^sub>0 :: 'a
begin

definition reachable where
  "reachable = E\<^sup>*\<^sup>* s\<^sub>0"

lemma start_reachable[intro!, simp]:
  "reachable s\<^sub>0"
  unfolding reachable_def by auto

lemma reachable_step:
  "reachable b" if "reachable a" "E a b"
  using that unfolding reachable_def by auto

lemma reachable_reaches:
  "reachable b" if "reachable a" "a \<rightarrow>* b"
  using that(2,1) by induction (auto intro: reachable_step)

lemma reachable_steps_append:
  assumes "reachable a" "steps xs" "hd xs = a" "last xs = b"
  shows "reachable b"
  using assms by (auto intro: graphI reachable_reaches)

lemmas steps_reachable = reachable_steps_append[of s\<^sub>0, simplified]

lemma reachable_steps_elem:
  "reachable y" if "reachable x" "steps xs" "y \<in> set xs" "hd xs = x"
proof -
  from \<open>y \<in> set xs\<close> obtain as bs where [simp]: "xs = as @ y # bs"
    by (auto simp: in_set_conv_decomp)
  show ?thesis
  proof (cases "as = []")
    case True
    with that show ?thesis
      by simp
  next
    case False
    (* XXX *)
    from \<open>steps xs\<close> have "steps (as @ [y])"
      by (auto intro: stepsD)
    with \<open>as \<noteq> []\<close> \<open>hd xs = x\<close> \<open>reachable x\<close> show ?thesis
      by (auto 4 3 intro: reachable_reaches graphI)
  qed
qed

lemma reachable_steps:
  "\<exists> xs. steps xs \<and> hd xs = s\<^sub>0 \<and> last xs = x" if "reachable x"
  using that unfolding reachable_def
proof induction
  case base
  then show ?case by (inst_existentials "[s\<^sub>0]"; force)
next
  case (step y z)
  from step.IH guess xs by clarify
  with step.hyps show ?case
    apply (inst_existentials "xs @ [z]")
    apply (force intro: graphI)
    by (cases xs; auto)+
qed

lemma reachable_cycle_iff:
  "reachable x \<and> x \<rightarrow>\<^sup>+ x \<longleftrightarrow> (\<exists> ws xs. steps (s\<^sub>0 # ws @ [x] @ xs @ [x]))"
proof (safe, goal_cases)
  case (2 ws)
  then show ?case
    by (auto intro: steps_reachable stepsD)
next
  case (3 ws xs)
  then show ?case
    by (auto intro: stepsD steps_reaches1)
next
  case prems: 1
  from \<open>reachable x\<close> prems(2) have "s\<^sub>0 \<rightarrow>\<^sup>+ x"
    unfolding reachable_def by auto
  with \<open>x \<rightarrow>\<^sup>+ x\<close> show ?case
    by (fastforce intro: steps_append' dest: reaches1_steps)
qed

lemma reachable_induct[consumes 1, case_names start step, induct pred: reachable]:
  assumes "reachable x"
    and "P s\<^sub>0"
    and "\<And> a b. reachable a \<Longrightarrow> P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
  shows "P x"
  using assms(1) unfolding reachable_def
  by induction (auto intro: assms(2-)[unfolded reachable_def])

lemmas graphI_aggressive =
  tranclp_into_rtranclp
  rtranclp.rtrancl_into_rtrancl
  tranclp.trancl_into_trancl
  rtranclp_into_tranclp2

lemmas graphI_aggressive1 =
  graphI_aggressive
  steps_append'

lemmas graphI_aggressive2 =
  graphI_aggressive
  stepsD
  steps_reaches1
  steps_reachable

lemmas graphD =
  reaches1_steps

lemmas graphD_aggressive =
  tranclpD

lemmas graph_startI =
  reachable_reaches
  start_reachable

end (* Graph Start Defs *)


section \<open>Subgraphs\<close>

subsection \<open>Edge-induced Subgraphs\<close>

locale Subgraph_Defs = G: Graph_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Defs E' .

end (* Subgraph Defs *)

locale Subgraph_Start_Defs = G: Graph_Start_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Start_Defs E' s\<^sub>0 .

end (* Subgraph Start Defs *)

locale Subgraph = Subgraph_Defs +
  assumes subgraph[intro]: "E' a b \<Longrightarrow> E a b"
begin

lemma non_subgraph_cycle_decomp:
  "\<exists> c d. G.reaches a c \<and> E c d \<and> \<not> E' c d \<and> G.reaches d b" if
  "G.reaches1 a b" "\<not> G'.reaches1 a b" for a b
    using that
  proof induction
    case (base y)
    then show ?case
      by auto
  next
    case (step y z)
    show ?case
    proof (cases "E' y z")
      case True
      with step have "\<not> G'.reaches1 a y"
        by (auto intro: tranclp.trancl_into_trancl) (* XXX *)
      with step obtain c d where
        "G.reaches a c" "E c d" "\<not> E' c d" "G.reaches d y"
        by auto
      with \<open>E' y z\<close> show ?thesis
        by (blast intro: rtranclp.rtrancl_into_rtrancl) (* XXX *)
    next
      case False
      with step show ?thesis
        by (intro exI conjI) auto
    qed
  qed

lemma reaches:
  "G.reaches a b" if "G'.reaches a b"
  using that by induction (auto intro: rtranclp.intros(2))

lemma reaches1:
  "G.reaches1 a b" if "G'.reaches1 a b"
  using that by induction (auto intro: tranclp.intros(2))

end (* Subgraph *)

locale Subgraph_Start = Subgraph_Start_Defs + Subgraph
begin

lemma reachable_subgraph[intro]: "G.reachable b" if \<open>G.reachable a\<close> \<open>G'.reaches a b\<close> for a b
  using that by (auto intro: G.graph_startI mono_rtranclp[rule_format, of E'])

lemma reachable:
  "G.reachable x" if "G'.reachable x"
  using that by (fastforce simp: G.reachable_def G'.reachable_def)

end (* Subgraph Start *)

subsection \<open>Node-induced Subgraphs\<close>

locale Subgraph_Node_Defs = Graph_Defs +
  fixes V :: "'a \<Rightarrow> bool"
begin

definition E' where "E' x y \<equiv> E x y \<and> V x \<and> V y"

sublocale Subgraph E E' by standard (auto simp: E'_def)

lemma subgraph':
  "E' x y" if "E x y" "V x" "V y"
  using that unfolding E'_def by auto

lemma E'_V1:
  "V x" if "E' x y"
  using that unfolding E'_def by auto

lemma E'_V2:
  "V y" if "E' x y"
  using that unfolding E'_def by auto

lemma G'_reaches_V:
  "V y" if "G'.reaches x y" "V x"
  using that by (cases) (auto intro: E'_V2)

lemma G'_steps_V_all:
  "list_all V xs" if "G'.steps xs" "V (hd xs)"
  using that by induction (auto intro: E'_V2)

lemma G'_steps_V_last:
  "V (last xs)" if "G'.steps xs" "V (hd xs)"
  using that by induction (auto dest: E'_V2)

lemmas subgraphI = E'_V1 E'_V2 G'_reaches_V

lemmas subgraphD = E'_V1 E'_V2 G'_reaches_V

end (* Subgraph Node *)


locale Subgraph_Node_Defs_Notation = Subgraph_Node_Defs
begin

no_notation E ("_ \<rightarrow> _" [100, 100] 40)
notation E' ("_ \<rightarrow> _" [100, 100] 40)
no_notation reaches ("_ \<rightarrow>* _" [100, 100] 40)
notation G'.reaches ("_ \<rightarrow>* _" [100, 100] 40)
no_notation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)
notation G'.reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)

end (* Subgraph_Node_Defs_Notation *)


subsection \<open>The Reachable Subgraph\<close>

context Graph_Start_Defs
begin

interpretation Subgraph_Node_Defs_Notation E reachable .

sublocale reachable_subgraph: Subgraph_Node_Defs E reachable .

lemma reachable_supgraph:
  "x \<rightarrow> y" if "E x y" "reachable x"
  using that unfolding E'_def by (auto intro: graph_startI)

lemma reachable_reaches_equiv: "reaches x y \<longleftrightarrow> x \<rightarrow>* y" if "reachable x" for x y
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: reachable_supgraph intro: graph_startI graphI_aggressive)
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: subgraph)
  done

lemma reachable_reaches1_equiv: "reaches1 x y \<longleftrightarrow> x \<rightarrow>\<^sup>+ y" if "reachable x" for x y
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: reachable_supgraph intro: graph_startI graphI_aggressive)
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: subgraph)
  done

lemma reachable_steps_equiv:
  "steps (x # xs) \<longleftrightarrow> G'.steps (x # xs)" if "reachable x"
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by (induction "x # xs" arbitrary: x xs) (auto dest: reachable_supgraph intro: graph_startI)
  subgoal premises prems
    using prems by induction auto
  done

end (* Graph Start Defs *)


section \<open>Bundles\<close>

bundle graph_automation
begin

lemmas [intro] = Graph_Defs.graphI Graph_Start_Defs.graph_startI
lemmas [dest]  = Graph_Start_Defs.graphD

end (* Bundle *)

bundle reaches_steps_iff =
  Graph_Defs.reaches1_steps_iff [iff]
  Graph_Defs.reaches_steps_iff  [iff]

bundle graph_automation_aggressive
begin

unbundle graph_automation

lemmas [intro] = Graph_Start_Defs.graphI_aggressive
lemmas [dest]  = Graph_Start_Defs.graphD_aggressive

end (* Bundle *)

bundle subgraph_automation
begin

unbundle graph_automation

lemmas [intro] = Subgraph_Node_Defs.subgraphI
lemmas [dest]  = Subgraph_Node_Defs.subgraphD

end (* Bundle *)


section \<open>Directed Acyclic Graphs\<close>
locale DAG = Graph_Defs +
  assumes acyclic: "\<not> E\<^sup>+\<^sup>+ x x"
begin

lemma topological_numbering:
  fixes S assumes "finite S"
  shows "\<exists>f :: _ \<Rightarrow> nat. inj_on f S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. E x y \<longrightarrow> f x < f y)"
  using assms
proof (induction rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "A = {}")
    case True
    then show ?thesis
      by simp
  next
    case False
    then obtain x where x: "x \<in> A" "\<forall>y \<in> A. \<not>E y x"
      using directed_graph_indegree_ge_1_cycle[OF \<open>finite A\<close>] acyclic by auto
    let ?A = "A - {x}"
    from \<open>x \<in> A\<close> have "?A \<subset> A"
      by auto
    from psubset.IH(1)[OF this] obtain f :: "_ \<Rightarrow> nat" where f:
      "inj_on f ?A" "\<forall>x\<in>?A. \<forall>y\<in>?A. x \<rightarrow> y \<longrightarrow> f x < f y"
      by blast
    let ?f = "\<lambda>y. if x \<noteq> y then f y + 1 else 0"
    from \<open>x \<in> A\<close> have "A = insert x ?A"
      by auto
    from \<open>inj_on f ?A\<close> have "inj_on ?f A"
      by (auto simp: inj_on_def)
    moreover from f(2) x(2) have "\<forall>x\<in>A. \<forall>y\<in>A. x \<rightarrow> y \<longrightarrow> ?f x < ?f y"
      by auto
    ultimately show ?thesis
      by blast
  qed
qed

end


section \<open>Finite Graphs\<close>

locale Finite_Graph = Graph_Defs +
  assumes finite_graph: "finite vertices"

locale Finite_DAG = Finite_Graph + DAG
begin

lemma finite_reachable:
  "finite {y. x \<rightarrow>* y}" (is "finite ?S")
proof -
  have "?S \<subseteq> insert x vertices"
    by (metis insertCI mem_Collect_eq reaches1_verts(2) rtranclpD subsetI)
  moreover from finite_graph have "finite (insert x vertices)"
    ..
  ultimately show ?thesis 
    using infinite_super
    by auto
qed

end


section \<open>Graph Invariants\<close>

locale Graph_Invariant = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
begin

lemma invariant_steps:
  "list_all P as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma invariant_reaches:
  "P b" if "a \<rightarrow>* b" "P a"
  using that by (induction; blast intro: invariant)

text \<open>Every graph invariant induces a subgraph.\<close>
sublocale Subgraph_Node_Defs where E = E and V = P .

lemma subgraph':
  assumes "x \<rightarrow> y" "P x"
  shows "E' x y"
  using assms by (intro subgraph') (auto intro: invariant)

lemma invariant_steps_iff:
  "G'.steps (v # vs) \<longleftrightarrow> steps (v # vs)" if "P v"
  apply (rule iffI)
  subgoal
    using G'.steps_alt_induct steps_appendI
          Single
    by blast
  subgoal premises prems
    using prems \<open>P v\<close> by (induction "v # vs" arbitrary: v vs) (auto intro: subgraph' invariant)
  done

lemma invariant_reaches_iff:
  "G'.reaches u v \<longleftrightarrow> reaches u v" if "P u"
  using that by (simp add: reaches_steps_iff2 G'.reaches_steps_iff2 invariant_steps_iff)

lemma invariant_reaches1_iff:
  "G'.reaches1 u v \<longleftrightarrow> reaches1 u v" if "P u"
  using that by (simp add: reaches1_steps_iff G'.reaches1_steps_iff invariant_steps_iff)

end (* Graph Invariant *)

locale Graph_Invariants = Graph_Defs +
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> Q b" and Q_P: "Q a \<Longrightarrow> P a"
begin

sublocale Pre: Graph_Invariant E P
  by standard (blast intro: invariant Q_P)

sublocale Post: Graph_Invariant E Q
  by standard (blast intro: invariant Q_P)

lemma invariant_steps:
  "list_all Q as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant Q_P)

lemma invariant_reaches1:
  "Q b" if "a \<rightarrow>\<^sup>+ b" "P a"
  using that by (induction; blast intro: invariant Q_P)

end (* Graph Invariants *)

locale Graph_Invariant_Start = Graph_Start_Defs + Graph_Invariant +
  assumes P_s\<^sub>0: "P s\<^sub>0"
begin

lemma invariant_steps:
  "list_all P as" if "steps (s\<^sub>0 # as)"
  using that P_s\<^sub>0 by (rule invariant_steps)

lemma invariant_reaches:
  "P b" if "s\<^sub>0 \<rightarrow>* b"
  using invariant_reaches[OF that P_s\<^sub>0] .

end (* Graph Invariant Start *)

locale Graph_Invariant_Strong = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "a \<rightarrow> b \<Longrightarrow> P b"
begin

sublocale inv: Graph_Invariant by standard (rule invariant)

lemma P_invariant_steps:
  "list_all P as" if "steps (a # as)"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma steps_last_invariant:
  "P (last xs)" if "steps (x # xs)" "xs \<noteq> []"
  using steps_last_step[of "x # xs"] that by (auto intro: invariant)

lemmas invariant_reaches = inv.invariant_reaches

lemma invariant_reaches1:
  "P b" if "a \<rightarrow>\<^sup>+ b"
  using that by (induction; blast intro: invariant)

end (* Graph Invariant *)

end (* Theory *)
