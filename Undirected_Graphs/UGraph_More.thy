theory UGraph_More
  imports Kruskal.UGraph Matroids.Matroid Kruskal.Kruskal_Misc
begin



context uGraph
begin

text \<open>This theory proves that @{term subforest}s in uGraph forms a Matroid.

  It collects material from \<open>Kruskal.Kruskal\<close> and \<open>Kruskal.UGraph_Impl\<close> to
  present the essentials together. 
 \<close>



lemma forest_empty: "forest {}"
  apply (auto simp: decycle_def forest_def)
  using epath.elims(2) by fastforce 


subsection \<open>Interface lemmas about subforests and uconnectedV\<close> 


abbreviation "V == verts"
abbreviation vertices :: "'b uprod \<Rightarrow> 'b set"
  where "vertices == set_uprod"
abbreviation joins :: "'b \<Rightarrow> 'b \<Rightarrow> 'b uprod \<Rightarrow> bool"
  where"joins == \<lambda>u v e. Upair u v = e"

lemma subforest_subset_E: "subforest E' \<Longrightarrow> E' \<subseteq> E" 
  by (auto simp: subforest_def)

lemma subforest_empty: "subforest {}"
  by (auto simp: subforest_def forest_empty) 

lemma subforest_mono: "subforest X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> subforest Y"  
  unfolding subforest_def using forest_mono by blast

lemma uconnectedV_same: "(u,v) \<in> uconnectedV {} \<longleftrightarrow> u=v \<and> v\<in>V"
  unfolding uconnected_def apply auto 
  using epath.elims(2) by force 

lemma findaugmenting_aux: "E1 \<subseteq> E \<Longrightarrow> E2 \<subseteq> E \<Longrightarrow> (u,v) \<in> uconnectedV E1 \<Longrightarrow> (u,v)\<notin> uconnectedV E2
           \<Longrightarrow> \<exists>a b e. (a,b) \<notin> uconnectedV E2 \<and> e \<notin> E2 \<and> e \<in> E1 \<and> joins a b e" 
proof (goal_cases)
  case 1
  then have "(u, v) \<in> (uconnected E1)" and uv: "u \<in> V" "v \<in> V"
    by auto
  then obtain p where *: "epath E1 u p v" unfolding uconnected_def by auto 
  from 1 uv have **: "\<not>(\<exists>p.  epath E2 u p v)" unfolding uconnected_def by auto
  from * ** have "\<exists>a b. (a, b) \<notin> uconnected E2
           \<and> Upair a b \<notin> E2 \<and> Upair a b \<in> E1" by(rule findaugmenting_edge)
  then show ?case by auto
qed

lemma augment_subforest: "subforest F \<Longrightarrow> e \<in> E-F \<Longrightarrow> joins u v e
           \<Longrightarrow> subforest (insert e F) \<longleftrightarrow> (u,v) \<notin> uconnectedV F"  
  unfolding subforest_def
proof (goal_cases)
  case 1
  note f = \<open>forest F \<and> F \<subseteq> E\<close>
  note notin = \<open>e \<in> E - F\<close> \<open>Upair u v = e\<close>
  from notin ecard2 have unv: "u\<noteq>v" by fastforce
  show "(forest (insert e F) \<and> insert e F \<subseteq> E) = ((u, v) \<notin> uconnectedV F)"
  proof
    assume a: "forest (insert e F) \<and> insert e F \<subseteq> E "
    have "(u, v) \<notin> uconnected F" apply(rule insert_stays_forest_means_not_connected)
      using notin a unv by auto
    then show "((u, v) \<notin> Restr (uconnected F) V)" by auto
  next 
    assume a: "(u, v) \<notin> Restr (uconnected F) V"
    have "forest (insert (Upair u v) F)" apply(rule augment_forest_overedges[where E=E])
      using notin f a unv  by auto 
    moreover have "insert e F \<subseteq> E"
      using notin f by auto
    ultimately show "forest (insert e F) \<and> insert e F \<subseteq> E" using notin by auto
  qed
qed

lemma equiv: "F \<subseteq> E \<Longrightarrow> equiv V (uconnectedV F)"
  by(rule equiv_vert_uconnected)

lemma uconnectedV_in: "F \<subseteq> E \<Longrightarrow> uconnectedV F \<subseteq> V \<times> V"     
  by auto

lemma insert_reachable: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> F \<subseteq> E \<Longrightarrow> e\<in>E \<Longrightarrow> joins x y e
           \<Longrightarrow> uconnectedV (insert e F) = per_union (uconnectedV F) x y"   
  using insert_uconnectedV_per' by metis

lemma exhaust: "e\<in>E \<Longrightarrow> \<exists>a b. joins a b e"
  apply(cases e) by auto

lemma vertices_constr: "\<And>a b e. joins a b e \<Longrightarrow> {a,b} \<subseteq> vertices e"
  by auto

lemma joins_sym: "\<And>a b e. joins a b e = joins b a e"
  by auto

lemma selfloop_no_subforest: "\<And>e. e\<in>E \<Longrightarrow> joins a a e \<Longrightarrow> ~subforest (insert e F)"
  using ecard2 by force

lemma finite_vertices: "\<And>e. e\<in>E \<Longrightarrow> finite (vertices e)"
  using ecard2 by auto

lemma edgesinvertices: "\<Union>( vertices ` E) \<subseteq> V"
  by auto

lemma finiteV[simp]: "finite V"
  by simp

lemma joins_uconnectedV: "joins a b e \<Longrightarrow> T\<subseteq>E \<Longrightarrow> e\<in>T \<Longrightarrow> (a,b) \<in> uconnectedV T"
  apply auto
  subgoal unfolding uconnected_def apply auto apply(rule exI[where x="[e]"]) apply simp
    using ecard2 by force
  subgoal by force
  subgoal by force 
  done



subsection \<open>derived facts from the above interface lemmas\<close> 


lemma joins_in_V: "joins a b e \<Longrightarrow> e\<in>E \<Longrightarrow> a\<in>V \<and> b\<in>V"
  apply(frule vertices_constr) using edgesinvertices by blast

lemma finiteE_finiteV: "finite E \<Longrightarrow> finite V"
  using finite_vertices by auto

lemma E_inV: "\<And>e. e\<in>E \<Longrightarrow> vertices e \<subseteq> V"
  using edgesinvertices by auto  

definition "CC E' x = (uconnectedV E')``{x}"      

lemma sameCC_reachable: "E' \<subseteq> E \<Longrightarrow> u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E' u = CC E' v \<longleftrightarrow> (u,v) \<in> uconnectedV E'"
  unfolding CC_def using  equiv_class_eq_iff[OF equiv ] by metis

definition "CCs E' = quotient verts (uconnectedV E')"  

lemma "quotient V Id = {{v}|v. v\<in>V}" unfolding quotient_def by auto  

definition "connected E' \<equiv> Restr (uconnected E') verts"
definition "VV   \<equiv> V"
lemma CCs_empty: "CCs {} = {{v}|v. v\<in>V}"  
proof -
  have *: "(\<And>u v. ((u, v) \<in> X) = (u = v \<and> v \<in> Y))
           \<Longrightarrow> (\<Union>x\<in>Y. {X `` {x}}) = {{v} |v. v \<in> Y}" for X :: "('a \<times> 'a) set" and Y
    by auto
  show ?thesis 
    unfolding CCs_def unfolding quotient_def
    by (rule *) (fact uconnectedV_same) 
qed

lemma CCs_empty_card: "card (CCs {}) = card V"   
proof -
  have i: "{{v}|v. v\<in>V} = (\<lambda>v. {v})`V"  
    by blast 
  have "card (CCs {}) = card {{v}|v. v\<in>V}" 
    using CCs_empty  by auto
  also have "\<dots> = card ((\<lambda>v. {v})`V)" by(simp only: i) 
  also have "\<dots> = card V"
    apply(rule card_image)
    unfolding inj_on_def by auto
  finally show ?thesis .
qed

lemma CCs_imageCC: "CCs F = (CC F) ` V"
  unfolding CCs_def CC_def quotient_def  
  by blast


lemma union_eqclass_decreases_components: 
  assumes "CC F x \<noteq> CC F y" "e \<notin> F" "x\<in>V" "y\<in>V" "F \<subseteq> E" "e\<in>E" "joins x y e" 
  shows "Suc (card (CCs (insert e F))) = card (CCs F)"
proof -  
  from assms(1) have xny: "x\<noteq>y" by blast   
  show ?thesis unfolding CCs_def
    apply(simp only: insert_reachable[OF   assms(3-7)])
    apply(rule unify2EquivClasses_alt)          
         apply(fact assms(1)[unfolded CC_def])                           
        apply fact+
      apply (rule uconnectedV_in)  
      apply fact    
     apply(rule equiv) 
     apply fact  
    by (fact finiteV)      
qed

lemma subforest_CCs: assumes "subforest E'" shows "card (CCs E') + card E' = card V"
proof -
  from assms have "finite E'" using subforest_subset_E
    using finiteE finite_subset by blast
  from this assms show ?thesis
  proof(induct E') 
    case (insert x F)
    then have xE: "x\<in>E" using subforest_subset_E by auto
    from this obtain a b where xab: "joins a b x"  using exhaust by blast
    { assume "a=b"
      with xab xE selfloop_no_subforest insert(4) have "False" by auto
    }
    then have xab': "a\<noteq>b" by auto
    from insert(4) subforest_mono have fF: "subforest F" by auto
    with insert(3) have eq: "card (CCs F) + card F = card V" by auto 

    from insert(4) subforest_subset_E have k: "F \<subseteq> E" by auto     
    from xab xab' have abV: "a\<in>V" "b\<in>V" using vertices_constr E_inV xE by fastforce+

    have "(a,b) \<notin> uconnectedV F" 
      apply(subst augment_subforest[symmetric])
         apply (rule fF)
      using xE xab xab insert by auto
    with k abV sameCC_reachable have "CC F a \<noteq> CC F b" by auto 
    have "Suc (card (CCs (insert x F))) = card (CCs F)" 
      apply(rule union_eqclass_decreases_components)  
      by fact+ 
    then show ?case using xab insert(1,2) eq   by auto 
  qed (simp add: CCs_empty_card)
qed

lemma pigeonhole_CCs: 
  assumes finiteV: "finite V" and cardlt: "card (CCs E1) < card (CCs E2)"
  shows "(\<exists>u v. u\<in>V \<and> v\<in>V \<and> CC E1 u = CC E1 v \<and> CC E2 u \<noteq> CC E2 v)"  
proof (rule ccontr, clarsimp)
  assume " \<forall>u. (\<forall>x\<in>E. u \<notin> set_uprod x)
             \<or> (\<forall>v. CC E1 u = CC E1 v \<longrightarrow> (\<forall>x\<in>E. v \<notin> set_uprod x) \<or> CC E2 u = CC E2 v)"
  then have "\<forall>u. u \<in> V \<longrightarrow> (\<forall>v. CC E1 u = CC E1 v \<longrightarrow> v \<in> V \<longrightarrow> CC E2 u = CC E2 v)"
    by blast
  then have "\<And>u v. u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E1 u = CC E1 v \<Longrightarrow> CC E2 u = CC E2 v" by blast

  with coarser[OF finiteV] have "card ((CC E1) ` V) \<ge> card ((CC E2) ` V)" by blast

  with CCs_imageCC cardlt show "False" by auto
qed

theorem assumes f1: "subforest E1"
  and f2: "subforest E2"  
  and c: "card E1 > card E2"
shows augment: "\<exists>e\<in>E1-E2. subforest (insert e E2)"
proof -
  \<comment> \<open>as E1 and E2 are both forests, and E1 has more edges than E2, E2 has more connected
        components than E1\<close> 
  from subforest_CCs[OF f1] subforest_CCs[OF f2] c have "card (CCs E1) < card (CCs E2)" by linarith

  \<comment> \<open>by an pigeonhole argument, we can obtain two vertices u and v
     that are in the same components of E1, but in different components of E2\<close>
  then obtain u v where sameCCinE1: "CC E1 u = CC E1 v" and
    diffCCinE2: "CC E2 u \<noteq> CC E2 v" and k: "u \<in> V" "v \<in> V"
    using pigeonhole_CCs[OF finiteV] by blast   

  from diffCCinE2 have unv: "u \<noteq> v" by auto

  \<comment> \<open>this means that there is a path from u to v in E1 ...\<close>   
  from f1 subforest_subset_E have e1: "E1 \<subseteq> E" by auto    
  with   sameCC_reachable k sameCCinE1 have pathinE1: "(u, v) \<in> uconnectedV E1" 
    by auto 
      \<comment> \<open>... but none in E2\<close>  
  from f2 subforest_subset_E have e2: "E2 \<subseteq> E" by auto    
  with   sameCC_reachable k diffCCinE2
  have nopathinE2: "(u, v) \<notin> uconnectedV E2" 
    by auto

  \<comment> \<open>hence, we can find vertices a and b that are not connected in E2,
          but are connected by an edge in E1\<close>    
  obtain a b e where pe: "(a,b) \<notin> uconnectedV E2" and abE2: "e \<notin> E2"
    and abE1: "e \<in> E1" and "joins a b e"
    using findaugmenting_aux[OF e1 e2 pathinE1 nopathinE2]    by auto

  with subforest_subset_E[OF f1] have "e \<in> E" by auto
  from abE1 abE2 have abdif: "e \<in> E1 - E2" by auto
  with e1 have "e \<in> E - E2" by auto

  \<comment> \<open>we can savely add this edge between a and b to E2 and obtain a bigger forest\<close>    
  have "subforest (insert e E2)" apply(subst augment_subforest)
    by fact+
  then show "\<exists>e\<in>E1-E2. subforest (insert e E2)" using abdif
    by blast
qed


sublocale matroid E subforest 
  apply (unfold_locales) 
  subgoal by simp
  subgoal by (fact subforest_subset_E)
  subgoal using subforest_empty by blast
  subgoal by (fact subforest_mono)
  subgoal using augment by simp
  done



end
 
end