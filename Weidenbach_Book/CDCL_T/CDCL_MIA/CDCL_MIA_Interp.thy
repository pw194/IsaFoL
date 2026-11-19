theory CDCL_MIA_Interp
imports CDCL_MIA_Models
begin

section \<open>MIA theory_problem interpretation\<close>

subsection \<open>Integral constraint\<close>
text \<open>Since we require this constraint a lot for the mixed formulas, I will use an abbreviation
      so that we do not have to unfold definitions about it all the time, and also do not nest
      definitions too deeply.\<close>
abbreviation wf_integral :: \<open>(nat \<Rightarrow> real) \<Rightarrow> var set \<Rightarrow> bool\<close> where
  \<open>wf_integral v Is \<equiv> (\<forall>x \<in> Is. v x \<in> \<int>)\<close>

subsection \<open>Model based acceptance and entailment\<close>
text \<open>This is our \<open>I \<Turnstile>\<^sub>\<T> P\<close>. It models asking the \<T>-solver for the consistency of
      a set of theory literals (which implicitly means the consistency of the conjunction of
      theory literals).\<close>
definition theory_check_mia :: \<open>'b mia_atom literal set \<Rightarrow> mia_problem \<Rightarrow> bool\<close> where
  \<open>theory_check_mia I P = (\<exists>v \<beta>. (wf_integral v P) \<and> (\<forall>L \<in> I. holds_lit v \<beta> L))\<close>

text \<open>This is our \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close>. A clause set N is entailed by P if all the clauses in it are
      theory valid.\<close>
definition theory_entails_clauses_mia :: \<open>mia_problem \<Rightarrow> 'b mia_atom clauses \<Rightarrow> bool\<close> where
  \<open>theory_entails_clauses_mia P N = (\<forall>v \<beta>. (wf_integral v P) \<longrightarrow> (\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L))\<close>

subsection \<open>Lemmas needed for the interpretation\<close>
lemma holds_lit_conflict:
  assumes pos: \<open>holds_lit v \<beta> L\<close> and neg: \<open>holds_lit v \<beta> (-L)\<close>
  shows \<open>False\<close>
  using assms
proof (induction L)
  case (Pos x)
  then show ?case 
  proof (cases x)
    case (ArithAtom x1)
    then show ?thesis using Pos by auto
  next
    case (BoolAtom x2)
    then show ?thesis using Pos by auto
  qed
next
  case (Neg x)
  then show ?case proof (cases x)
    case (ArithAtom x1)
    then show ?thesis using Neg by auto
  next
    case (BoolAtom x2)
    then show ?thesis using Neg by auto
  qed
qed

lemma holds_lit_neg: \<open>\<not> holds_lit v \<beta> L \<Longrightarrow> holds_lit v \<beta> (-L)\<close>
proof (induction L)
  case (Pos x)
  then show ?case
    proof (cases x)
      case (ArithAtom x1)
      then show ?thesis using Pos by auto
    next
      case (BoolAtom x2)
      then show ?thesis using Pos by auto
    qed
next
  case (Neg x)
  then show ?case
    proof (cases x)
      case (ArithAtom x1)
      then show ?thesis using Neg by auto
    next
      case (BoolAtom x2)
      then show ?thesis using Neg by auto
    qed
qed

lemma holds_lit_valid: \<open>holds_lit v \<beta> L \<or> holds_lit v \<beta> (- L)\<close>
  using holds_lit_neg by blast

lemma theory_implies_prop: 
  assumes cons: \<open>consistent_interp I\<close> 
      and atms: \<open>atm_of ` I = atms_of_mm N\<close> 
      and tent: \<open>theory_entails_clauses_mia P N\<close> 
     and check: \<open>theory_check_mia I P\<close> 
   shows \<open>I \<Turnstile>sm N\<close>
proof
  obtain v \<beta> where integral: \<open>(wf_integral v P)\<close> and holds: \<open>(\<forall>L \<in> I. holds_lit v \<beta> L)\<close>
    using assms by (auto simp: theory_check_mia_def)
  then have H1: \<open>(\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L)\<close>
    using tent theory_entails_clauses_mia_def by blast
  then have mutual: \<open>(\<forall>C \<in># N. \<exists>L \<in># C. (L \<in> I \<and> -L \<notin> I) \<or> (-L \<in> I \<and> L \<notin> I))\<close>
    using atms holds by (metis atm_of_in_atm_of_set_in_uminus holds_lit_conflict in_implies_atm_of_on_atms_of_ms)
    have \<open>\<forall>C \<in># N. \<exists>L \<in># C. L \<in> I\<close>
  proof
    fix C
    assume A1: \<open>C \<in># N\<close>
    show \<open>\<exists>L\<in>#C. L \<in> I\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>(\<forall>L\<in>#C. L \<notin> I)\<close> by auto
      then have H2: \<open>(\<forall>L\<in>#C. -L \<in> I)\<close> using mutual A1 using atms by (metis atm_of_in_atm_of_set_in_uminus in_implies_atm_of_on_atms_of_ms) 
      then have \<open>(\<forall>L\<in>I. holds_lit v \<beta> L)\<close> using holds by blast 
      then show \<open>False\<close>
        using A1 H1 H2 holds_lit_conflict by blast 
    qed
  qed
  then show \<open>I \<Turnstile>m N\<close>
    by (simp add: true_cls_def true_cls_mset_def)
qed

subsection \<open>The interpretation\<close>

lemma ax1:
  assumes check: \<open>theory_check_mia I P\<close> 
       and tent: \<open>theory_entails_clauses_mia P {#C#}\<close> 
       and atms: \<open>atms_of C \<subseteq> atm_of ` I\<close> 
  shows \<open>I \<Turnstile> C\<close>
proof(rule ccontr)
  obtain v \<beta> where integral: \<open>(wf_integral v P)\<close> and holds: \<open>(\<forall>L \<in> I. holds_lit v \<beta> L)\<close>
    using assms(1) by (auto simp: theory_check_mia_def)
  then have ex: \<open>\<exists>L \<in># C. holds_lit v \<beta> L\<close>
    using tent unfolding theory_entails_clauses_mia_def
    by auto 
  assume \<open>\<not> I \<Turnstile> C\<close>
  then have all: \<open>\<forall>L \<in># C. -L \<in> I\<close>
    using atms by (metis atm_of_in_atm_of_set_in_uminus atms_of_def in_set_image_subsetD insert_DiffM true_cls_add_mset) 
  then show \<open>False\<close>
    using ex holds_lit_conflict holds by blast
qed

lemma ax2:
  assumes cons: \<open>consistent_interp I\<close> 
      and atms: \<open>atm_of ` I = atms_of_mm N\<close> 
       and sat: \<open>I \<Turnstile>sm N\<close>
  shows \<open>theory_check_mia I P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses_mia P {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close>
proof (cases \<open>theory_check_mia I P\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding theory_check_mia_def
  proof(intro disjI2)
    let ?C = \<open>{#- L. L \<in># mset_set I#}\<close>
    assume A1: \<open>\<not> (\<exists>v \<beta>. (wf_integral v P) \<and> (\<forall>L \<in> I. holds_lit v \<beta> L))\<close>
    have \<open>finite (atm_of ` I)\<close> by (simp add: assms(2)) 
    moreover have \<open>I \<subseteq> Pos ` (atm_of ` I) \<union> Neg ` (atm_of ` I)\<close> by (smt (cvc5, interleave) Set.basic_monos(7) Un_subset_iff imageI imageI literal.exhaust_sel subsetI) 
    ultimately have fin: \<open>finite I\<close> using atms
     by (metis finite_imageI infinite_Un rev_finite_subset)
     have cnot: \<open>I \<Turnstile>s CNot ?C\<close> using cons by (simp add: fin true_clss_def_iff_negation_in_model) 
    have atmsub: \<open>atms_of ?C \<subseteq> atm_of ` I\<close> using fin by (metis atms_of_def atms_of_pNeg finite_set_mset_mset_set pNeg_def set_eq_subset)
    have dis: \<open>distinct_mset ?C\<close> by (metis distinct_mset_pNeg_iff is_mset_set pNeg_def)
    have taut: \<open>\<not>tautology ?C\<close> using assms(1) cnot consistent_CNot_not_tautology by blast 
    have tent: \<open>theory_entails_clauses_mia P {#?C#}\<close>
      unfolding theory_entails_clauses_mia_def
      proof(intro allI impI ballI)
      fix v \<beta> C
      assume A2: \<open>wf_integral v P\<close> and
        C: \<open>C\<in>#{#uminus `# mset_set I#}\<close>
      have \<open>\<exists>L \<in># ?C. holds_lit v \<beta> L\<close>
      proof (rule ccontr)
        assume A3: \<open>\<not> ?thesis\<close>
        then have \<open>(\<forall>L\<in>#?C. holds_lit v \<beta> (-L))\<close>
          using holds_lit_neg by auto
        then show \<open>False\<close>
          using A1 A2 A3 fin by (metis elem_mset_set holds_lit_neg image_msetI)
      qed
      then show \<open>Multiset.Bex C (holds_lit v \<beta>)\<close>
        using C by (metis in_multiset_nempty member_add_mset)
    qed
   then show \<open>\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses_mia P {#C#} \<and> C \<in> simple_clss (atm_of ` I)\<close>
     using atmsub cnot dis taut by (meson distinct_mset_not_tautology_implies_in_simple_clss in_mono simple_clss_mono)
 qed
qed

lemma ax3:
  assumes cons: \<open>consistent_interp I\<close> 
      and atms: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close> 
      and check: \<open>theory_check_mia I P\<close> 
  shows \<open>\<exists>J. (theory_check_mia J P) \<and> I \<subseteq> J \<and> (atm_of ` J = atms_of_mm N) \<and> consistent_interp J\<close>
proof -
  obtain v \<beta> where integral: \<open>(wf_integral v P)\<close> and holds: \<open>(\<forall>L \<in> I. holds_lit v \<beta> L)\<close>
    using assms by (auto simp: theory_check_mia_def)
  let ?J = \<open>I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> (atm_of ` I) \<and> holds_lit v \<beta> L}\<close>
  have H1: \<open>I \<subseteq> ?J\<close> by auto
  have H2: \<open>(atm_of ` ?J = atms_of_mm N)\<close>
  proof
    show \<open>atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L}) \<subseteq> atms_of_mm N\<close>
      using assms(2) by fastforce
    show \<open>atms_of_mm N \<subseteq> atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L})\<close>
    proof 
      fix x
      assume A: \<open>x \<in> atms_of_mm N\<close>
      then show \<open>x \<in> atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L})\<close>
        proof (cases \<open>x \<in> atm_of ` I\<close>)
          case True
          then show ?thesis
            by blast 
        next
          case False
          have \<open>holds_lit v \<beta> (Pos x) \<or> holds_lit v \<beta> (Neg x)\<close>
            by auto
          then show ?thesis
            using False A by (metis (lifting) Un_iff imageI literal.sel(1,2) mem_Collect_eq) 
        qed
      qed
    qed
  have all: \<open>\<forall>L \<in> ?J. holds_lit v \<beta> L\<close>
    using holds by fastforce 
  then have H3: \<open>consistent_interp ?J\<close>
    unfolding consistent_interp_def using holds_lit_conflict by blast 
  then have H4: \<open>theory_check_mia ?J P\<close>
    unfolding theory_check_mia_def
    using all integral by blast 
  show \<open>\<exists>J. theory_check_mia J P \<and> I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
    using H2 H3 H4 by blast 
qed

interpretation theory_mia: theory_problem theory_entails_clauses_mia theory_check_mia
  apply (unfold_locales)
  subgoal for I N P using ax1 by auto
  subgoal for I N P using ax2 by blast
  subgoal for I N P using ax3 by auto
  done

thm theory_mia.dpll\<^sub>\<T>_sound

subsection \<open>Soundness\<close>
lemma satisfiable\<^sub>\<T>_iff_sat_mf: \<open>theory_mia.satisfiable\<^sub>\<T> P (set_mset N) 
                              \<longleftrightarrow> (\<exists>v \<beta>. wf_integral v P \<and> (\<forall>C \<in># N. (\<exists>L \<in># C. holds_lit v \<beta> L)))\<close>
proof 
  assume \<open>theory_mia.satisfiable\<^sub>\<T> P (set_mset N)\<close>
  then obtain I where sat: \<open>I \<Turnstile>sm N\<close> 
           and check: \<open>theory_check_mia I P\<close> 
           and cons: \<open>consistent_interp I\<close> 
           and atms: \<open>atm_of ` I = atms_of_mm N\<close>
    by (auto simp: theory_mia.satisfiable\<^sub>\<T>_def)
  then obtain v \<beta> where integral: \<open>(wf_integral v P)\<close> and holds: \<open>(\<forall>L \<in> I. holds_lit v \<beta> L)\<close>
    using check by (auto simp: theory_check_mia_def)
  show \<open>\<exists>v \<beta>. wf_integral v P \<and> (\<forall>C\<in>#N. \<exists>L\<in>#C. holds_lit v \<beta> L)\<close>
  proof (rule exI[where x = v], rule exI[where x = \<beta>], rule conjI)
    show \<open>wf_integral v P\<close> using integral by auto
    show \<open>\<forall>C\<in>#N. \<exists>L\<in>#C. holds_lit v \<beta> L\<close> 
    proof (rule ccontr)
      assume \<open>\<not> (\<forall>C\<in>#N. \<exists>L\<in>#C. holds_lit v \<beta> L)\<close>
      then obtain D where inN: \<open>D \<in># N\<close> and all: \<open>\<forall>L\<in>#D. \<not> holds_lit v \<beta> L\<close>
        by blast 
      then show \<open>False\<close>
        using holds sat by (meson true_cls_def true_clss_def true_lit_def) 
    qed
  qed
next
  assume \<open>\<exists>v \<beta>. wf_integral v P \<and> (\<forall>C\<in>#N. \<exists>L\<in>#C. holds_lit v \<beta> L)\<close>
  then obtain v \<beta> where integral: \<open>wf_integral v P\<close> and holds: \<open>(\<forall>C\<in>#N. \<exists>L\<in>#C. holds_lit v \<beta> L)\<close>
    by auto
  let ?I = \<open>{L | L. (atm_of L \<in> atms_of_mm N) \<and> holds_lit v \<beta> L}\<close>
  have 1: \<open>?I \<Turnstile>sm N\<close>
    by (simp add: in_implies_atm_of_on_atms_of_ms local.holds true_cls_def true_clss_def) 
  have 2: \<open>theory_check_mia ?I P\<close>
    using integral theory_check_mia_def by fastforce
  have 3: \<open>consistent_interp ?I\<close>
    using consistent_interp_def holds_lit_conflict by auto 
  have 4: \<open>atm_of ` ?I = atms_of_mm N\<close>
  proof
    show \<open>atm_of ` {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L} \<subseteq> atms_of_mm N\<close>
    proof
      fix x
      assume \<open>x \<in> atm_of ` {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L}\<close>
      then show \<open>x \<in> atms_of_mm N\<close> by blast
    qed
  next
    show \<open>atms_of_mm N \<subseteq> atm_of ` {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L}\<close>
    proof
      fix x
      assume \<open>x \<in> atms_of_mm N\<close>
      then show \<open>x \<in> atm_of ` {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L}\<close>
      proof (cases \<open>holds_lit v \<beta> (Pos x)\<close>)
        case True
        then have \<open>Pos x \<in> {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L}\<close>
          using \<open>x \<in> atms_of_mm N\<close> by simp
        then show ?thesis
          by (metis (no_types, lifting) literal.sel(1) rev_image_eqI) 
      next
                case False
        then have \<open>holds_lit v \<beta> (Neg x)\<close>
          using holds_lit_neg[of v \<beta> \<open>Pos x\<close>] by simp
        then have \<open>Neg x \<in> {L |L. atm_of L \<in> atms_of_mm N \<and> holds_lit v \<beta> L}\<close>
          using \<open>x \<in> atms_of_mm N\<close> by simp
        then show ?thesis
          by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(2)) 
      qed
    qed
  qed
  show \<open>theory_mia.satisfiable\<^sub>\<T> P (set_mset N)\<close>
    unfolding theory_mia.satisfiable\<^sub>\<T>_def 
    using 1 2 3 4 by auto 
qed

end