theory DPLL_T_Implementation
imports CDCL.DPLL_W_Implementation CDCL.DPLL_CDCL_W_Implementation DPLL_T "HOL-Library.Code_Target_Numeral"
begin

section \<open>Simple Implementation of DPLL_T\<close>
text \<open>I try to closely follow the development in \<^file>\<open>../CDCL/DPLL_W_Implementation.thy\<close> and to re-use
      as much as I can for this part\<close>

subsection \<open>The step function\<close>
text 
\<open>
  The DPLL_T_step function first performs the \<^term>\<open>dpll\<^sub>W\<close> step function \<^term>\<open>DPLL_step\<close>.
  Once normal DPLL can not take a step anymore, we ask the theory. Since this also implies that
  we find ourselves in a \<^term>\<open>conclusive_dpll\<^sub>W_state\<close>, it could be that we are in the UNSAT case
  and the final theory check is wasted effort. This is an optimization for the future, however,
  as I try to keep everything simple for now.
\<close>
definition DPLL_T_step :: "('v literal list \<Rightarrow> bool) \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list
  \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list" where
"DPLL_T_step \<T>_solver = (\<lambda>(Ms, N). (let (Ms', N') = DPLL_step (Ms, N) 
          in if (Ms', N') = (Ms, N) 
              then (if \<T>_solver (map lit_of Ms) then (Ms, N)
                  else (case backtrack_split Ms of
                            (_, L # M) \<Rightarrow> (Propagated (- (lit_of L)) () # M, N)
                          | (_, _) \<Rightarrow> (Ms, N)))
              else (Ms', N')))"

lemma snd_DPLL_T_step[simp]:
  "snd (DPLL_T_step \<T>_solver (Ms, N)) = N"
  by (simp add: DPLL_T_step_def snd_DPLL_step[of Ms N] split_beta case_prod_beta list.case_eq_if) 

subsection \<open>The main loop\<close>
text \<open>Other than \<^term>\<open>DPLL_tot\<close> we use a partial_function instead of a typedef. This means we do
      not directly prove termination but will have to use a well-foundedness argument eventually.
      Moreover, we lose some expressiveness as we always have to start from an initial state for
      which \<^term>\<open>dpll\<^sub>W_all_inv\<close> holds. This is not an issue for DPLL however.\<close>
partial_function (tailrec) DPLL_T_partial ::
\<open>('v literal list \<Rightarrow> bool) \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list
  \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list\<close> where
\<open>DPLL_T_partial \<T>_solver S =
  (let S' = DPLL_T_step \<T>_solver S in if S' = S then S else DPLL_T_partial \<T>_solver S')\<close>

declare DPLL_T_partial.simps[code]

subsection \<open>The main lemmas\<close>
context theory_problem
begin

definition \<T>_solver_correct :: \<open>('v literal list \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'v literal list list \<Rightarrow> bool\<close> where
  \<open>\<T>_solver_correct \<T>_solver P N \<longleftrightarrow>
     (\<forall>Ms. consistent_interp (set Ms) \<longrightarrow> atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<longrightarrow>
           (\<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P))\<close>

lemma \<T>_solver_correctI:
  assumes \<open>\<And>Ms. consistent_interp (set Ms) \<Longrightarrow> atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<Longrightarrow>
             \<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P\<close>
  shows \<open>\<T>_solver_correct \<T>_solver P N\<close>
  using assms by (simp add: \<T>_solver_correct_def)

lemma \<T>_solver_correctD:
  assumes \<open>\<T>_solver_correct \<T>_solver P N\<close>
    and \<open>consistent_interp (set Ms)\<close>
    and \<open>atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N))\<close>
  shows \<open>\<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P\<close>
  using assms by (simp add: \<T>_solver_correct_def)

lemma DPLL_T_step_is_a_dpll\<^sub>\<T>_step:
  assumes inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms N))\<close> 
  and step: \<open>(Ms', N') = DPLL_T_step \<T>_solver (Ms, N)\<close>
  and neq: \<open>(Ms, N) \<noteq> (Ms', N')\<close>
  and solver: \<open>\<T>_solver_correct \<T>_solver P N\<close>
  shows \<open>dpll\<^sub>\<T> P (toS Ms N) (toS Ms' N')\<close>
proof -
  have "(Ms', N') = DPLL_step (Ms, N)" if "(Ms, N) \<noteq> DPLL_step (Ms, N)"
    using step that unfolding DPLL_T_step_def
    by (auto simp: Let_def split: prod.splits)
  moreover have ?thesis
    if I1: \<open>(Ms', N') = DPLL_step (Ms, N)\<close>
  proof -
    have \<open>dpll\<^sub>W (toS Ms N) (toS Ms' N')\<close> using DPLL_step_is_a_dpll\<^sub>W_step[OF I1 neq] by auto 
    then show ?thesis by (rule dpll\<^sub>W_step)
  qed
  moreover have ?thesis
    if I2: \<open>(Ms, N) = DPLL_step (Ms, N)\<close>
  proof (cases \<open>\<T>_solver (map lit_of Ms)\<close>)
    case True
    have \<open>(Ms, N) = DPLL_T_step \<T>_solver (Ms, N)\<close>
      unfolding DPLL_T_step_def using I2 using True by auto 
    then show ?thesis using step neq by auto 
  next
    case False
    obtain m' m where bt: \<open>backtrack_split Ms = (m', m)\<close>
      using surjective_pairing by blast
    then show ?thesis
    proof (cases \<open>m\<close>)
      case Nil
      then have \<open>(Ms, N) = DPLL_T_step \<T>_solver (Ms, N)\<close> unfolding DPLL_T_step_def
        using bt that by auto 
      then show ?thesis using neq step
        by auto 
    next
      case (Cons a list)
      have \<open>trail (toS Ms N) = Ms\<close> by auto
      moreover have \<open>backtrack_split Ms = (m', a # list)\<close>
        by (simp add: bt Cons)
      moreover have \<open>(Propagated (- (lit_of a)) () # list, N) = DPLL_T_step \<T>_solver (Ms, N)\<close>
        unfolding DPLL_T_step_def
        using False calculation(2) that by auto 
      moreover have \<open>is_decided a\<close>
        using bt Cons by (metis backtrack_split_snd_hd_decided list.discI list.sel(1) snd_eqD)
      moreover have \<open>\<not> lits_of_l (trail (toS Ms N)) \<Turnstile>\<^sub>\<T> P\<close>
      proof -
        have cons: \<open>consistent_interp (set (map lit_of Ms))\<close>
          using inv by (auto simp: lits_of_def)
        have atms: \<open>atm_of ` set (map lit_of Ms) \<subseteq> atms_of_mm (mset (map mset N))\<close>
          using inv
          using atms_of_mm_state\<^sub>\<T>_clauses_equals calculation(1) state\<^sub>\<T>_trail_equals_state 
            by (metis dpll\<^sub>W_all_inv_def list.set_map lits_of_def snd_eqD) 
        have \<open>\<T>_solver (map lit_of Ms) \<longleftrightarrow> set (map lit_of Ms) \<Turnstile>\<^sub>\<T> P\<close>
          using solver cons atms by (simp add: \<T>_solver_correct_def)
        then show ?thesis
          using False by (simp add: lits_of_def)
      qed
      ultimately show ?thesis using dpll\<^sub>\<T>.backtrack\<^sub>\<T>
        using step by (metis Pair_inject snd_eqD) 
    qed
  qed
  ultimately show ?thesis
    by auto
qed 

lemma DPLL_T_step_inv:
  assumes \<open>(Ms', N') = DPLL_T_step \<T>_solver (Ms, N)\<close>
    and inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms N))\<close>
    and solver: \<open>\<T>_solver_correct \<T>_solver P N\<close>
  shows \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms' N'))\<close>
proof(cases \<open>(Ms', N') \<noteq> (Ms, N)\<close>)
  case True
  then show ?thesis
    using DPLL_T_step_is_a_dpll\<^sub>\<T>_step assms(1) dpll\<^sub>\<T>_inv inv solver by blast   
next
  case False
  then show ?thesis
    using inv by auto 
qed

thm backtrack_snd_empty_not_decided
term lits_of_l
lemma DPLL_T_step_stuck_conclusive:
  assumes stuck: \<open>(Ms, N) = DPLL_T_step \<T>_solver (Ms, N)\<close>
    and inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms N))\<close>
    and solver: \<open>\<T>_solver_correct \<T>_solver P N\<close>
  shows \<open>conclusive_dpll\<^sub>\<T>_state P (toS Ms N)\<close>
proof-
  have lits: \<open>set (map lit_of Ms) = lits_of_l Ms\<close>
    by (simp add: lits_of_def) 
  have stepW: \<open>DPLL_step (Ms, N) = (Ms, N)\<close>
    using stuck unfolding DPLL_T_step_def apply (auto split: prod.split)
    by (smt (verit, best) DPLL_step_obtains case_prod_conv)
  then have \<open>conclusive_dpll\<^sub>W_state (toS Ms N)\<close>
    using DPLL_step_stuck_final_state by force
  then show \<open>?thesis\<close>
    unfolding conclusive_dpll\<^sub>W_state_def 
  proof(elim disjE)
    have cons: \<open>consistent_interp (set (map lit_of Ms))\<close> 
      using inv unfolding consistent_interp_def
      using lits state\<^sub>\<T>_trail_equals_state by (metis consistent_interp_def dpll\<^sub>W_all_inv_dest(3) fstI) 
    have atms: \<open>atm_of ` (set (map lit_of Ms)) \<subseteq> atms_of_mm (mset (map mset N))\<close> 
      using inv
      using atms_of_mm_state\<^sub>\<T>_clauses_equals lits state\<^sub>\<T>_trail_equals_state by (metis dpll\<^sub>W_all_inv_dest(2) fst_eqD snd_eqD) 
    have solver_iff: \<open>\<T>_solver (map lit_of Ms) = (set (map lit_of Ms) \<Turnstile>\<^sub>\<T> P)\<close>
      using solver cons atms by (simp add: \<T>_solver_correct_def)
    assume A1: \<open>trail (toS Ms N) \<Turnstile>asm clauses (toS Ms N)\<close>
    then show \<open>conclusive_dpll\<^sub>\<T>_state P (toS Ms N)\<close>
    proof (cases \<open>\<T>_solver (map lit_of Ms)\<close>)
      case True
      then show ?thesis
        using A1 conclusive_dpll\<^sub>\<T>_state_def lits solver_iff by fastforce 
    next   
      case False
      have no_dec: \<open>\<forall>L\<in>set (trail (toS Ms N)). \<not> is_decided L\<close>
      proof -
        obtain M M' where bt: \<open>backtrack_split Ms = (M, M')\<close>
          using prod.exhaust_sel by blast
        have \<open>M' = []\<close>
        proof (rule ccontr)
          assume \<open>M' \<noteq> []\<close>
          then obtain L M'' where \<open>M' = (L # M'')\<close> and \<open>is_decided L\<close>
            using bt by (metis backtrack_split_snd_hd_decided list.exhaust list.sel(1) snd_eqD)  
          then have \<open>DPLL_T_step \<T>_solver (Ms, N) \<noteq> (Ms, N)\<close>
            using bt inv stepW False unfolding DPLL_T_step_def apply (auto split: prod.split)
            by (metis append_Cons backtrack_split_list_eq list.distinct(1) self_append_conv2 snd_apfst snd_eqD) 
          then show \<open>False\<close>
            using stuck by auto 
        qed
        then show ?thesis
          using backtrack_snd_empty_not_decided bt by auto  
      qed
      have \<open>\<not> set (map lit_of Ms) \<Turnstile>\<^sub>\<T> P\<close>
        using False solver_iff by auto
      then have \<open>\<not> lits_of_l Ms \<Turnstile>\<^sub>\<T> P\<close>
        using lits by auto
      then obtain C where cnot: \<open>(Ms \<Turnstile>as CNot C)\<close> \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#})\<close> \<open>(C \<in> simple_clss (atm_of ` lits_of_l Ms))\<close>
        using cons lits theory_conflict_trail by metis
      then have \<open>C \<in># simple_clss_theory P (mset `# mset N)\<close>
        using atms lits set_mset_simple_clss_theory simple_clss_mono by fastforce 
      then show ?thesis unfolding conclusive_dpll\<^sub>\<T>_state_def
        using cnot(1) no_dec by auto      
    qed
  next
    show \<open>(\<forall>L\<in>set (trail (toS Ms N)). \<not> is_decided L) \<and> (\<exists>C\<in>#clauses (toS Ms N). trail (toS Ms N) \<Turnstile>as CNot C) \<Longrightarrow> conclusive_dpll\<^sub>\<T>_state P (toS Ms N)\<close>
    proof (elim conjE)
      assume C1: \<open>\<forall>L\<in>set (trail (toS Ms N)). \<not> is_decided L\<close> 
         and C2: \<open>\<exists>C\<in>#clauses (toS Ms N). trail (toS Ms N) \<Turnstile>as CNot C\<close>
      then obtain D where \<open>D \<in># (clauses (toS Ms N))\<close> and D1: \<open>(trail (toS Ms N) \<Turnstile>as CNot D)\<close>
        by auto
      then have \<open>D \<in># clauses (state\<^sub>\<T> P (toS Ms N))\<close> by auto
      then show \<open>conclusive_dpll\<^sub>\<T>_state P (toS Ms N)\<close>
        unfolding conclusive_dpll\<^sub>\<T>_state_def
        using C1 D1 by auto
    qed
  qed
qed

thm wf_induct
thm wf_if_measure_f wf_dpll\<^sub>\<T>
lemma dpll\<^sub>\<T>_is_wf:
  shows \<open>wf {(S', S). (toS' S', toS' S) \<in> {(T', T). dpll\<^sub>W_all_inv (state\<^sub>\<T> P T) \<and> dpll\<^sub>\<T> P T T'}}\<close>
  using wf_if_measure_f[OF wf_dpll\<^sub>\<T>, of \<open>toS'\<close> P] by auto

thm wf_induct wf_induct_rule
lemma DPLL_T_partial_inv_fix:
  assumes inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms N))\<close>
      and run: \<open>(Ms', N') = DPLL_T_partial \<T>_solver (Ms, N)\<close>
      and solver: \<open>\<T>_solver_correct \<T>_solver P N\<close>
    shows \<open>(Ms', N') = DPLL_T_step \<T>_solver (Ms', N')\<close> 
          \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* (toS' (Ms, N)) (toS' (Ms', N'))\<close> 
          \<open>N = N'\<close> sorry (*Idea: wf_induction as DPLL_T_step preserves the relation previously shown to be wf*)


theorem DPLL_T_partial_correct:
  assumes run: \<open>(Ms, N') = DPLL_T_partial \<T>_solver ([], N)\<close>
    and state: \<open>(M, N'') = toS Ms N'\<close>
    and solver: \<open>\<T>_solver_correct \<T>_solver P N\<close>
  shows \<open>(M \<Turnstile>asm N'' \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N'')\<close>
proof -
  have 1: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS [] N))\<close>
    using rtranclp_dpll\<^sub>W_inv_starting_from_0 by fastforce
  have final: \<open>(Ms, N') = DPLL_T_step \<T>_solver (Ms, N') \<close>  
      and abs: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* (toS' ([], N)) (toS' (Ms, N'))\<close> 
      and same_clss: \<open>N = N'\<close>
    using DPLL_T_partial_inv_fix[OF 1 run] solver by blast+
  then have \<open>conclusive_dpll\<^sub>\<T>_state P (toS Ms N')\<close>
    using DPLL_T_step_stuck_conclusive[OF final] solver 1 dpll\<^sub>\<T>_inv_rtranclp by force
  then show ?thesis
    using dpll\<^sub>\<T>_conclusive_state_correct[of P] abs same_clss state
    by fastforce 
qed

end

(*Code gen test for partial function*)
export_code DPLL_T_partial in Haskell

end