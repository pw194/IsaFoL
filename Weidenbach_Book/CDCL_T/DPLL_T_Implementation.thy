theory DPLL_T_Implementation
imports CDCL.DPLL_W_Implementation CDCL.DPLL_CDCL_W_Implementation DPLL_T "HOL-Library.Code_Target_Numeral"
begin

section \<open>Simple Implementation of DPLL_T\<close>

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
  
partial_function (tailrec) DPLL_T_partial ::
\<open>('v literal list \<Rightarrow> bool) \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list
  \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list\<close> where
\<open>DPLL_T_partial \<T>_solver S =
  (let S' = DPLL_T_step \<T>_solver S in if S' = S then S else DPLL_T_partial \<T>_solver S')\<close>

declare DPLL_T_partial.simps[code]

context theory_problem
begin

lemma DPLL_T_step_is_a_dpll\<^sub>\<T>_step:
  assumes step: \<open>(Ms', N') = DPLL_T_step \<T>_solver (Ms, N)\<close>
  and neq: \<open>(Ms, N) \<noteq> (Ms', N')\<close>
  and rej: \<open>\<And>I. \<not> \<T>_solver I \<Longrightarrow> \<not> (set I) \<Turnstile>\<^sub>\<T> P\<close>
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
         using rej[OF False] by (simp add: lits_of_def)
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
    and rej: \<open>\<And>I. \<not> \<T>_solver I \<Longrightarrow> \<not> (set I) \<Turnstile>\<^sub>\<T> P\<close>
  shows \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS Ms' N'))\<close>
proof(cases \<open>(Ms', N') \<noteq> (Ms, N)\<close>)
  case True
  then show ?thesis
    using DPLL_T_step_is_a_dpll\<^sub>\<T>_step assms(1) dpll\<^sub>\<T>_inv inv rej by blast 
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
    and solver: \<open>\<And>Ms. consistent_interp (set Ms) \<Longrightarrow>
                   atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<Longrightarrow>
                   \<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P\<close>
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
      by (rule solver[of \<open>map lit_of Ms\<close>, OF cons atms])
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


lemma DPLL_T_partial_inv_fix:
  assumes inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (toS M N))\<close>
      and run: \<open>(M', N') = DPLL_T_partial \<T>_solver (M, N)\<close>
      and solver: \<open>\<And>Ms. consistent_interp (set Ms) \<Longrightarrow>
              atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<Longrightarrow>
              \<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P\<close>
  shows \<open>DPLL_T_step \<T>_solver (M', N') = (M', N')\<close> \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* (toS' (M, N)) (toS' (M', N'))\<close> \<open>N = N'\<close>
  sorry
    
theorem DPLL_T_partial_correct:
  assumes run: \<open>(Ms, N') = DPLL_T_partial \<T>_solver ([], N)\<close>
    and state: \<open>(M, N'') = toS Ms N'\<close>
   and solver: \<open>\<And>Ms. consistent_interp (set Ms) \<Longrightarrow>
                atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<Longrightarrow>
                \<T>_solver Ms \<longleftrightarrow> set Ms \<Turnstile>\<^sub>\<T> P\<close>
  shows \<open>(M \<Turnstile>asm N'' \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N'')\<close>
  sorry

end

(*Code gen test for partial function*)
export_code DPLL_T_partial in Haskell

end