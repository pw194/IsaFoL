theory DPLL_T
imports CDCL.DPLL_W
begin

section \<open>DPLL(\<T>)\<close>

text \<open>
  This file... WIP description
\<close>

locale theory_problem =
  fixes
    theory_entails_clauses :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50) and
    theory_check           :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)

assumes
    entail_mono: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close> and
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
begin

subsection \<open>The rules\<close>
text \<open>
  Instead of directly working in the \<^file>\<open>../CDCL/DPLL_W.thy\<close> file and adjusting the rules,
  I try a simulation. Further, the new backtrack rule does not talk about any clause, but
  simply allows to check the consistency of the current trail if at least one decision is present
\<close>
inductive dpll\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> bool\<close> for P where
  dpll\<^sub>W_step: \<open>dpll\<^sub>W S S' \<Longrightarrow>  dpll\<^sub>\<T> P S S'\<close> |
  backtrack\<^sub>\<T>: \<open>backtrack_split (trail S) = (M', L # M) 
                \<Longrightarrow> is_decided L 
                \<Longrightarrow> \<not> lits_of_l (trail S) \<Turnstile>\<^sub>\<T> P
                \<Longrightarrow> dpll\<^sub>\<T> P S (Propagated (- (lit_of L)) () # M, clauses S)\<close>

lemma dpll\<^sub>\<T>_same_clauses: \<open>dpll\<^sub>\<T> P S S' \<Longrightarrow> clauses S = clauses S'\<close>
proof (induction rule: dpll\<^sub>\<T>.induct)
  case (dpll\<^sub>W_step S S')
  then show ?case by (simp add: dpll\<^sub>W_same_clauses) 
next
  case (backtrack\<^sub>\<T> S M' L M)
  then show ?case by auto
qed

subsection \<open>Theory Lemmas\<close>
text \<open>
  Given a theory problem P and clause set N, we define the extension of N with respect to P
  to include all simple clauses that can be build over the atoms in N, and which are theory 
  entailed. Note that this set is finite, as the set of simple clauses over N is finite as well. 
\<close>
definition simple_clss_theory :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>simple_clss_theory P N = mset_set {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}}\<close>

lemma simple_clss_theory_finite: \<open>finite ({C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}})\<close>
  by (simp add: simple_clss_finite)
  
lemma simple_clss_theory_distinct: \<open>distinct_mset (simple_clss_theory P N)\<close>
  by (simp add: simple_clss_theory_def)

lemma set_mset_simple_clss_theory:
  \<open>set_mset (simple_clss_theory P N) = {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}}\<close>
  unfolding simple_clss_theory_def using simple_clss_theory_distinct
  by (auto simp: simple_clss_finite)

text \<open>
  The normal \<^verbatim>\<open>dpll\<^sub>W\<close> state gets extended by adding the theory lemmas to the clauses. I
  call the extension function \<^verbatim>\<open>state\<^sub>\<T>\<close>.
\<close>
definition state\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_state\<close> where
  \<open>state\<^sub>\<T> P S = (trail S, (clauses S) + (simple_clss_theory P (clauses S)))\<close>

lemma state\<^sub>\<T>_trail_equals_state[simp]: \<open>trail (state\<^sub>\<T> P S) = trail S\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma state\<^sub>\<T>_clauses_equals_clauses[simp]: \<open>clauses (state\<^sub>\<T> P S) = (clauses S + (simple_clss_theory P (clauses S)))\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma state\<^sub>\<T>_pair[simp]: \<open>state\<^sub>\<T> P (M, N) = (M, N + simple_clss_theory P N)\<close>
  by (simp add: state\<^sub>\<T>_def)

lemma state_clauses_subset_state\<^sub>\<T>_clauses: \<open>clauses S \<subseteq># clauses (state\<^sub>\<T> P S)\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma atms_of_mm_simple_clss_theory_subset:
  \<open>atms_of_mm (simple_clss_theory P N) \<subseteq> atms_of_mm N\<close>
  by (auto simp: set_mset_simple_clss_theory simple_clss_def atms_of_ms_def)

lemma atms_of_mm_state\<^sub>\<T>_clauses_equals[simp]:
  \<open>atms_of_mm (clauses (state\<^sub>\<T> P S)) = atms_of_mm (clauses S)\<close>
  using atms_of_mm_simple_clss_theory_subset[of P \<open>clauses S\<close>] by (auto simp: state\<^sub>\<T>_def)

lemma simple_clss_trail_in_simple_clss_theory:
  assumes  inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close> 
           and ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#}\<close> 
           and simple: \<open>D \<in> simple_clss (atm_of ` lits_of_l (trail (state\<^sub>\<T> P S)))\<close>
         shows \<open>D \<in># simple_clss_theory P (clauses (state\<^sub>\<T> P S))\<close>
proof -
  have \<open>atms_of D \<subseteq> (atm_of ` lits_of_l (trail (state\<^sub>\<T> P S)))\<close> using simple by (auto simp: simple_clss_def)  
  also have \<open>... \<subseteq> atms_of_mm (clauses (state\<^sub>\<T> P S))\<close> by (rule dpll\<^sub>W_all_inv_dest(2)[OF inv])
  finally have \<open>D \<in> simple_clss (atms_of_mm (clauses (state\<^sub>\<T> P S)))\<close>
    using simple by (auto simp: simple_clss_def)
  then show ?thesis
    using ent by (simp add: set_mset_simple_clss_theory)
qed

subsection \<open>Simulation\<close>
text \<open>
  We now want to show that a step of our \<^verbatim>\<open>dpll\<^sub>\<T>\<close> transition system corresponds to a step in our
  \<^verbatim>\<open>dpll\<^sub>W\<close> transition system, but where we consider the set of theory lemmas to be part of the
  initial clause set, i.e., we consider the state extension via \<^verbatim>\<open>state\<^sub>\<T>\<close>
\<close>

lemma dpll\<^sub>W_step_is_state\<^sub>\<T>_step: \<open>dpll\<^sub>W S S' \<Longrightarrow> dpll\<^sub>W (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: dpll\<^sub>W.induct)
  case (propagate L C S) note[simp] = propagate
  then have \<open>add_mset L C \<in># clauses (state\<^sub>\<T> P S)\<close> 
    using state_clauses_subset_state\<^sub>\<T>_clauses[of S P] by auto
  moreover have conf: \<open>trail (state\<^sub>\<T> P S) \<Turnstile>as CNot C\<close> 
    by auto
  moreover have undef: \<open>undefined_lit (trail (state\<^sub>\<T> P S)) L\<close>
    by auto
  ultimately show ?case
    using dpll\<^sub>W.propagate[of L C \<open>state\<^sub>\<T> P S\<close>] by auto
next
  case (decided S L) note[simp] = decided
  then have \<open>undefined_lit (trail (state\<^sub>\<T> P S)) L\<close> by auto 
  moreover have \<open>atm_of L \<in> atms_of_mm (clauses (state\<^sub>\<T> P S))\<close> by auto
  ultimately show ?case
    using dpll\<^sub>W.decided[of \<open>state\<^sub>\<T> P S\<close> L] by auto
next
  case (backtrack S M' L M D) note[simp] = backtrack
  then have \<open>backtrack_split (trail (state\<^sub>\<T> P S)) = (M', L # M)\<close> by auto
  moreover have \<open>is_decided L\<close> by auto
  moreover have \<open>D \<in># clauses (state\<^sub>\<T> P S)\<close> by auto
  moreover have \<open>trail (state\<^sub>\<T> P S) \<Turnstile>as CNot D\<close> by auto
  ultimately show ?case
    using dpll\<^sub>W.backtrack[of \<open>state\<^sub>\<T> P S\<close> M' L M D] by auto 
qed

lemma dpll\<^sub>W_step_is_state\<^sub>\<T>_step_star: \<open>dpll\<^sub>W\<^sup>*\<^sup>* S S' \<Longrightarrow> dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    using dpll\<^sub>W_step_is_state\<^sub>\<T>_step by (meson rtranclp.simps) 
qed

lemma theory_conflict_trail:
  assumes cons: \<open>consistent_interp (lits_of_l M)\<close> and conf: \<open>\<not> lits_of_l M \<Turnstile>\<^sub>\<T> P\<close>
  obtains C where \<open>(M \<Turnstile>as CNot C)\<close> \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#})\<close> \<open>(C \<in> simple_clss (atm_of ` lits_of_l M))\<close>
  using assms proof -
  let ?N = \<open>mset (map (\<lambda>L. {#lit_of L#}) M)\<close>
  have atms: \<open>(atm_of ` (lits_of_l M)) = (atms_of_mm ?N)\<close> by auto
  have ent: \<open>lits_of_l M \<Turnstile>sm ?N\<close> by (auto simp: true_clss_def lits_of_def)
  obtain D where \<open>(lits_of_l M) \<Turnstile>s CNot D\<close> \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#}\<close> \<open>D \<in> simple_clss (atm_of ` (lits_of_l M))\<close>
    using theory_model_found_or_conflict[OF cons atms ent] conf by blast
  then show ?thesis
    using that unfolding true_annots_true_cls by blast
qed

lemma dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step:
  \<open>dpll\<^sub>\<T> P S S' \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> dpll\<^sub>W (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: dpll\<^sub>\<T>.induct)
  case (dpll\<^sub>W_step S S')
  then show ?case using dpll\<^sub>W_step_is_state\<^sub>\<T>_step by auto
next
  case (backtrack\<^sub>\<T> S M' L M)
  then obtain D where cnot: \<open>((trail (state\<^sub>\<T> P S)) \<Turnstile>as CNot D)\<close> 
    and ent: \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#})\<close> 
    and simple: \<open>(D \<in> simple_clss (atm_of ` (lits_of_l (trail (state\<^sub>\<T> P S)))))\<close>
    using theory_conflict_trail[of \<open>trail (state\<^sub>\<T> P S)\<close> P] state\<^sub>\<T>_trail_equals_state 
    by (auto simp: dpll\<^sub>W_all_inv_def)
  then have D_thm: \<open>D \<in># simple_clss_theory P (clauses (state\<^sub>\<T> P S))\<close>
    using simple_clss_trail_in_simple_clss_theory backtrack\<^sub>\<T>.prems by auto 
  then have cls: \<open>D \<in># clauses (state\<^sub>\<T> P S)\<close>
    using atms_of_mm_state\<^sub>\<T>_clauses_equals set_mset_simple_clss_theory by fastforce
  have trail_decomp: \<open>backtrack_split (trail (state\<^sub>\<T> P S)) = (M', L # M)\<close> using backtrack\<^sub>\<T> by auto
  then show ?case 
    using dpll\<^sub>W.backtrack[OF trail_decomp backtrack\<^sub>\<T>(2) cls cnot] by auto
qed

lemma dpll\<^sub>\<T>_star_is_dpll\<^sub>W_star: 
  \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* S S' \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    using dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step by (metis rtranclp.simps rtranclp_dpll\<^sub>W_all_inv) 
qed

subsection \<open>Invariants\<close>
lemma dpll\<^sub>W_inv_state\<^sub>\<T>_inv: \<open>dpll\<^sub>W_all_inv S \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close>
  unfolding dpll\<^sub>W_all_inv_def
  apply (intro conjI)
  subgoal by (rule all_decomposition_implies_mono[OF set_mset_mono[OF state_clauses_subset_state\<^sub>\<T>_clauses]]) auto
  subgoal by auto 
  subgoal by auto
  subgoal by auto
  done

lemma dpll\<^sub>\<T>_inv: \<open>dpll\<^sub>\<T> P S S' \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S')\<close>
  using dpll\<^sub>W_all_inv dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step by blast

lemma dpll\<^sub>\<T>_inv_rtranclp: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* S S' \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S')\<close>
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using dpll\<^sub>\<T>_inv by auto
qed

subsection \<open>Termination\<close>
lemma wf_dpll\<^sub>\<T>: 
  \<open>wf {(S', S). dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<and> dpll\<^sub>\<T> P S S'}\<close>
  apply (rule wf_subset[OF wf_if_measure_f[OF wf_dpll\<^sub>W, of \<open>state\<^sub>\<T> P\<close>]])
  using dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step by auto

subsection \<open>Satisfiability for \<T>\<close>
text \<open>First version for \<^verbatim>\<open>satisfiable\<^sub>\<T>\<close>\<close>
(*
definition satisfiable :: "'a clause set \<Rightarrow> bool" where
  "satisfiable CC \<longleftrightarrow> (\<exists>I. (I \<Turnstile>s CC \<and> consistent_interp I \<and> total_over_m I CC))"
*)
(*
definition satisfiable\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v clause set \<Rightarrow> bool\<close> where
  \<open>satisfiable\<^sub>\<T> P N \<longleftrightarrow>
     (\<exists>I. I \<Turnstile>s N \<and> I \<Turnstile>\<^sub>\<T> P \<and> consistent_interp I \<and> total_over_m I N )\<close>
*)
text \<open>Second version for \<^verbatim>\<open>satisfiable\<^sub>\<T>\<close>\<close>
definition satisfiable\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v clause set \<Rightarrow> bool\<close> where
  \<open>satisfiable\<^sub>\<T> P N \<longleftrightarrow>
     (\<exists>I. I \<Turnstile>s N \<and> I \<Turnstile>\<^sub>\<T> P \<and> consistent_interp I \<and> (atm_of ` I) = (atms_of_ms N))\<close>

subsection \<open>Final and conclusive states\<close>

lemma final_trail_total:
  assumes
    final: \<open>\<forall>S'. \<not> dpll\<^sub>W (M, N) S'\<close> and
    inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (M, N))\<close>
  shows \<open>atm_of ` lits_of_l M = atms_of_mm N\<close>
  oops

text \<open>First idea for conclusive\<close>
(*
definition "conclusive_dpll\<^sub>W_state (S:: 'v dpll\<^sub>W_state) \<longleftrightarrow>
  (trail S \<Turnstile>asm clauses S \<or> ((\<forall>L \<in> set (trail S). \<not>is_decided L)
  \<and> (\<exists>C \<in># clauses S. trail S \<Turnstile>as CNot C)))"
*)
definition "conclusive_dpll\<^sub>\<T>_state P S \<longleftrightarrow>
  ((trail S \<Turnstile>asm clauses S \<and> lits_of (set (trail S)) \<Turnstile>\<^sub>\<T> P) \<or> ((\<forall>L \<in> set (trail S). \<not>is_decided L)
  \<and> (\<exists>C \<in># clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C)))"

lemma dpll\<^sub>\<T>_final_state_is_dpll\<^sub>W_final_state: \<open>(\<forall>S'. \<not>(dpll\<^sub>\<T> P S S')) \<Longrightarrow> \<forall>S'. \<not>(dpll\<^sub>W S S')\<close>
  using dpll\<^sub>W_step by blast

lemma dpll\<^sub>W_state\<^sub>\<T>_conclusive_is_dpll\<^sub>\<T>_conclusive: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>W_state (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>\<T>_state P S\<close>
  unfolding conclusive_dpll\<^sub>W_state_def
proof (elim disjE)
  assume inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close>
  assume sat: \<open>trail (state\<^sub>\<T> P S) \<Turnstile>asm clauses (state\<^sub>\<T> P S)\<close>
  show \<open>conclusive_dpll\<^sub>\<T>_state P S\<close>
  proof (rule ccontr)
    assume non_conc: \<open>\<not> conclusive_dpll\<^sub>\<T>_state P S\<close>
    then show \<open>False\<close>
      unfolding conclusive_dpll\<^sub>\<T>_state_def
      apply (simp only: de_Morgan_disj de_Morgan_conj)
      apply (elim conjE)
      apply (elim disjE)
      subgoal using sat by force 
      subgoal using sat by auto 
      subgoal using sat inv 
      proof -
        obtain D where cnot: \<open>((trail (state\<^sub>\<T> P S)) \<Turnstile>as CNot D)\<close> 
        and ent: \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#})\<close> 
        and simple: \<open>(D \<in> simple_clss (atm_of ` (lits_of_l (trail (state\<^sub>\<T> P S)))))\<close>
           using theory_conflict_trail inv sat
           using \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C) \<Longrightarrow> False\<close>
             \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<forall>L\<in>set (trail S). \<not> is_decided L) \<Longrightarrow> False\<close> conclusive_dpll\<^sub>\<T>_state_def non_conc state\<^sub>\<T>_trail_equals_state
           by (metis dpll\<^sub>W_all_inv_def) 
        then show \<open>False\<close>
          using sat cnot
          using atms_of_mm_state\<^sub>\<T>_clauses_equals inv set_mset_simple_clss_theory state\<^sub>\<T>_clauses_equals_clauses
          by (smt (cvc5, best) consistent_CNot_not dpll\<^sub>W_all_inv_def mem_Collect_eq simple_clss_mono subsetD true_annots_true_cls true_clss_def union_iff) 
      qed
      subgoal
      proof -
        obtain D where cnot: \<open>((trail (state\<^sub>\<T> P S)) \<Turnstile>as CNot D)\<close> 
        and ent: \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#})\<close> 
        and simple: \<open>(D \<in> simple_clss (atm_of ` (lits_of_l (trail (state\<^sub>\<T> P S)))))\<close>
          using theory_conflict_trail[of \<open>trail (state\<^sub>\<T> P S)\<close> P] state\<^sub>\<T>_trail_equals_state inv
          using \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C) \<Longrightarrow> False\<close>
            \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<forall>L\<in>set (trail S). \<not> is_decided L) \<Longrightarrow> False\<close> conclusive_dpll\<^sub>\<T>_state_def non_conc by (metis dpll\<^sub>W_all_inv_def)
        assume \<open>\<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C)\<close>
        then show \<open>False\<close>
          using cnot atms_of_mm_state\<^sub>\<T>_clauses_equals ent inv set_mset_simple_clss_theory simple simple_clss_trail_in_simple_clss_theory by auto 
      qed
      done
  qed
next
  assume \<open>(\<forall>L\<in>set (trail (state\<^sub>\<T> P S)). \<not> is_decided L) \<and> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail (state\<^sub>\<T> P S) \<Turnstile>as CNot C)\<close>
  then show \<open>conclusive_dpll\<^sub>\<T>_state P S\<close>
    by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
qed

lemma dpll\<^sub>\<T>_no_more_step_is_a_conclusive_state: \<open>(\<forall>S'. \<not>(dpll\<^sub>\<T> P S S')) \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>\<T>_state P S\<close>
proof (rule ccontr)
  assume \<open>\<forall>S'. \<not> dpll\<^sub>\<T> P S S'\<close> and \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close> and \<open>\<not> conclusive_dpll\<^sub>\<T>_state P S\<close>
  then show \<open>False\<close>
    unfolding conclusive_dpll\<^sub>\<T>_state_def
    apply (simp only: de_Morgan_disj de_Morgan_conj)
  proof -
    assume A1: \<open>\<forall>S'. \<not> dpll\<^sub>\<T> P S S'\<close>
    assume A2: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close>
    assume A3: \<open>(\<not> trail S \<Turnstile>asm clauses S \<or> \<not> lits_of_l (trail S) \<Turnstile>\<^sub>\<T> P) 
                \<and> (\<not> (\<forall>L\<in>set (trail S). \<not> is_decided L) \<or> \<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C))\<close>
    then show \<open>False\<close>
      apply (elim conjE)
      apply (elim disjE)
      subgoal
        using A1 conclusive_dpll\<^sub>W_state_def dpll\<^sub>W_no_more_step_is_a_conclusive_state dpll\<^sub>W_step by blast 
      subgoal
        using A1 dpll\<^sub>W_step state_clauses_subset_state\<^sub>\<T>_clauses by (meson conclusive_dpll\<^sub>W_state_def dpll\<^sub>W_no_more_step_is_a_conclusive_state mset_subset_eqD) 
      subgoal
        using A1 backtrack\<^sub>\<T> by (metis backtrack_split_snd_hd_decided backtrack_split_some_is_decided_then_snd_has_hd list.discI list.sel(1) snd_eqD) 
      subgoal
      proof -
        obtain D where cnot: \<open>((trail (state\<^sub>\<T> P S)) \<Turnstile>as CNot D)\<close> 
        and ent: \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#})\<close> 
        and simple: \<open>(D \<in> simple_clss (atm_of ` (lits_of_l (trail (state\<^sub>\<T> P S)))))\<close>
          using theory_conflict_trail[of \<open>trail (state\<^sub>\<T> P S)\<close> P] state\<^sub>\<T>_trail_equals_state A1 A2
          unfolding dpll\<^sub>W_all_inv_def
          using A3 \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C) \<Longrightarrow> False\<close>
            \<open>\<not> trail S \<Turnstile>asm clauses S \<Longrightarrow> \<not> (\<forall>L\<in>set (trail S). \<not> is_decided L) \<Longrightarrow> False\<close> by auto 
        assume \<open>\<not> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C)\<close>
        then show \<open>False\<close> 
          using state\<^sub>\<T>_trail_equals_state cnot A2 atms_of_mm_state\<^sub>\<T>_clauses_equals 
                ent set_mset_simple_clss_theory simple simple_clss_trail_in_simple_clss_theory 
          by auto 
      qed
      done
  qed
qed

lemma dpll\<^sub>W_all_inv_state\<^sub>\<T>_init: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P ([], N))\<close>
  unfolding dpll\<^sub>W_all_inv_def by auto
thm satisfiable_carac

lemma \<open>atms_of_mm (simple_clss_theory P N) \<subseteq> atms_of_mm N\<close>
  sorry
lemma dpll\<^sub>\<T>_conclusive_state_correct:
  assumes run: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* ([], N) (M, N)\<close> and
    ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close>
      and concl: \<open>conclusive_dpll\<^sub>\<T>_state P (M, N)\<close>
  shows \<open>(M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>) (*This way of abbreviating was new to me*)
proof
  let ?I = "lits_of_l M"
  assume \<open>?A\<close>
  then have IN: \<open>?I \<Turnstile>sm N\<close> \<open>lits_of_l M \<Turnstile>\<^sub>\<T> P\<close> by (auto simp: true_annots_true_cls)
  have \<open>consistent_interp ?I\<close> \<open>atm_of ` ?I  \<subseteq> atms_of_mm N\<close>
    using dpll\<^sub>\<T>_inv_rtranclp[OF run dpll\<^sub>W_all_inv_state\<^sub>\<T>_init] atms_of_mm_simple_clss_theory_subset[of P N]
    by (auto simp: dpll\<^sub>W_all_inv_def)
  then show \<open>?B\<close>
    unfolding satisfiable\<^sub>\<T>_def using theory_extendable[of \<open>lits_of_l M\<close> N P] IN ent apply (auto simp: )
    by (meson true_clss_mono_left true_clss_set_mset)
next
  let ?I = "lits_of_l M"
  assume \<open>?B\<close>
  have H: \<open>consistent_interp ?I\<close> \<open>atm_of ` ?I  \<subseteq> atms_of_mm N\<close> and
    decomp: \<open>all_decomposition_implies  (set_mset N \<union> set_mset (simple_clss_theory P N)) (get_all_ann_decomposition M)\<close>
    using dpll\<^sub>\<T>_inv_rtranclp[OF run dpll\<^sub>W_all_inv_state\<^sub>\<T>_init] atms_of_mm_simple_clss_theory_subset[of P N]
    by (auto simp: dpll\<^sub>W_all_inv_def)
  moreover then have False if H: \<open>(\<exists>C\<in>#clauses (state\<^sub>\<T> P (M, N)). trail (M, N) \<Turnstile>as CNot C)\<close> \<open>(\<forall>L \<in> set M. \<not>is_decided L)\<close>
  proof -
    obtain C where \<open>C\<in>#clauses (state\<^sub>\<T> P (M, N))\<close> \<open>trail (M, N) \<Turnstile>as CNot C\<close>
      using H by auto
    then have \<open>unsatisfiable (set_mset N \<union> set_mset (simple_clss_theory P N))\<close>
      using decomp only_propagated_vars_unsat[of M C \<open>set_mset (clauses (state\<^sub>\<T> P (M, N)))\<close>] 
       atms_of_mm_simple_clss_theory_subset[of P N] H(2) \<open>atm_of ` ?I  \<subseteq> atms_of_mm N\<close> 
      by (auto simp del: )
    then show False
      using \<open>?B\<close> apply (auto simp: satisfiable\<^sub>\<T>_def)
    
      sorry
  qed
    then have \<open> trail (M, N) \<Turnstile>asm clauses (M, N) \<and> lits_of_l (trail (M, N)) \<Turnstile>\<^sub>\<T> P\<close>
      using concl unfolding conclusive_dpll\<^sub>\<T>_state_def conclusive_dpll\<^sub>W_state_def
      by (auto simp: )
  then have \<open>lits_of_l M \<Turnstile>m N + simple_clss_theory P N\<close> 
    sorry
  ultimately have IN: \<open>?I \<Turnstile>sm N\<close> \<open>lits_of_l M \<Turnstile>\<^sub>\<T> P\<close> using concl apply (auto simp: conclusive_dpll\<^sub>\<T>_state_def satisfiable\<^sub>\<T>_def)
    apply (meson consistent_CNot_not true_annots_true_cls true_cls_mset_def)
    by (meson consistent_CNot_not true_annots_true_cls true_cls_mset_def)
    
  then show \<open>?A\<close>
    sorry
qed

subsection \<open>Soundness\<close>

text \<open>First idea\<close>
lemma dpll\<^sub>\<T>_sound:
  assumes run\<^sub>\<T>: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* ([], N) (M, N)\<close>
      and final: \<open>\<forall>S. \<not> dpll\<^sub>\<T> P (M, N) S\<close>
  shows \<open>(M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N)\<close>
proof -
  have run\<^sub>W: \<open>dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P ([], N)) (state\<^sub>\<T> P (M, N))\<close>
    using dpll\<^sub>W_all_inv_state\<^sub>\<T>_init dpll\<^sub>\<T>_star_is_dpll\<^sub>W_star run\<^sub>\<T> by blast
  then have inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (M, N))\<close>
    using dpll\<^sub>W_all_inv_state\<^sub>\<T>_init rtranclp_dpll\<^sub>W_all_inv by blast
  then have \<open>conclusive_dpll\<^sub>\<T>_state P (M, N)\<close>
    by (rule dpll\<^sub>\<T>_no_more_step_is_a_conclusive_state[OF final])
  then show ?thesis
    by (rule dpll\<^sub>\<T>_conclusive_state_correct[OF run\<^sub>\<T>])
qed
    
  
end

end