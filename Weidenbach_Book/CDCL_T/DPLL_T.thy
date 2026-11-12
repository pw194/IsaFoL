theory DPLL_T
imports CDCL.DPLL_W
begin

section \<open>DPLL(\<T>)\<close>
text 
\<open>
  This file offers a simple formalization of an abstract DPLL(\<T>) calculus. Note that we mean DPLL
  in the sense of naive backtracking and no clause learning. Unlike a lot of papers and SMT
  literature, we distinguish between DPLL as the naive backtracking version and CDCL as the modern
  clause learning procedure.
\<close>

subsection \<open>The theory problem locale\<close>
text 
\<open>
  As a first attempt, I use the theory_problem locale in order to talk about theory entailment and
  satisfiability. This locale is related to the development in \<^file>\<open>CDCL_W_Bound.thy\<close> and very
  abstract. We do not describe a theory with it but the extension of our clause set by additional
  clauses along with an abstract oracle \<^term>\<open>P\<close>:

    \<triangleright> theory_entails_clauses tells us if the orcale entails all clauses of \<^term>\<open>N\<close>
    \<triangleright> theory_check tells us if the oracle accepts an assignment \<^term>\<open>I\<close>

  Further, the three locale assumptions:

    \<triangleright> entail_add: entailed clause sets are closed under adding another entailed clause

    \<triangleright> theory_model_found_or_conflict: tells us that an oracle rejection of a well-formed 
      (potentially partial) assignment \<^term>\<open>I\<close> means, that there exists some simple clause the 
      oracle entails that is false under \<^term>\<open>I\<close> and can be explained only with atoms of \<^term>\<open>I\<close>

    \<triangleright> theory_model_model_sat: if the oracle accepts a consistent assignment \<^term>\<open>I\<close>, then every
      entailed clause set over exactly the atoms of \<^term>\<open>I\<close> is satisfiable. Note that satisfiable
      only state existence of a model here, but we do not give it.

    \<triangleright> theory_extendable: is an experimental addition to the locale as it was needed for a proof.
      
\<close>

locale theory_problem =
  fixes
    theory_entails_clauses :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50) and
    theory_check           :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)

assumes
    entail_add: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close> and
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
begin

subsection \<open>The rules\<close>
text 
\<open> theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
  Instead of directly working in the \<^file>\<open>../CDCL/DPLL_W.thy\<close> file and adjusting the rules,
  I try a simulation. Further, the new backtrack rule does not talk about any clause, but
  simply allows to check the consistency of the current trail if at least one decision is present.
  That is, my interpretation of DPLL(\<T>) is the standard DPLL_W with the addition of passing its
  trail to the oracle.
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
text 
\<open>
  Given an oracle P and clause set N, we define the extension of N with respect to P
  to include all simple clauses that can be build over the atoms in N, and which are entailed by 
  the oracle. I will call these clauses theory lemmas. Note that this set is finite, as the set of 
  simple clauses over N is finite as well. 
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
text 
\<open>
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

text 
\<open>
  This lemma is particularly useful because it allows us to obtain a violated theory lemma
  based on the rejection of the oracle from a consistent trail.
\<close>
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
text \<open>Second version for \<^verbatim>\<open>satisfiable\<^sub>\<T>\<close>\<close>
definition satisfiable\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v clause set \<Rightarrow> bool\<close> where
  \<open>satisfiable\<^sub>\<T> P N \<longleftrightarrow>
     (\<exists>I. I \<Turnstile>s N \<and> I \<Turnstile>\<^sub>\<T> P \<and> consistent_interp I \<and> (atm_of ` I) = (atms_of_ms N))\<close>

(*
    entail_mono: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close> and
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
*)

lemma satisfiable\<^sub>\<T>_is_satisfiable: \<open>satisfiable\<^sub>\<T> P N \<Longrightarrow> satisfiable N\<close>
  using satisfiable\<^sub>\<T>_def by auto

lemma entailment_closure: \<open>finite S \<Longrightarrow> (\<forall>C \<in> S. P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}) \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N + (mset_set S)\<close>
proof (induction rule: finite.induct)
  case emptyI
  then show ?case by auto
next
  case (insertI A a)
  then show ?case using entail_add by (metis insertCI insert_absorb mset_set.insert union_mset_add_mset_right) 
qed

lemma entailment_theory_closure: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N + simple_clss_theory P N\<close>
  using entailment_closure
  using simple_clss_theory_def by (metis (lifting) add_cancel_right_right mem_Collect_eq mset_set_empty_iff) 

lemma unsat_with_lemmas_not_satisfiable\<^sub>\<T>:
  assumes
    A1: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close> and
    A2: \<open>unsatisfiable (set_mset (N + simple_clss_theory P N))\<close>
  shows \<open>\<not> satisfiable\<^sub>\<T> P (set_mset N)\<close>
proof
  let ?N' = \<open>set_mset N\<close>
  assume \<open>satisfiable\<^sub>\<T> P (set_mset N)\<close>
  then obtain I where \<open>I \<Turnstile>s ?N'\<close> 
                and ent: \<open>I \<Turnstile>\<^sub>\<T> P\<close> 
                and con:\<open>consistent_interp I\<close> 
                and \<open>(atm_of ` I) = (atms_of_ms ?N')\<close>
    by (auto simp: satisfiable\<^sub>\<T>_def)
  then have atm: \<open>(atm_of ` I) = atms_of_mm (N + simple_clss_theory P N)\<close>
    using atms_of_mm_simple_clss_theory_subset by force
  have test: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N + simple_clss_theory P N\<close> by (rule entailment_theory_closure[OF A1])
  then show \<open>False\<close>
    using theory_model_model_sat[OF con atm test ent] A2 by auto
qed

text \<open>First idea for conclusive\<close>
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

lemma dpll\<^sub>\<T>_conclusive_state_correct:
  assumes run: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* ([], N) (M, N)\<close> 
          and ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close>
          and concl: \<open>conclusive_dpll\<^sub>\<T>_state P (M, N)\<close>
  shows \<open>(M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>) (*This way of abbreviating was new to me*)
proof -
  have \<open>dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P ([], N)) (state\<^sub>\<T> P (M, N))\<close>
    by (rule dpll\<^sub>\<T>_star_is_dpll\<^sub>W_star[OF run dpll\<^sub>W_all_inv_state\<^sub>\<T>_init])
  then have inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (M, N))\<close>
    using rtranclp_dpll\<^sub>W_inv_starting_from_0 by fastforce
  let ?I = \<open>lits_of_l M\<close>
  show \<open>(M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) = satisfiable\<^sub>\<T> P (set_mset N)\<close>
  proof
  assume A: \<open>?A\<close>
  then have t_ent: \<open>?I \<Turnstile>\<^sub>\<T> P\<close> by auto
  then have cons: \<open>consistent_interp ?I\<close> and atm: \<open>atm_of ` ?I \<subseteq> atms_of_mm N\<close>
    using inv apply fastforce
    using atms_of_mm_state\<^sub>\<T>_clauses_equals inv state\<^sub>\<T>_trail_equals_state by (metis dpll\<^sub>W_all_inv_dest(2) fst_eqD snd_eqD)  
  then show \<open>?B\<close>
    unfolding satisfiable\<^sub>\<T>_def using A theory_extendable[OF cons atm ent t_ent]
    by (metis true_annots_true_cls true_clss_mono_left) 
next
  assume B: \<open>?B\<close>
  show \<open>?A\<close>
  proof (rule ccontr)
    assume n: \<open>\<not> (M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P)\<close>
    then show \<open>False\<close>
    proof -
      have undec: \<open>(\<forall>L \<in> set (trail (M, N)). \<not>is_decided L)\<close> and conf: \<open>(\<exists>C \<in># clauses (state\<^sub>\<T> P (M, N)). trail (M, N) \<Turnstile>as CNot C)\<close>
      using concl n conclusive_dpll\<^sub>\<T>_state_def by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
    then obtain C where
     C_in: \<open>C \<in># N + simple_clss_theory P N\<close> and
     C_confl: \<open>trail (M, N) \<Turnstile>as CNot C\<close>
      by auto
    have \<open>unsatisfiable (set_mset (N + simple_clss_theory P N))\<close>
      using only_propagated_vars_unsat[OF undec C_in C_confl] inv
      using state\<^sub>\<T>_clauses_equals_clauses state\<^sub>\<T>_trail_equals_state by (metis dpll\<^sub>W_all_inv_dest(1,2) split_pairs2) 
    then show \<open>False\<close>
      using unsat_with_lemmas_not_satisfiable\<^sub>\<T>[OF ent] B
      by auto 
      qed
    qed
  qed
qed

subsection \<open>Soundness\<close>
text \<open>First idea\<close>
lemma dpll\<^sub>\<T>_sound:
  assumes run\<^sub>\<T>: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* ([], N) (M, N)\<close>
      and ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close>
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
    by (rule dpll\<^sub>\<T>_conclusive_state_correct[OF run\<^sub>\<T> ent])
qed
    
end

end