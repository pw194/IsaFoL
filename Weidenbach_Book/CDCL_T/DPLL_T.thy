theory DPLL_T
imports CDCL.DPLL_W
begin

section \<open>DPLL(\<T>)\<close>
text 
\<open>
  This file offers a simple formalization of an abstract DPLL(\<T>) calculus. Note that we mean DPLL
  in the sense of naive backtracking and no clause learning. Unlike a lot of papers and SMT
  literature, we distinguish between DPLL as the naive backtracking version and CDCL as the modern
  clause learning procedure. Moreover we always consider a given, fixed clause set. Thus our atoms 
  we talk about are finite in nature and we do not currently support adding new atoms.
\<close>

subsection \<open>The theory problem locale\<close>
text 
\<open>
  As a first attempt, I use a theory_problem locale in order to talk about theory entailment and
  consistency. This locale is very abstract. We use it to describe the extension of our clause set 
  by additional clauses that are entailed by the theory problem \<open>P\<close>. Our \<open>P\<close> contains all the
  necessary information of our theory to define the notion of consistency and entailment.

    \<triangleright> theory_entails_clauses tells us if the theory entails all clauses of \<open>N\<close>
    \<triangleright> theory_check tells us if an assignment \<open>I\<close> is consistent in the theory

  Further, the current three locale assumptions:

    \<triangleright> theory_check_sound: says that an assignment \<open>I\<close> that is \<T>-consistent must propositionally
                          satisfy a theory entailed clause that is fully defined in \<open>I\<close>.

    \<triangleright> theory_model_found_or_conflict: tells us that an inconsistency of a well-formed 
      (potentially partial) assignment \<open>I\<close> means, that there exists some simple clause the 
      theory entails, and which is false under \<open>I\<close>. Further, it and can be explained only 
      with atoms of \<open>I\<close> The atoms of \<open>I\<close> must be the same as the atoms of some clause set \<open>N\<close>

    \<triangleright> theory_extendable: is an experimental addition to the locale as it was needed for a proof.
                         It allows us to extend a consistent, partial model of the theory, to a 
                         total one that covers exactly the finitely many atoms of N.
\<close>

locale theory_problem =
  fixes
    theory_entails_clauses :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50) and
    theory_check           :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)

assumes
    theory_model_sound: \<open>I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> atms_of C \<subseteq> atm_of ` I \<Longrightarrow> I \<Turnstile> C\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N 
      \<Longrightarrow> I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
begin

subsection \<open>The rules\<close>
text 
\<open>
  Instead of directly working in the \<^file>\<open>../CDCL/DPLL_W.thy\<close> file and adjusting the rules,
  I try a simulation. Further, the new backtrack rule does not talk about any clause, but
  simply allows to check the consistency of the current trail if at least one decision is present,
  and then backtracks in the case of an inconsistency. That is, my interpretation of DPLL(\<T>) is the 
  standard DPLL_W with the addition of passing its (partial) trail to the \<T>_solver.
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
  Given a theory problem \<open>P\<close> and clause set \<open>N\<close>, we define the extension of \<open>N\<close> with respect to \<open>P\<close>
  to include all simple clauses that can be build over the atoms in \<open>N\<close>, and which are entailed by 
  the theory. We call these clauses theory lemmas. Note that this set is finite, as the set of 
  simple clauses over \<open>N\<close> is finite as well. 
\<close>
definition simple_clss_theory :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>simple_clss_theory P N = mset_set {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}}\<close>

lemma simple_clss_theory_finite: \<open>finite ({C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}})\<close>
  by (simp add: simple_clss_finite)
  
lemma simple_clss_theory_distinct: \<open>distinct_mset (simple_clss_theory P N)\<close>
  by (simp add: simple_clss_theory_def)

lemma set_mset_simple_clss_theory:
  \<open>set_mset (simple_clss_theory P N) = {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}}\<close>
  by (auto simp: simple_clss_finite simple_clss_theory_def simple_clss_theory_distinct)

text 
\<open>
  The normal \<^term>\<open>dpll\<^sub>W\<close> state gets extended by adding the theory lemmas to the clauses. I
  call the extension function \<open>state\<^sub>\<T>\<close>. The trail remains the same.
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
  using atms_of_mm_simple_clss_theory_subset[of P \<open>clauses S\<close>] by auto

lemma simple_clss_trail_in_simple_clss_theory:
  assumes inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close> 
          and tent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {#D#}\<close> 
          and simple: \<open>D \<in> simple_clss (atm_of ` lits_of_l (trail (state\<^sub>\<T> P S)))\<close>
  shows \<open>D \<in># simple_clss_theory P (clauses (state\<^sub>\<T> P S))\<close>
proof -
  have \<open>atms_of D \<subseteq> (atm_of ` lits_of_l (trail (state\<^sub>\<T> P S)))\<close> using simple by (auto simp: simple_clss_def)  
  also have \<open>... \<subseteq> atms_of_mm (clauses (state\<^sub>\<T> P S))\<close> by (rule dpll\<^sub>W_all_inv_dest(2)[OF inv])
  finally have \<open>D \<in> simple_clss (atms_of_mm (clauses (state\<^sub>\<T> P S)))\<close>
    using simple by (auto simp: simple_clss_def)
  then show ?thesis
    by (simp add: tent set_mset_simple_clss_theory)
qed

subsection \<open>Simulation\<close>
text 
\<open>
  We now want to show that a step of our \<^term>\<open>dpll\<^sub>\<T>\<close> transition system corresponds to a step in our
  \<^term>\<open>dpll\<^sub>W\<close> transition system, but where we consider the set of theory lemmas to be part of the
  initial clause set, i.e., we consider the state extension via \<^term>\<open>state\<^sub>\<T>\<close>
\<close>

lemma dpll\<^sub>W_step_is_state\<^sub>\<T>_step: \<open>dpll\<^sub>W S S' \<Longrightarrow> dpll\<^sub>W (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: dpll\<^sub>W.induct) \<comment> \<open>Every rule application is still applicable in the extension\<close>
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

lemma dpll\<^sub>W_step_is_state\<^sub>\<T>_step_star: \<open>dpll\<^sub>W\<^sup>*\<^sup>* S S'' \<Longrightarrow> dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P S) (state\<^sub>\<T> P S'')\<close>
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step S' S'')
  then show ?case using dpll\<^sub>W_step_is_state\<^sub>\<T>_step[OF step(2), of P]
    rtranclp.rtrancl_into_rtrancl[of \<open>dpll\<^sub>W\<close>, OF step(3), of \<open>(state\<^sub>\<T> P S')\<close>] by auto
qed

text 
\<open>
  This lemma is particularly useful because it allows us to obtain a violated theory lemma
  based on the \<T>-inconsistency of the trail, as later determined by the \<T>-solver.
\<close>
lemma theory_conflict_trail:
  assumes cons: \<open>consistent_interp (lits_of_l M)\<close> and conf: \<open>\<not> lits_of_l M \<Turnstile>\<^sub>\<T> P\<close>
  obtains C where \<open>(M \<Turnstile>as CNot C)\<close> \<open>(P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#})\<close> \<open>(C \<in> simple_clss (atm_of ` lits_of_l M))\<close>
  using assms proof - \<comment> \<open>We can use the locale assumption to obtain the conflict for a suitable N\<close>
  let ?N = \<open>mset (map (\<lambda>L. {#lit_of L#}) M)\<close> \<comment> \<open>Our N are the units on the trail\<close>
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
  case (dpll\<^sub>W_step S S') \<comment> \<open>A W step is trivially a step wrt. \<open>state\<^sub>\<T>\<close>\<close>
  then show ?case using dpll\<^sub>W_step_is_state\<^sub>\<T>_step by auto
next
  case (backtrack\<^sub>\<T> S M' L M) \<comment> \<open>A \<T> backtrack can be shown to be a W backtrack wrt. \<open>state\<^sub>\<T>\<close>\<close>
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
  \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* S S'' \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P S) (state\<^sub>\<T> P S'')\<close>
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step S' S'')
  then have run: \<open>dpll\<^sub>W\<^sup>*\<^sup>* (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close> by auto
  have \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S')\<close>
    by (rule rtranclp_dpll\<^sub>W_all_inv[OF run step(4)])
  then have \<open>dpll\<^sub>W (state\<^sub>\<T> P S') (state\<^sub>\<T> P S'')\<close>
    by (rule dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step[OF step(2)])
  then show ?case using rtranclp.rtrancl_into_rtrancl[of \<open>dpll\<^sub>W\<close>, OF run] by auto
qed


subsection \<open>Invariants\<close>
text 
\<open>
  Here are some small facts about \<^term>\<open>dpll\<^sub>W_all_inv\<close> and how \<^term>\<open>dpll\<^sub>\<T>\<close> 
  preserves it on the extended state. Note that some comments in this file implicitly assume
  to talk about states that satisfy the extended-state invariant (via \<open>state\<^sub>\<T>\<close>), for brevity.
  The necessity of the (extended) invariant should always be clear from the proofs.
\<close>

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
text 
\<open>
  Termination can reuse the existing measure from \<^term>\<open>dpll\<^sub>W\<close>. We show termination by proving 
  the set \<^term>\<open>{(S', S). dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<and> dpll\<^sub>\<T> P S S'}\<close> to be a subset of the 
  well-founded set \<^term>\<open>{(b, a). (state\<^sub>\<T> P b, state\<^sub>\<T> P a) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}\<close>
\<close>

lemma wf_dpll\<^sub>\<T>:
  \<open>wf {(S', S). dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<and> dpll\<^sub>\<T> P S S'}\<close>
  apply (rule wf_subset[OF wf_if_measure_f[OF wf_dpll\<^sub>W, of \<open>state\<^sub>\<T> P\<close>]])
  using dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step by auto

subsection \<open>Satisfiability for \<T>\<close>
text 
\<open>
  The definition \<open>satisfiable\<^sub>\<T>\<close> tells us that there exists an assignment \<open>I\<close> such that
    \<triangleright> We can propositionally satisfy the clauses
    \<triangleright> Our \<T>-solver accepts the assignment (in other words, it is consistent)
    \<triangleright> The assignment is propositionally consistent (in the sense of being well-formed)
    \<triangleright> The assignment talks about the same atoms as \<open>N\<close>
\<close>

definition satisfiable\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v clause set \<Rightarrow> bool\<close> where
  \<open>satisfiable\<^sub>\<T> P N \<longleftrightarrow>
     (\<exists>I. I \<Turnstile>s N \<and> I \<Turnstile>\<^sub>\<T> P \<and> consistent_interp I \<and> (atm_of ` I) = (atms_of_ms N))\<close>

text 
\<open>
  This lemma is a sanity check in case I adjust the definition of theory satisfiability.
  Theory satisfiability should imply propositional satisfiability (but in general not vice versa)
\<close>
lemma satisfiable\<^sub>\<T>_is_satisfiable: \<open>satisfiable\<^sub>\<T> P N \<Longrightarrow> satisfiable N\<close>
  using satisfiable\<^sub>\<T>_def by auto

lemma unsat_with_lemmas_not_satisfiable\<^sub>\<T>:
  assumes
    A1: \<open>unsatisfiable (set_mset (N + simple_clss_theory P N))\<close>
  shows \<open>\<not> satisfiable\<^sub>\<T> P (set_mset N)\<close>
proof
  let ?N' = \<open>set_mset N\<close>
  assume sat: \<open>satisfiable\<^sub>\<T> P (set_mset N)\<close>
  then obtain I where sat: \<open>I \<Turnstile>s ?N'\<close> 
                and check: \<open>I \<Turnstile>\<^sub>\<T> P\<close> 
                 and cons: \<open>consistent_interp I\<close> 
                 and atms: \<open>(atm_of ` I) = (atms_of_ms ?N')\<close>
    by (auto simp: satisfiable\<^sub>\<T>_def)
  then obtain C where C: \<open>C \<in> (set_mset (N + simple_clss_theory P N))\<close> 
                  and conf: \<open>\<not> (I \<Turnstile> C)\<close>
                  and mutual: \<open>C \<in># N \<or> C \<in># simple_clss_theory P N\<close>
    using assms by (meson satisfiable_carac true_clss_def union_iff) 
  then show \<open>False\<close>
  proof (elim disjE) \<comment> \<open>Our conflict is either in N or a theory lemma\<close>
    assume \<open>\<not> I \<Turnstile> C\<close> and \<open>C \<in># N\<close>
    then show \<open>False\<close> \<comment> \<open>A propositional conflict in N closes immediately\<close>
      using sat true_clss_def by blast 
  next
    assume cnot: \<open>\<not> I \<Turnstile> C\<close> and simple: \<open>C \<in># simple_clss_theory P N\<close>
    then have tent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {# C #}\<close>
      using set_mset_simple_clss_theory by auto
    then show \<open>False\<close> \<comment> \<open>A theory lemma conflict closes by new locale assumption\<close>
      using cnot theory_model_sound[OF check tent] atms (*New axiom instead of the old models_sat*)
          set_mset_simple_clss_theory simple simple_clssE by fastforce 
  qed
qed

lemma satisfiable\<^sub>\<T>_is_satisfiable_with_lemmas: \<open>satisfiable\<^sub>\<T> P (set_mset N) 
          \<Longrightarrow> satisfiable (set_mset (N + simple_clss_theory P N))\<close>
  using unsat_with_lemmas_not_satisfiable\<^sub>\<T> by auto

subsection \<open>Conclusive states\<close>
text 
\<open>
  A conclusive state is not necessarily final. It tells us that we can already conclude the
  desired property. In our case, for a reachable state that satisfies the extended state invariant,
  if the trail satisfies the clauses and is \<T>-consistent, then we have theory satisfiability. 
  Secondly, if we have only propagations and a conflict, then we can conclude UNSAT from this state 
  as shown later. Alternatively to a total model, this enables the idea to implement early stopping, 
  before all clause atoms are assigned.
\<close>
definition "conclusive_dpll\<^sub>\<T>_state P S \<longleftrightarrow>
  ((trail S \<Turnstile>asm clauses S \<and> lits_of (set (trail S)) \<Turnstile>\<^sub>\<T> P) \<or> ((\<forall>L \<in> set (trail S). \<not>is_decided L)
  \<and> (\<exists>C \<in># clauses (state\<^sub>\<T> P S). trail S \<Turnstile>as CNot C)))"

text \<open>Note, the converse of this obviously doesn't hold\<close>
lemma dpll\<^sub>\<T>_final_state_is_dpll\<^sub>W_final_state: \<open>(\<forall>S'. \<not>(dpll\<^sub>\<T> P S S')) \<Longrightarrow> \<forall>S'. \<not>(dpll\<^sub>W S S')\<close>
  using dpll\<^sub>W_step by blast

lemma dpll\<^sub>W_state\<^sub>\<T>_conclusive_is_dpll\<^sub>\<T>_conclusive:
  \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>W_state (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>\<T>_state P S\<close>
  unfolding conclusive_dpll\<^sub>W_state_def
proof (elim disjE)
  assume inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close>
    and sat: \<open>trail (state\<^sub>\<T> P S) \<Turnstile>asm clauses (state\<^sub>\<T> P S)\<close>
  have cons: \<open>consistent_interp (lits_of_l (trail S))\<close>
    using inv by auto
  have \<open>lits_of_l (trail S) \<Turnstile>\<^sub>\<T> P\<close>
  proof (rule ccontr) \<comment> \<open>Trail needs to be \<T> consistent otherwise some theory lemma is falsified\<close>
    assume \<open>\<not> lits_of_l (trail S) \<Turnstile>\<^sub>\<T> P\<close>
    then obtain C where conflict: \<open>trail S \<Turnstile>as CNot C\<close>
      and ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}\<close>
      and simple: \<open>C \<in> simple_clss (atm_of ` lits_of_l (trail S))\<close>
      using theory_conflict_trail[OF cons] by blast
    have \<open>C \<in># simple_clss_theory P (clauses S)\<close>
      using simple_clss_trail_in_simple_clss_theory[OF inv ent] simple
      by (simp only: state\<^sub>\<T>_trail_equals_state simple_clss_theory_def
          atms_of_mm_state\<^sub>\<T>_clauses_equals)
    then have \<open>C \<in># clauses (state\<^sub>\<T> P S)\<close> by simp
    then have \<open>lits_of_l (trail S) \<Turnstile> C\<close>
      using sat by (auto simp: true_annots_true_cls true_clss_def)
    then show False
      using conflict consistent_CNot_not[OF cons]
      by (auto simp: true_annots_true_cls)
  qed
  then show \<open>conclusive_dpll\<^sub>\<T>_state P S\<close>
    using sat by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
next \<comment> \<open>Follows immediately by definition\<close>
  assume \<open>(\<forall>L\<in>set (trail (state\<^sub>\<T> P S)). \<not> is_decided L) \<and> (\<exists>C\<in>#clauses (state\<^sub>\<T> P S). trail (state\<^sub>\<T> P S) \<Turnstile>as CNot C)\<close>
  then show \<open>conclusive_dpll\<^sub>\<T>_state P S\<close>
    by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
qed

lemma dpll\<^sub>\<T>_no_more_step_is_a_conclusive_state:
  \<open>(\<forall>S'. \<not>(dpll\<^sub>\<T> P S S')) \<Longrightarrow> dpll\<^sub>W_all_inv (state\<^sub>\<T> P S) \<Longrightarrow> conclusive_dpll\<^sub>\<T>_state P S\<close>
proof -
  assume final: \<open>\<forall>S'. \<not> dpll\<^sub>\<T> P S S'\<close>
    and inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P S)\<close>
  have concl: \<open>conclusive_dpll\<^sub>W_state S\<close>
    using dpll\<^sub>\<T>_final_state_is_dpll\<^sub>W_final_state[OF final]
    by (rule dpll\<^sub>W_no_more_step_is_a_conclusive_state)
  show ?thesis
  proof (cases \<open>lits_of_l (trail S) \<Turnstile>\<^sub>\<T> P\<close>)
    case True \<comment> \<open>Follows immediately by definition\<close>
    then show ?thesis
      using concl by (auto simp: conclusive_dpll\<^sub>W_state_def conclusive_dpll\<^sub>\<T>_state_def)
  next
    case False
    have no_decisions: \<open>\<forall>L\<in>set (trail S). \<not> is_decided L\<close>
    proof (rule ccontr)
      assume \<open>\<not> (\<forall>L\<in>set (trail S). \<not> is_decided L)\<close>
      then obtain M' L M where split: \<open>backtrack_split (trail S) = (M', L # M)\<close>
        using backtrack_split_some_is_decided_then_snd_has_hd by blast
      have \<open>is_decided L\<close>
        using backtrack_split_snd_hd_decided[of \<open>trail S\<close>] split by simp
      then have \<open>dpll\<^sub>\<T> P S (Propagated (- (lit_of L)) () # M, clauses S)\<close>
        by (rule backtrack\<^sub>\<T>[OF split _ False])
      then show False using final by auto \<comment> \<open>Having a decision contradicts finality of the state\<close>
    qed
    have cons: \<open>consistent_interp (lits_of_l (trail S))\<close>
      using inv by auto
    obtain C where conflict: \<open>trail S \<Turnstile>as CNot C\<close>
      and ent: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#}\<close>
      and simple: \<open>C \<in> simple_clss (atm_of ` lits_of_l (trail S))\<close>
      using theory_conflict_trail[OF cons False] by blast
    have \<open>C \<in># simple_clss_theory P (clauses S)\<close>
      using simple_clss_trail_in_simple_clss_theory[OF inv ent] simple
      by (simp only: state\<^sub>\<T>_trail_equals_state simple_clss_theory_def
          atms_of_mm_state\<^sub>\<T>_clauses_equals)
    then have \<open>C \<in># clauses (state\<^sub>\<T> P S)\<close> by simp
    then show ?thesis
      using no_decisions conflict by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
  qed
qed

lemma dpll\<^sub>W_all_inv_state\<^sub>\<T>_init: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P ([], N))\<close>
  unfolding dpll\<^sub>W_all_inv_def by auto

lemma dpll\<^sub>\<T>_conclusive_state_correct:
  assumes run: \<open>(dpll\<^sub>\<T> P)\<^sup>*\<^sup>* ([], N) (M, N)\<close>
      and concl: \<open>conclusive_dpll\<^sub>\<T>_state P (M, N)\<close>
  shows \<open>(M \<Turnstile>asm N \<and> lits_of_l M \<Turnstile>\<^sub>\<T> P) \<longleftrightarrow> satisfiable\<^sub>\<T> P (set_mset N)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have inv: \<open>dpll\<^sub>W_all_inv (state\<^sub>\<T> P (M, N))\<close>
    by (rule dpll\<^sub>\<T>_inv_rtranclp[OF run dpll\<^sub>W_all_inv_state\<^sub>\<T>_init])
  have cons: \<open>consistent_interp (lits_of_l M)\<close>
    using inv by auto
  have atms: \<open>atm_of ` lits_of_l M \<subseteq> atms_of_mm N\<close>
    using dpll\<^sub>W_all_inv_dest(2)[OF inv]
    by (simp only: state\<^sub>\<T>_trail_equals_state atms_of_mm_state\<^sub>\<T>_clauses_equals
        fst_conv snd_conv)
  show ?thesis
  proof
    assume sat: \<open>?A\<close>
    then obtain J where check: \<open>J \<Turnstile>\<^sub>\<T> P\<close>
      and extends: \<open>lits_of_l M \<subseteq> J\<close>
      and total: \<open>atm_of ` J = atms_of_mm N\<close>
      and consistent: \<open>consistent_interp J\<close>
      using theory_extendable[OF cons atms sat[THEN conjunct2]] by auto
    have \<open>J \<Turnstile>s set_mset N\<close>
      by (rule true_clss_mono_left[OF _ extends])
        (use sat in \<open>auto simp: true_annots_true_cls\<close>)
    then show \<open>?B\<close>
      using check total consistent by (auto simp: satisfiable\<^sub>\<T>_def)
  next
    assume sat: \<open>?B\<close>
    show \<open>?A\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?A\<close>
      then obtain C where no_decisions: \<open>\<forall>L\<in>set M. \<not> is_decided L\<close>
        and member: \<open>C \<in># N + simple_clss_theory P N\<close>
        and conflict: \<open>M \<Turnstile>as CNot C\<close>
        using concl by (auto simp: conclusive_dpll\<^sub>\<T>_state_def)
      have \<open>unsatisfiable (set_mset (N + simple_clss_theory P N))\<close>
        using only_propagated_vars_unsat[OF no_decisions member conflict]
          dpll\<^sub>W_all_inv_dest(1,2)[OF inv] by simp
      then show False
        using unsat_with_lemmas_not_satisfiable\<^sub>\<T> sat by auto
    qed
  qed
qed

subsection \<open>Soundness\<close>
text 
\<open>
  The proof reuses the propositional development. Every \<^term>\<open>dpll\<^sub>\<T>\<close> step under the invariant
  corresponds to a \<^term>\<open>dpll\<^sub>W\<close> step inside the extended state, so the invariants of \<^term>\<open>dpll\<^sub>W\<close> 
  carry over, and the theory comes into play in most simulation lemmas and when we show that a final 
  state is conclusive. The conclusive state then (by the correctness lemma) allows us to conclude 
  soundness immediately.
\<close>
theorem dpll\<^sub>\<T>_sound:
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