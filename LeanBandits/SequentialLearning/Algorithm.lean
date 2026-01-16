/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Architect
import LeanBandits.ForMathlib.Measurable
import LeanBandits.ForMathlib.Traj

/-!
# Algorithms
-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R Ω : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R} {mΩ : MeasurableSpace Ω}

/-- A stochastic, sequential algorithm. -/
@[blueprint
  "def:algorithm"
  (title := "Algorithm")
  (statement := /-- A sequential, stochastic algorithm with actions in a measurable space
    $\mathcal{A}$ and observations in a measurable space $\mathcal{R}$ is described by the following
    data:
    \begin{itemize}
      \item for all $t \in \mathbb{N}$, a policy $\pi_t : (\mathcal{A} \times \mathcal{R})^{t+1}
      \rightsquigarrow \mathcal{A}$, a Markov kernel which gives the distribution of the action of
      the algorithm at time $t+1$ given the history of previous actions and observations,
      \item $P_0 \in \mathcal{P}(\mathcal{A})$, a probability measure that gives the distribution of
      the first action.
    \end{itemize} -/)]
structure Algorithm (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] where
  /-- Policy or sampling rule: distribution of the next action. -/
  policy : (n : ℕ) → Kernel (Iic n → α × R) α
  [h_policy : ∀ n, IsMarkovKernel (policy n)]
  /-- Distribution of the first action. -/
  p0 : Measure α
  [hp0 : IsProbabilityMeasure p0]

instance (alg : Algorithm α R) (n : ℕ) : IsMarkovKernel (alg.policy n) := alg.h_policy n
instance (alg : Algorithm α R) : IsProbabilityMeasure alg.p0 := alg.hp0

/-- A stochastic environment. -/
@[blueprint
  "def:environment"
  (title := "Environment")
  (statement := /-- An environment with which an algorithm interacts is described by the following
    data:
    \begin{itemize}
      \item for all $t \in \mathbb{N}$, a feedback $\nu_t : (\mathcal{A} \times \mathcal{R})^{t+1}
      \times \mathcal{A} \rightsquigarrow \mathcal{R}$, a Markov kernel which gives the distribution
      of the observation at time $t+1$ given the history of previous pulls and observations, and the
      action of the algorithm at time $t+1$,
      \item $\nu'_0 \in \mathcal{A} \rightsquigarrow \mathcal{R}$, a Markov kernel that gives the
      distribution of the first observation given the first action.
    \end{itemize} -/)]
structure Environment (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] where
  /-- Distribution of the next observation as function of the past history. -/
  feedback : (n : ℕ) → Kernel ((Iic n → α × R) × α) R
  [h_feedback : ∀ n, IsMarkovKernel (feedback n)]
  /-- Distribution of the first observation given the first action. -/
  ν0 : Kernel α R
  [hp0 : IsMarkovKernel ν0]

instance (env : Environment α R) (n : ℕ) : IsMarkovKernel (env.feedback n) := env.h_feedback n
instance (env : Environment α R) : IsMarkovKernel env.ν0 := env.hp0

/-- Kernel describing the distribution of the next action-reward pair given the history
up to `n`. -/
noncomputable
def stepKernel (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    Kernel (Iic n → α × R) (α × R) :=
  alg.policy n ⊗ₖ env.feedback n
deriving IsMarkovKernel

@[simp]
lemma fst_stepKernel (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    (stepKernel alg env n).fst = alg.policy n := by
  rw [stepKernel, Kernel.fst_compProd]

section IsAlgEnvSeq

variable {A : ℕ → Ω → α} {R' : ℕ → Ω → R} {alg : Algorithm α R} {env : Environment α R}
    {P : Measure Ω} [IsFiniteMeasure P]

/-- Step of the algorithm-environment sequence: the action-reward pair at time `n`. -/
@[blueprint
  "def:history"
  (title := "History")
  (statement := /-- For two sequences of random variables $A : \mathbb{N} \to \Omega \to
    \mathcal{A}$ and $R : \mathbb{N} \to \Omega \to \mathcal{R}$ (actions and observations), we call
    step of the interaction at time $t$ the random variable $X_t : \Omega \to \mathcal{A} \times
    \mathcal{R}$ defined by $X_t(\omega) = (A_t(\omega), R_t(\omega))$.
    We call history up to time $t$ the random variable $H_t : \Omega \to (\mathcal{A} \times
    \mathcal{R})^{t+1}$ defined by $H_t(\omega) = (X_0(\omega), \ldots, X_t(\omega))$. -/)]
def IsAlgEnvSeq.step (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (n : ℕ) (ω : Ω) : α × R :=
  (A n ω, R' n ω)

@[fun_prop]
lemma IsAlgEnvSeq.measurable_step (n : ℕ) (hA : Measurable (A n))
    (hR' : Measurable (R' n)) :
    Measurable (IsAlgEnvSeq.step A R' n) := by
  unfold IsAlgEnvSeq.step
  fun_prop

/-- History of the algorithm-environment sequence up to time `n`. -/
@[blueprint
  "def:history"
  (title := "History")
  (statement := /-- For two sequences of random variables $A : \mathbb{N} \to \Omega \to
    \mathcal{A}$ and $R : \mathbb{N} \to \Omega \to \mathcal{R}$ (actions and observations), we call
    step of the interaction at time $t$ the random variable $X_t : \Omega \to \mathcal{A} \times
    \mathcal{R}$ defined by $X_t(\omega) = (A_t(\omega), R_t(\omega))$.
    We call history up to time $t$ the random variable $H_t : \Omega \to (\mathcal{A} \times
    \mathcal{R})^{t+1}$ defined by $H_t(\omega) = (X_0(\omega), \ldots, X_t(\omega))$. -/)]
def IsAlgEnvSeq.hist (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (n : ℕ) (ω : Ω) : Iic n → α × R :=
  fun i ↦ (A i ω, R' i ω)

@[fun_prop]
lemma IsAlgEnvSeq.measurable_hist (hA : ∀ n, Measurable (A n))
    (hR' : ∀ n, Measurable (R' n)) (n : ℕ) :
    Measurable (IsAlgEnvSeq.hist A R' n) := by
  unfold IsAlgEnvSeq.hist
  fun_prop

lemma IsAlgEnvSeq.eval_comp_hist (n : ℕ) :
    (fun x ↦ x ⟨n, by simp⟩) ∘ (hist A R' n) = step A R' n := rfl

lemma IsAlgEnvSeq.fst_eval_comp_hist (n : ℕ) :
    (fun x ↦ (x ⟨n, by simp⟩).1) ∘ (hist A R' n) = A n := rfl

lemma IsAlgEnvSeq.snd_eval_comp_hist (n : ℕ) :
    (fun x ↦ (x ⟨n, by simp⟩).2) ∘ (hist A R' n) = R' n := rfl

/-- An algorithm-environment sequence: a sequence of actions and rewards generated
by an algorithm interacting with an environment. -/
@[blueprint
  "def:IsAlgEnvSeq"
  (title := "Algorithm-environment interaction")
  (statement := /-- Let $\mathfrak{A}$ be an algorithm as in Definition~\ref{def:algorithm} and
    $\mathfrak{E}$ be an environment as in Definition~\ref{def:environment}.
    A probability space $(\Omega, P)$ and two sequences of random variables $A : \mathbb{N} \to
    \Omega \to \mathcal{A}$ and $R : \mathbb{N} \to \Omega \to \mathcal{R}$ form an
    algorithm-environment interaction for $\mathfrak{A}$ and $\mathfrak{E}$ if the following
    conditions hold:
    \begin{enumerate}
      \item The law of $A_0$ is $P_0$.
      \item $P \left[ R_0 \mid A_0 \right] = \nu'_0$.
      \item For all $t \in \mathbb{N}$, $P\left[A_{t+1} \mid A_0, R_0, \ldots, A_t, R_t \right] =
      \pi_t$.
      \item For all $t \in \mathbb{N}$, $P\left[R_{t+1} \mid A_0, R_0, \ldots, A_t, R_t,
      A_{t+1}\right] = \nu_t$.
    \end{enumerate} -/)]
structure IsAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (alg : Algorithm α R) (env : Environment α R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_action_zero : HasLaw (fun ω ↦ (A 0 ω)) alg.p0 P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (A 0) env.ν0 P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (env.feedback n) P

attribute [blueprint
  "thm:ionescu-tulcea"
  (title := "Ionescu-Tulcea")
  (statement := /-- Let $(\Omega_t)_{t \in \mathbb{N}}$ be a family of measurable spaces. Let
    $(\kappa_t)_{t \in \mathbb{N}}$ be a family of Markov kernels such that for any $t$, $\kappa_t$
    is a kernel from $\prod_{i=0}^t \Omega_{i}$ to $\Omega_{t+1}$.
    Then there exists a unique Markov kernel $\xi : \Omega_0 \rightsquigarrow \prod_{i = 1}^{\infty}
    \Omega_{i}$ such that for any $n \ge 1$,
    $\pi_{[1,n]*} \xi = \kappa_0 \otimes \ldots \otimes \kappa_{n-1}$.
    Here $\pi_{[1,n]} : \prod_{i=1}^{\infty} \Omega_i \to \prod_{i=1}^n \Omega_i$ is the projection
    on the first $n$ coordinates. -/)]
  ProbabilityTheory.Kernel.traj

attribute [blueprint
  "def:trajMeasure"
  (title := "Trajectory measure")
  (statement := /-- For $\mu \in \mathcal{P}(\Omega_0)$, we call trajectory measure the probability
    measure $\xi_0 \circ \mu$ on $\Omega_{\mathcal{T}} := \prod_{i=0}^{\infty} \Omega_i$.
    We denote it by $P_{\mathcal{T}}$.
    The $\mathcal{T}$ subscript stands for ``trajectory''. -/)]
  ProbabilityTheory.Kernel.trajMeasure

@[blueprint
  "lem:law_step"
  (statement := /-- In an algorithm-environment interaction $(A, R, P)$ as in
    Definition~\ref{def:IsAlgEnvSeq},
    \begin{itemize}
      \item the law of the initial step $X_0$ is $P_0 \otimes \nu'_0$,
      \item for all $t \in \mathbb{N}$, $P \left[ X_{t+1} \mid H_t \right] = \pi_t \otimes \nu_t$.
    \end{itemize} -/)
  (proof := /-- Immediate from the properties of an algorithm-environment interaction. -/)
  (latexEnv := "lemma")]
lemma IsAlgEnvSeq.hasLaw_step_zero
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) :
    HasLaw (step A R' 0) (alg.p0 ⊗ₘ env.ν0) P :=
  HasLaw.prod_of_hasCondDistrib h.hasLaw_action_zero h.hasCondDistrib_reward_zero

@[blueprint
  "lem:law_step"
  (statement := /-- In an algorithm-environment interaction $(A, R, P)$ as in
    Definition~\ref{def:IsAlgEnvSeq},
    \begin{itemize}
      \item the law of the initial step $X_0$ is $P_0 \otimes \nu'_0$,
      \item for all $t \in \mathbb{N}$, $P \left[ X_{t+1} \mid H_t \right] = \pi_t \otimes \nu_t$.
    \end{itemize} -/)
  (proof := /-- Immediate from the properties of an algorithm-environment interaction. -/)
  (latexEnv := "lemma")]
lemma IsAlgEnvSeq.hasCondDistrib_step
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    HasCondDistrib (step A R' (n + 1)) (hist A R' n) (stepKernel alg env n) P :=
  HasCondDistrib.prod (h.hasCondDistrib_action n) (h.hasCondDistrib_reward n)

/-- Filtration generated by the history up to time `n`. -/
@[blueprint
  "def:IsAlgEnvSeq.filtration"
  (statement := /-- For an algorithm-environment interaction $(A, R, P)$ as in
    Definition~\ref{def:IsAlgEnvSeq}, we denote by $\mathcal{F}_t$ the sigma-algebra generated by
    the history up to time $t$: $\mathcal{F}_t = \sigma(H_t)$.
    We denote by $\mathcal{F}^A_t$ the sigma-algebra generated by the history up to time $t-1$ and
    the action at time $t$: $\mathcal{F}^A_t = \sigma(H_{t-1}, A_t)$. -/)]
def IsAlgEnvSeq.filtration (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) :
    Filtration ℕ mΩ where
  seq i := MeasurableSpace.comap (hist A R' i) inferInstance
  mono' i j hij := by
    simp only
    rw [← measurable_iff_comap_le]
    have : hist A R' i = (fun h k ↦ h ⟨k.1, by grind⟩) ∘ hist A R' j := rfl
    rw [this]
    exact measurable_comp_comap _ (by fun_prop)
  le' i := by
    rw [← measurable_iff_comap_le]
    exact measurable_hist hA hR' i

lemma IsAlgEnvSeq.measurable_action_filtration
    (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) (n : ℕ) :
    Measurable[IsAlgEnvSeq.filtration hA hR' n] (A n) := by
  have : A n = (fun h ↦ (h ⟨n, by simp⟩).1) ∘ (hist A R' n) := by
    ext ω : 1
    simp [IsAlgEnvSeq.hist]
  rw [this]
  exact measurable_comp_comap _ (by fun_prop)

/-- Filtration generated by the history at time `n-1` together with the action at time `n`. -/
@[blueprint
  "def:IsAlgEnvSeq.filtration"
  (statement := /-- For an algorithm-environment interaction $(A, R, P)$ as in
    Definition~\ref{def:IsAlgEnvSeq}, we denote by $\mathcal{F}_t$ the sigma-algebra generated by
    the history up to time $t$: $\mathcal{F}_t = \sigma(H_t)$.
    We denote by $\mathcal{F}^A_t$ the sigma-algebra generated by the history up to time $t-1$ and
    the action at time $t$: $\mathcal{F}^A_t = \sigma(H_{t-1}, A_t)$. -/)]
def IsAlgEnvSeq.filtrationAction
    (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) :
    Filtration ℕ mΩ where
  seq n := if n = 0 then MeasurableSpace.comap (A 0) inferInstance
    else IsAlgEnvSeq.filtration hA hR' (n - 1) ⊔ MeasurableSpace.comap (A n) inferInstance
  mono' n m hnm := by
    simp only
    by_cases hn : n = 0
    · by_cases hm : m = 0
      · simp [hn, hm]
      · simp only [hn, ↓reduceIte, hm]
        refine le_sup_of_le_left ?_
        rw [← measurable_iff_comap_le]
        suffices Measurable[IsAlgEnvSeq.filtration hA hR' 0] (A 0) from
          this.mono ((IsAlgEnvSeq.filtration hA hR').mono zero_le') le_rfl
        exact measurable_action_filtration hA hR' 0
    have hm : m ≠ 0 := by grind
    simp only [hn, hm, ↓reduceIte]
    have hnm' : n - 1 ≤ m - 1 := by grind
    simp only [sup_le_iff]
    constructor
    · refine le_sup_of_le_left ?_
      exact (IsAlgEnvSeq.filtration hA hR').mono hnm'
    · rcases eq_or_lt_of_le hnm with rfl | hlt
      · exact le_sup_of_le_right le_rfl
      refine le_sup_of_le_left ?_
      rw [← measurable_iff_comap_le]
      have h_le : n ≤ m - 1 := by grind
      suffices Measurable[IsAlgEnvSeq.filtration hA hR' n] (A n) from
        this.mono ((IsAlgEnvSeq.filtration hA hR').mono h_le) le_rfl
      exact measurable_action_filtration hA hR' n
  le' n := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      rw [← measurable_iff_comap_le]
      fun_prop
    simp only [hn, ↓reduceIte, sup_le_iff]
    constructor
    · exact (IsAlgEnvSeq.filtration hA hR').le _
    · rw [← measurable_iff_comap_le]
      fun_prop

lemma IsAlgEnvSeq.filtrationAction_zero_eq_comap
    {hA : ∀ n, Measurable (A n)} {hR' : ∀ n, Measurable (R' n)} :
    filtrationAction hA hR' 0 = MeasurableSpace.comap (A 0) inferInstance := by
  simp [filtrationAction]

lemma IsAlgEnvSeq.filtrationAction_eq_comap
    {hA : ∀ n, Measurable (A n)} {hR' : ∀ n, Measurable (R' n)} (n : ℕ) (hn : n ≠ 0) :
    filtrationAction hA hR' n =
      MeasurableSpace.comap (fun ω ↦ (hist A R' (n - 1) ω, A n ω)) inferInstance := by
  simp only [filtrationAction, filtration, ← MeasurableSpace.comap_prodMk, hn, ↓reduceIte]
  rfl

end IsAlgEnvSeq

/-- Kernel sending a partial trajectory of the bandit Seq `Iic n → α × ℝ` to a measure
on `ℕ → α × ℝ`, supported on full trajectories that start with the partial one. -/
noncomputable def traj (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    Kernel (Iic n → α × R) (ℕ → α × R) :=
  Kernel.traj (X := fun _ ↦ α × R) (stepKernel alg env) n
deriving IsMarkovKernel

/-- Measure on the sequence of actions and observations generated by the algorithm/environment. -/
noncomputable
def trajMeasure (alg : Algorithm α R) (env : Environment α R) :
    Measure (ℕ → α × R) :=
  Kernel.trajMeasure (alg.p0 ⊗ₘ env.ν0) (stepKernel alg env)
deriving IsProbabilityMeasure

section ModelEquivalence

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {env : Environment α R}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {A₁ : ℕ → Ω → α} {R₁ : ℕ → Ω → R} {A₂ : ℕ → Ω' → α} {R₂ : ℕ → Ω' → R}

theorem eq_trajMeasure_of_isAlgEnvSeq (h : IsAlgEnvSeq A₁ R₁ alg env P) :
    P.map (fun ω n ↦ (A₁ n ω, R₁ n ω)) = trajMeasure alg env := by
  rw [trajMeasure]
  have h := Kernel.eq_trajMeasure (Y := fun n ω ↦ (A₁ n ω, R₁ n ω)) (P := P)
    (μ₀ := alg.p0 ⊗ₘ env.ν0) (κ := stepKernel alg env) (fun n ↦ ?_) ?_ (fun n ↦ ?_)
  · exact h
  · have hA := h.measurable_A n
    have hR := h.measurable_R n
    fun_prop
  · simp only
    exact h.hasLaw_step_zero
  · exact h.hasCondDistrib_step n

@[blueprint
  "thm:isAlgEnvSeq_unique"
  (title := "\\cite{lattimore2020bandit}, Proposition 4.8")
  (statement := /-- If $(A, R, P)$ and $(A', R', P')$ are two algorithm-environment interactions for
    the same algorithm $\mathfrak{A}$ and environment $\mathfrak{E}$, then the joint distributions
    of the sequences of actions and observations are equal: the law of $(A_i, R_i)_{i \in
    \mathbb{N}}$ under $P$ is equal to the law of $(A'_i, R'_i)_{i \in \mathbb{N}}$ under $P'$. -/)]
theorem isAlgEnvSeq_unique (h1 : IsAlgEnvSeq A₁ R₁ alg env P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg env P') :
    P.map (fun ω n ↦ (A₁ n ω, R₁ n ω)) = P'.map (fun ω n ↦ (A₂ n ω, R₂ n ω)) := by
  rw [eq_trajMeasure_of_isAlgEnvSeq h1, eq_trajMeasure_of_isAlgEnvSeq h2]

end ModelEquivalence

end Learning
