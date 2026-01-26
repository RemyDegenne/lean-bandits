/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
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
structure Algorithm (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] where
  /-- Policy or sampling rule: distribution of the next action. -/
  policy : (n : ℕ) → Kernel (Iic n → α × R) α
  [h_policy : ∀ n, IsMarkovKernel (policy n)]
  /-- Distribution of the first action. -/
  p0 : Measure α
  [hp0 : IsProbabilityMeasure p0]

instance (alg : Algorithm α R) (n : ℕ) : IsMarkovKernel (alg.policy n) := alg.h_policy n
instance (alg : Algorithm α R) : IsProbabilityMeasure alg.p0 := alg.hp0

/-- An algorithm that receives observations in `E × R` created form an algorithm that receives
observations in `R` by ignoring the additional information. -/
def Algorithm.prod_left (E : Type*) [MeasurableSpace E] (alg : Algorithm α R) :
    Algorithm α (E × R) where
  policy n := (alg.policy n).comap (fun h i ↦ ((h i).1, (h i).2.2)) (by fun_prop)
  p0 := alg.p0

/-- A stochastic environment. -/
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
    {P : Measure Ω} [IsFiniteMeasure P] {N : ℕ}

/-- Step of the algorithm-environment sequence: the action-reward pair at time `n`. -/
def IsAlgEnvSeq.step (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (n : ℕ) (ω : Ω) : α × R :=
  (A n ω, R' n ω)

@[fun_prop]
lemma IsAlgEnvSeq.measurable_step (n : ℕ) (hA : Measurable (A n))
    (hR' : Measurable (R' n)) :
    Measurable (IsAlgEnvSeq.step A R' n) := by
  unfold IsAlgEnvSeq.step
  fun_prop

/-- History of the algorithm-environment sequence up to time `n`. -/
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

/-- An algorithm-environment sequence: a sequence of actions and rewards generated
by an algorithm interacting with an environment. -/
structure IsAlgEnvSeqUntil
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (alg : Algorithm α R) (env : Environment α R)
    (P : Measure Ω) [IsFiniteMeasure P] (N : ℕ) : Prop where
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_action_zero : HasLaw (fun ω ↦ (A 0 ω)) alg.p0 P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (A 0) env.ν0 P
  hasCondDistrib_action n (hn : n < N) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P
  hasCondDistrib_reward n (hn : n < N) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (env.feedback n) P

lemma IsAlgEnvSeqUntil.mono [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeqUntil A R' alg env P N) {N' : ℕ} (hN : N' ≤ N) :
    IsAlgEnvSeqUntil A R' alg env P N' where
  measurable_A := h.measurable_A
  measurable_R := h.measurable_R
  hasLaw_action_zero := h.hasLaw_action_zero
  hasCondDistrib_reward_zero := h.hasCondDistrib_reward_zero
  hasCondDistrib_action n hn := h.hasCondDistrib_action n (hn.trans_le hN)
  hasCondDistrib_reward n hn := h.hasCondDistrib_reward n (hn.trans_le hN)

lemma IsAlgEnvSeq.isAlgEnvSeqUntil
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) (N : ℕ) :
    IsAlgEnvSeqUntil A R' alg env P N where
  measurable_A := h.measurable_A
  measurable_R := h.measurable_R
  hasLaw_action_zero := h.hasLaw_action_zero
  hasCondDistrib_reward_zero := h.hasCondDistrib_reward_zero
  hasCondDistrib_action n _ := h.hasCondDistrib_action n
  hasCondDistrib_reward n _ := h.hasCondDistrib_reward n

lemma IsAlgEnvSeq.hasLaw_step_zero
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) :
    HasLaw (step A R' 0) (alg.p0 ⊗ₘ env.ν0) P :=
  HasLaw.prod_of_hasCondDistrib h.hasLaw_action_zero h.hasCondDistrib_reward_zero

lemma IsAlgEnvSeqUntil.hasLaw_step_zero
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeqUntil A R' alg env P N) :
    HasLaw (IsAlgEnvSeq.step A R' 0) (alg.p0 ⊗ₘ env.ν0) P :=
  HasLaw.prod_of_hasCondDistrib h.hasLaw_action_zero h.hasCondDistrib_reward_zero

lemma IsAlgEnvSeq.hasCondDistrib_step
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    HasCondDistrib (step A R' (n + 1)) (hist A R' n) (stepKernel alg env n) P :=
  HasCondDistrib.prod (h.hasCondDistrib_action n) (h.hasCondDistrib_reward n)

lemma IsAlgEnvSeqUntil.hasCondDistrib_step
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeqUntil A R' alg env P N) (n : ℕ) (hn : n < N) :
    HasCondDistrib (IsAlgEnvSeq.step A R' (n + 1)) (IsAlgEnvSeq.hist A R' n)
      (stepKernel alg env n) P :=
  HasCondDistrib.prod (h.hasCondDistrib_action n hn) (h.hasCondDistrib_reward n hn)

/-- Filtration generated by the history up to time `n`. -/
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
  {A₁ : ℕ → Ω → α} {R₁ : ℕ → Ω → R} {A₂ : ℕ → Ω' → α} {R₂ : ℕ → Ω' → R} {N : ℕ}

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

lemma eq_trajMeasure_map_frestrictLe_of_isAlgEnvSeqUntil
    (h : IsAlgEnvSeqUntil A₁ R₁ alg env P N) :
    P.map (fun ω (n : Iic N) ↦ (A₁ n ω, R₁ n ω)) =
      (trajMeasure alg env).map (Preorder.frestrictLe N) := by
  rw [trajMeasure]
  have h := Kernel.eq_trajMeasure_map_frestrictLe (Y := fun n ω ↦ (A₁ n ω, R₁ n ω))
    (P := P) (μ₀ := alg.p0 ⊗ₘ env.ν0) (κ := stepKernel alg env) ?_ (fun n hn ↦ ?_) (N := N)
  · exact h
  · exact h.hasLaw_step_zero
  · exact h.hasCondDistrib_step n hn

/-- The law of the sequence of actions and observations generated by an algorithm-environment pair
is unique: it does not depend on the probability space used. -/
theorem isAlgEnvSeq_unique (h1 : IsAlgEnvSeq A₁ R₁ alg env P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg env P') :
    P.map (fun ω n ↦ (A₁ n ω, R₁ n ω)) = P'.map (fun ω n ↦ (A₂ n ω, R₂ n ω)) := by
  rw [eq_trajMeasure_of_isAlgEnvSeq h1, eq_trajMeasure_of_isAlgEnvSeq h2]

theorem isAlgEnvSeqUntil_unique (h1 : IsAlgEnvSeqUntil A₁ R₁ alg env P N)
    (h2 : IsAlgEnvSeqUntil A₂ R₂ alg env P' N) :
    P.map (fun ω (n : Iic N) ↦ (A₁ n ω, R₁ n ω)) =
      P'.map (fun ω (n : Iic N) ↦ (A₂ n ω, R₂ n ω)) := by
  rw [eq_trajMeasure_map_frestrictLe_of_isAlgEnvSeqUntil h1,
    eq_trajMeasure_map_frestrictLe_of_isAlgEnvSeqUntil h2]

end ModelEquivalence

end Learning
