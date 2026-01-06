/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.HasCondDistrib
import LeanBandits.ForMathlib.Measurable
import LeanBandits.ForMathlib.Traj
import Mathlib.Probability.HasLaw

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
    {P : Measure Ω} [IsFiniteMeasure P]

def IsAlgEnvSeq.step (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (n : ℕ) (ω : Ω) : α × R :=
  (A n ω, R' n ω)

@[fun_prop]
lemma IsAlgEnvSeq.measurable_step (n : ℕ) (hA : Measurable (A n))
    (hR' : Measurable (R' n)) :
    Measurable (IsAlgEnvSeq.step A R' n) := by
  unfold IsAlgEnvSeq.step
  fun_prop

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

lemma IsAlgEnvSeq.hasLaw_step_zero
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) :
    HasLaw (step A R' 0) (alg.p0 ⊗ₘ env.ν0) P :=
  HasLaw.prod_of_hasCondDistrib h.hasLaw_action_zero h.hasCondDistrib_reward_zero

lemma IsAlgEnvSeq.hasCondDistrib_step
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    HasCondDistrib (step A R' (n + 1)) (hist A R' n) (stepKernel alg env n) P :=
  HasCondDistrib.prod (h.hasCondDistrib_action n) (h.hasCondDistrib_reward n)

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
    exact h.hasLaw_step_zero.map_eq
  · exact (h.hasCondDistrib_step n).condDistrib_eq

theorem isAlgEnvSeq_unique (h1 : IsAlgEnvSeq A₁ R₁ alg env P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg env P') :
    P.map (fun ω n ↦ (A₁ n ω, R₁ n ω)) = P'.map (fun ω n ↦ (A₂ n ω, R₂ n ω)) := by
  rw [eq_trajMeasure_of_isAlgEnvSeq h1, eq_trajMeasure_of_isAlgEnvSeq h2]

end ModelEquivalence

namespace IT

/-- Action and reward at step `n`. -/
def step (n : ℕ) (h : ℕ → α × R) : α × R := h n

/-- `action n` is the action pulled at time `n`. This is a random variable on the measurable space
`ℕ → α × ℝ`. -/
def action (n : ℕ) (h : ℕ → α × R) : α := (h n).1

/-- `reward n` is the reward at time `n`. This is a random variable on the measurable space
`ℕ → α × R`. -/
def reward (n : ℕ) (h : ℕ → α × R) : R := (h n).2

/-- `hist n` is the history up to time `n`. This is a random variable on the measurable space
`ℕ → α × R`. -/
def hist (n : ℕ) (h : ℕ → α × R) : Iic n → α × R := fun i ↦ h i

lemma fst_comp_step (n : ℕ) : Prod.fst ∘ step (α := α) (R := R) n = action n := rfl

@[fun_prop]
lemma measurable_step (n : ℕ) : Measurable (step n (α := α) (R := R)) := by
  unfold step; fun_prop

@[fun_prop]
lemma measurable_step_prod : Measurable (fun p : ℕ × (ℕ → α × R) ↦ step p.1 p.2) :=
  measurable_from_prod_countable_right fun n ↦ (by simp only; fun_prop)

@[fun_prop]
lemma measurable_action (n : ℕ) : Measurable (action n (α := α) (R := R)) := by
  unfold action; fun_prop

@[fun_prop]
lemma measurable_action_prod : Measurable (fun p : ℕ × (ℕ → α × R) ↦ action p.1 p.2) :=
  measurable_from_prod_countable_right fun n ↦ (by simp only; fun_prop)

@[fun_prop]
lemma measurable_reward (n : ℕ) : Measurable (reward n (α := α) (R := R)) := by
  unfold reward; fun_prop

@[fun_prop]
lemma measurable_reward_prod : Measurable (fun p : ℕ × (ℕ → α × R) ↦ reward p.1 p.2) :=
  measurable_from_prod_countable_right fun n ↦ (by simp only; fun_prop)

@[fun_prop]
lemma measurable_hist (n : ℕ) : Measurable (hist n (α := α) (R := R)) := by unfold hist; fun_prop

lemma hist_eq_frestrictLe :
    hist = Preorder.frestrictLe («π» := fun _ ↦ α × R) := by
  ext n h i : 3
  simp [hist, Preorder.frestrictLe]

/-- Filtration of the algorithm Seq. -/
protected def filtration (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α × R)) :=
  MeasureTheory.Filtration.piLE (X := fun _ ↦ α × R)

lemma filtration_eq_comap (n : ℕ) :
    IT.filtration α R n = MeasurableSpace.comap (hist n) inferInstance := by
  simp [IT.filtration, Filtration.piLE_eq_comap_frestrictLe, ← hist_eq_frestrictLe]

lemma step_eq_eval_comp_hist (n : ℕ) :
    step (α := α) (R := R) n = (fun x ↦ x ⟨n, by simp⟩) ∘ (hist n) := rfl

lemma action_eq_eval_comp_hist (n : ℕ) :
    action (α := α) (R := R) n = (fun x ↦ (x ⟨n, by simp⟩).1) ∘ (hist n) := rfl

lemma reward_eq_eval_comp_hist (n : ℕ) :
    reward (α := α) (R := R) n = (fun x ↦ (x ⟨n, by simp⟩).2) ∘ (hist n) := rfl

lemma measurable_step_filtration (n : ℕ) : Measurable[IT.filtration α R n] (step n) := by
  rw [filtration_eq_comap, step_eq_eval_comp_hist]
  exact measurable_comp_comap _ (by fun_prop)

lemma adapted_step [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
    [SecondCountableTopology α] [OpensMeasurableSpace α]
    [TopologicalSpace R] [TopologicalSpace.PseudoMetrizableSpace R]
    [SecondCountableTopology R] [OpensMeasurableSpace R] :
    Adapted (IT.filtration α R) (step (α := α) (R := R)) :=
  fun n ↦ (measurable_step_filtration n).stronglyMeasurable

lemma measurable_hist_filtration (n : ℕ) : Measurable[IT.filtration α R n] (hist n) := by
  simp [filtration_eq_comap, measurable_iff_comap_le]

lemma adapted_hist [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
    [SecondCountableTopology α] [OpensMeasurableSpace α]
    [TopologicalSpace R] [TopologicalSpace.PseudoMetrizableSpace R]
    [SecondCountableTopology R] [OpensMeasurableSpace R] :
    Adapted (IT.filtration α R) hist :=
  fun n ↦ (measurable_hist_filtration n).stronglyMeasurable

lemma measurable_action_filtration (n : ℕ) : Measurable[IT.filtration α R n] (action n) := by
  rw [filtration_eq_comap, action_eq_eval_comp_hist]
  exact measurable_comp_comap _ (by fun_prop)

lemma adapted_action [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    Adapted (IT.filtration α R) action :=
  fun n ↦ (measurable_action_filtration n).stronglyMeasurable

lemma measurable_reward_filtration (n : ℕ) : Measurable[IT.filtration α R n] (reward n) := by
  rw [filtration_eq_comap, reward_eq_eval_comp_hist]
  exact measurable_comp_comap _ (by fun_prop)

lemma adapted_reward [TopologicalSpace R] [TopologicalSpace.PseudoMetrizableSpace R]
    [SecondCountableTopology R] [OpensMeasurableSpace R] :
    Adapted (IT.filtration α R) reward :=
  fun n ↦ (measurable_reward_filtration n).stronglyMeasurable

section FiltrationAction

/-- Filtration generated by the history at time `n-1` together with the action at time `n`. -/
def filtrationAction (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α × R)) where
  seq n := if n = 0 then MeasurableSpace.comap (action 0) inferInstance
    else IT.filtration α R (n - 1) ⊔ MeasurableSpace.comap (action n) inferInstance
  mono' n m hnm := by
    simp only
    by_cases hn : n = 0
    · by_cases hm : m = 0
      · simp [hn, hm]
      · simp only [hn, ↓reduceIte, hm]
        refine le_sup_of_le_left ?_
        rw [← measurable_iff_comap_le]
        suffices Measurable[IT.filtration α R 0] (action 0) from
          this.mono ((IT.filtration α R).mono zero_le') le_rfl
        exact measurable_action_filtration 0
    have hm : m ≠ 0 := by grind
    simp only [hn, hm, ↓reduceIte]
    have hnm' : n - 1 ≤ m - 1 := by grind
    simp only [sup_le_iff]
    constructor
    · refine le_sup_of_le_left ?_
      exact (IT.filtration α R).mono hnm'
    · rcases eq_or_lt_of_le hnm with rfl | hlt
      · exact le_sup_of_le_right le_rfl
      refine le_sup_of_le_left ?_
      rw [← measurable_iff_comap_le]
      have h_le : n ≤ m - 1 := by grind
      suffices Measurable[IT.filtration α R n] (action n) from
        this.mono ((IT.filtration α R).mono h_le) le_rfl
      exact measurable_action_filtration n
  le' n := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      rw [← measurable_iff_comap_le]
      fun_prop
    simp only [hn, ↓reduceIte, sup_le_iff]
    constructor
    · exact (IT.filtration α R).le _
    · rw [← measurable_iff_comap_le]
      fun_prop

lemma filtrationAction_zero_eq_comap :
    filtrationAction α R 0 = MeasurableSpace.comap (action 0) inferInstance := by
  simp [filtrationAction]

lemma filtrationAction_eq_comap (n : ℕ) (hn : n ≠ 0) :
    filtrationAction α R n =
      MeasurableSpace.comap (fun ω ↦ (hist (n - 1) ω, action n ω)) inferInstance := by
  simp only [filtrationAction, filtration_eq_comap, ← MeasurableSpace.comap_prodMk, hn, ↓reduceIte]
  rfl

lemma filtration_le_filtrationAction_add_one (n : ℕ) :
    IT.filtration α R n ≤ filtrationAction α R (n + 1) := le_sup_of_le_left le_rfl

lemma filtration_le_filtrationAction {m n : ℕ} (h : n < m) :
    IT.filtration α R n ≤ filtrationAction α R m := by
  have h' : n + 1 ≤ m := by grind
  exact (filtration_le_filtrationAction_add_one n).trans ((filtrationAction α R).mono h')

lemma filtrationAction_le_filtration_self (n : ℕ) :
    filtrationAction α R n ≤ IT.filtration α R n := by
  by_cases hn : n = 0
  · simp only [hn, filtrationAction_zero_eq_comap]
    rw [← measurable_iff_comap_le]
    exact measurable_action_filtration 0
  simp only [filtrationAction, hn, ↓reduceIte, sup_le_iff]
  constructor
  · exact (IT.filtration α R).mono (by grind)
  · rw [← measurable_iff_comap_le]
    exact measurable_action_filtration _

lemma filtrationAction_le_filtration {m n : ℕ} (h : m ≤ n) :
    filtrationAction α R m ≤ IT.filtration α R n :=
  (filtrationAction_le_filtration_self m).trans ((IT.filtration α R).mono h)

lemma measurable_action_filtrationAction (n : ℕ) :
    Measurable[filtrationAction α R n] (action n) := by
  simp only [filtrationAction]
  rw [measurable_iff_comap_le]
  split_ifs with hn
  · simp [hn]
  · exact le_sup_of_le_right le_rfl

end FiltrationAction

section Laws

lemma hasLaw_step_zero (alg : Algorithm α R) (env : Environment α R) :
    HasLaw (step 0) (alg.p0 ⊗ₘ env.ν0) (trajMeasure alg env) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    unfold step
    rw [← coe_default_Iic_zero]
    simp only [trajMeasure, Kernel.trajMeasure]
    rw [← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc,
      Kernel.deterministic_comp_eq_map, Kernel.traj_zero_map_eval_zero,
      Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id

lemma hasLaw_action_zero (alg : Algorithm α R) (env : Environment α R) :
    HasLaw (action 0) alg.p0 (trajMeasure alg env) where
  map_eq := by
    rw [← fst_comp_step, ← Measure.map_map (by fun_prop) (by fun_prop),
      (hasLaw_step_zero alg env).map_eq, ← Measure.fst, Measure.fst_compProd]

variable [StandardBorelSpace R] [Nonempty R]

lemma condDistrib_reward_zero (alg : Algorithm α R) (env : Environment α R) :
    condDistrib (reward 0) (action 0) (trajMeasure alg env)
      =ᵐ[(trajMeasure alg env).map (action 0)] env.ν0 := by
  have h_step := (hasLaw_step_zero alg env).map_eq
  have h_action := (hasLaw_action_zero alg env).map_eq
  rwa [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop), h_action]

variable [StandardBorelSpace α] [Nonempty α]

lemma condDistrib_step (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    condDistrib (step (n + 1)) (hist n) (trajMeasure alg env)
      =ᵐ[(trajMeasure alg env).map (hist n)] stepKernel alg env n :=
  Kernel.condDistrib_trajMeasure

lemma condDistrib_action (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    condDistrib (action (n + 1)) (hist n) (trajMeasure alg env)
      =ᵐ[(trajMeasure alg env).map (hist n)] alg.policy n := by
  rw [← fst_comp_step]
  refine (condDistrib_comp _ (by fun_prop) (by fun_prop)).trans ?_
  filter_upwards [condDistrib_step alg env n] with h h_eq
  rw [Kernel.map_apply _ (by fun_prop), h_eq, ← Kernel.map_apply _ (by fun_prop), ← Kernel.fst_eq,
    fst_stepKernel]

lemma condDistrib_reward (alg : Algorithm α R) (env : Environment α R) (n : ℕ) :
    condDistrib (reward (n + 1)) (fun ω ↦ (hist n ω, action (n + 1) ω)) (trajMeasure alg env)
      =ᵐ[(trajMeasure alg env).map (fun ω ↦ (hist n ω, action (n + 1) ω))] env.feedback n := by
  have h_step := condDistrib_step alg env n
  have h_action := condDistrib_action alg env n
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_step h_action ⊢
  rw [h_action, ← Measure.compProd_assoc, ← stepKernel, ← h_step,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma isAlgEnvSeq_trajMeasure (alg : Algorithm α R) (env : Environment α R) :
    IsAlgEnvSeq action reward alg env (trajMeasure alg env) where
  hasLaw_action_zero := hasLaw_action_zero alg env
  hasCondDistrib_reward_zero := ⟨by fun_prop, by fun_prop, condDistrib_reward_zero alg env⟩
  hasCondDistrib_action n := ⟨by fun_prop, by fun_prop, condDistrib_action alg env n⟩
  hasCondDistrib_reward n := ⟨by fun_prop, by fun_prop, condDistrib_reward alg env n⟩

end Laws

end IT

end Learning
