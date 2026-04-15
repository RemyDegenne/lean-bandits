/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Bandit.SumRewards
public import LeanMachineLearning.ForMathlib.MeasurableArgMax

/-! # Bayesian stationary environments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Learning

variable {𝓔 α R Ω : Type*}
variable [MeasurableSpace 𝓔] [MeasurableSpace α] [MeasurableSpace R] [MeasurableSpace Ω]

structure IsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) (κ : Kernel (𝓔 × α) R) (alg : Algorithm α R)
    (E : Ω → 𝓔) (A : ℕ → Ω → α) (R' : ℕ → Ω → R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E := by fun_prop
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E Q P
  hasCondDistrib_action_zero : HasCondDistrib (A 0) E (Kernel.const _ alg.p0) P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (fun ω ↦ (E ω, A 0 ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω))
      ((alg.policy n).prodMkLeft _) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, E ω, A (n + 1) ω))
      (κ.prodMkLeft _) P

namespace IsBayesAlgEnvSeq

def trajectory (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (ω : Ω) : ℕ → α × R := fun n ↦ (A n ω, R' n ω)

@[fun_prop]
lemma measurable_trajectory {A : ℕ → Ω → α} {R' : ℕ → Ω → R} (hA : ∀ n, Measurable (A n))
    (hR : ∀ n, Measurable (R' n)) : Measurable (trajectory A R') := by
  unfold trajectory
  fun_prop

section Real

noncomputable
def actionMean (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (a : α) (ω : Ω) : ℝ := (κ (E ω, a))[id]

@[fun_prop]
lemma measurable_actionMean {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {a : α} (hE : Measurable E) :
    Measurable (actionMean κ E a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)

@[fun_prop]
lemma measurable_uncurry_actionMean_comp [Countable α] [MeasurableSingletonClass α]
    {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} (hE : Measurable E) {f : Ω → α} (hf : Measurable f) :
    Measurable (fun ω ↦ actionMean κ E (f ω) ω) := by
  change Measurable ((fun aω ↦ actionMean κ E aω.1 aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun _ ↦ measurable_actionMean hE)

lemma integrable_uncurry_actionMean_comp [Countable α] [MeasurableSingletonClass α]
    {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} (hE : Measurable E) {f : Ω → α} (hf : Measurable f)
    {P : Measure Ω} [IsFiniteMeasure P] {l u : ℝ} (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) :
    Integrable (fun ω ↦ actionMean κ E (f ω) ω) P := by
  refine ⟨(measurable_uncurry_actionMean_comp hE hf).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with ω using abs_le_max_abs_abs (hm (E ω) (f ω)).1 (hm (E ω) (f ω)).2

noncomputable
def bestAction [Nonempty α] [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (ω : Ω) : α :=
  measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω

@[fun_prop]
lemma measurable_bestAction [Nonempty α] [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} (hE : Measurable E) : Measurable (bestAction κ E) :=
  measurable_measurableArgmax (by fun_prop)

/-- The gap at time `n`. -/
noncomputable
def gap (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  Bandits.gap (κ.sectR (E ω)) (A n ω)

omit [MeasurableSpace Ω] in
/-- The gap is non-negative if the means are bounded by `u : ℝ` (even if `α` is not `Finite`). -/
lemma gap_nonneg_of_le [Nonempty α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ}
    {ω : Ω} {u : ℝ} (h : ∀ e a, (κ (e, a))[id] ≤ u) : 0 ≤ gap κ E A n ω := by
  simp_rw [gap, Bandits.gap, Kernel.sectR_apply]
  linarith [le_ciSup ⟨u, Set.forall_mem_range.2 fun a ↦ (h (E ω) a)⟩ (A n ω)]

omit [MeasurableSpace Ω] in
lemma gap_le_of_mem_Icc [Nonempty α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ}
    {ω : Ω} {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) : gap κ E A n ω ≤ u - l := by
  simp_rw [gap, Bandits.gap, Kernel.sectR_apply]
  grind [ciSup_le (fun a ↦ (h (E ω) a).2)]

omit [MeasurableSpace Ω] in
lemma gap_eq_sub [Nonempty α] [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ} {ω : Ω} :
    gap κ E A n ω = actionMean κ E (bestAction κ E ω) ω - actionMean κ E (A n ω) ω := by
  rw [gap, Bandits.gap]
  congr
  apply le_antisymm
  · exact ciSup_le (isMaxOn_measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω)
  · exact Finite.le_ciSup (fun a ↦ actionMean κ E a ω) _

@[fun_prop]
lemma measurable_gap [Countable α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ}
    (hE : Measurable E) (hA : ∀ t, Measurable (A t)) : Measurable (gap κ E A n) :=
  (Measurable.iSup fun _ ↦ stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)).sub
    (stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop))

lemma integrable_gap [Countable α] [Nonempty α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔}
    {A : ℕ → Ω → α} {n : ℕ} {P : Measure Ω} [IsFiniteMeasure P] (hE : Measurable E)
    (hA : ∀ t, Measurable (A t)) {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) :
    Integrable (gap κ E A n) P := by
  apply Integrable.of_bound (by fun_prop) (u - l)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg_of_le (fun e a ↦ (h e a).2))]
  exact gap_le_of_mem_Icc h

noncomputable
def regret (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.sectR (E ω)) A n ω

omit [MeasurableSpace Ω] in
lemma regret_eq_sum_gap {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ} {ω : Ω} :
    regret κ E A n ω = ∑ s ∈ range n, gap κ E A s ω := by
  simp [regret, Bandits.regret, gap, Bandits.gap]

omit [MeasurableSpace Ω] in
lemma regret_eq_sum_gap' {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ} :
    regret κ E A n = fun ω ↦ ∑ s ∈ range n, gap κ E A s ω := funext fun _ ↦ regret_eq_sum_gap

@[fun_prop]
lemma measurable_regret [Countable α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {n : ℕ}
    (hE : Measurable E) (hA : ∀ t, Measurable (A t)) : Measurable (regret κ E A n) := by
  rw [regret_eq_sum_gap']
  fun_prop

lemma integrable_regret [Countable α] [Nonempty α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔}
    {A : ℕ → Ω → α} {n : ℕ} {P : Measure Ω} [IsFiniteMeasure P] (hE : Measurable E)
    (hA : ∀ t, Measurable (A t)) {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) :
    Integrable (regret κ E A n) P := by
  rw [regret_eq_sum_gap']
  exact integrable_finset_sum _ (fun _ _ ↦ integrable_gap hE hA h)

end Real

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔} {κ : Kernel (𝓔 × α) R} {alg : Algorithm α R}
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {P : Measure Ω} [IsFiniteMeasure P]

section Laws

lemma hasLaw_action_zero [IsProbabilityMeasure P] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    HasLaw (A 0) alg.p0 P := h.hasCondDistrib_action_zero.hasLaw_of_const

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

lemma hasCondDistrib_reward' [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (E ω, A (n + 1) ω)) κ P :=
  (h.hasCondDistrib_reward n).comp_left (by fun_prop)

end Laws

section CondDistribIsAlgEnvSeq

lemma hasLaw_IT_action_zero (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasLaw (IT.action 0) alg.p0 (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  filter_upwards [condDistrib_comp E
      ((measurable_trajectory h.measurable_A h.measurable_R).aemeasurable)
      (IT.measurable_action (α := α) (R := R) 0),
    h.hasCondDistrib_action_zero.condDistrib_eq] with _ hc hcd
  exact ⟨(IT.measurable_action 0).aemeasurable, by
    rw [← Kernel.map_apply _ (IT.measurable_action 0), ← hc,
      show IT.action 0 ∘ trajectory A R' = A 0 from rfl, hcd, Kernel.const_apply]⟩

lemma hasCondDistrib_IT_reward_zero [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward 0) (IT.action 0) (κ.sectR e)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  exact h.hasCondDistrib_reward_zero.ae_hasCondDistrib_sectR
    (IT.measurable_action 0) (IT.measurable_reward 0)
    (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable
    h.measurable_E.aemeasurable

lemma hasCondDistrib_IT_action (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.action (n + 1)) (IT.hist n) (alg.policy n)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  filter_upwards [(h.hasCondDistrib_action n).ae_hasCondDistrib_sectR
    (IT.measurable_hist n) (IT.measurable_action (n + 1))
    (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable
    h.measurable_E.aemeasurable] with _ he
  rwa [Kernel.sectR_prodMkLeft] at he

lemma hasCondDistrib_IT_reward [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward (n + 1)) (fun τ ↦ (IT.hist n τ, IT.action (n + 1) τ))
      ((κ.sectR e).prodMkLeft _) (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hc : HasCondDistrib (R' (n + 1))
      (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun (e, _, a) ↦ (e, a)) (by fun_prop)) P :=
    (h.hasCondDistrib_reward n).comp_right (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodCongr .prodComm (.refl _)).trans .prodAssoc))
  exact hc.ae_hasCondDistrib_sectR ((IT.measurable_hist n).prodMk
    (IT.measurable_action (n + 1))) (IT.measurable_reward (n + 1))
    (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable h.measurable_E.aemeasurable

lemma hasLaw_IT_hist (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasLaw (IT.hist n) (condDistrib (IsAlgEnvSeq.hist A R' n) E P e)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq, show IsAlgEnvSeq.hist A R' n = IT.hist n ∘ trajectory A R' from rfl]
  filter_upwards [condDistrib_comp E
    (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable
    (IT.measurable_hist n)] with _ he
  exact ⟨(IT.measurable_hist n).aemeasurable, by
    rw [← Kernel.map_apply _ (IT.measurable_hist n), he]⟩

lemma ae_IsAlgEnvSeq [IsMarkovKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, IsAlgEnvSeq IT.action IT.reward alg (stationaryEnv (κ.sectR e))
      (condDistrib (trajectory A R') E P e) := by
  filter_upwards [hasLaw_IT_action_zero h, hasCondDistrib_IT_reward_zero h,
    ae_all_iff.2 (hasCondDistrib_IT_action h), ae_all_iff.2 (hasCondDistrib_IT_reward h)]
    with _ ha0 hr0 hA hR
  exact ⟨IT.measurable_action, IT.measurable_reward, ha0, hr0, hA, hR⟩

end CondDistribIsAlgEnvSeq

section HasSubgaussianMGF

private lemma sqrt_two_mul_le {k : ℕ} (hk : k ≠ 0) {s μ σ l : ℝ}
    (h : √(2 * σ * l / k) ≤ |s / k - μ|) : √(2 * k * σ * l) ≤ |s - k * μ| := by
  have hkp : (0 : ℝ) < k := by positivity
  calc √(2 * k * σ * l)
    _ = √(2 * σ * l / k * k ^ 2) := by
      field_simp
    _ = √(2 * σ * l / k) * k := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hkp.le]
    _ ≤ |s / k - μ| * k := by
      nlinarith
    _ = |s - k * μ| := by
      field_simp
      grind

variable {K : ℕ} [Nonempty (Fin K)]
variable {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ] {alg : Algorithm (Fin K) ℝ}
variable {A : ℕ → Ω → (Fin K)} {R' : ℕ → Ω → ℝ}
variable [IsProbabilityMeasure P]

lemma prob_abs_empMean_sub_actionMean_ge_le (h : IsBayesAlgEnvSeq Q κ alg E A R' P) {σ2 : ℝ≥0}
    (hσ2 : 0 < σ2) (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, ∃ a, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / pullCount A a t ω) ≤ |empMean A R' a t ω - actionMean κ E a ω|}
      ≤ ENNReal.ofReal (2 * K * (n - 1) * δ) := by
  have := h.measurable_E
  have := h.measurable_A
  have := h.measurable_R
  let S := {(e, τ) | ∃ a, ∃ t < n, pullCount IT.action a t τ ≠ 0 ∧
    √(2 * pullCount IT.action a t τ * σ2 * Real.log (1 / δ)) ≤
      |sumRewards IT.action IT.reward a t τ - pullCount IT.action a t τ * actionMean κ id a e|}
  calc
    _ ≤ (P.map (fun ω ↦ (E ω, trajectory A R' ω))) S := by
        rw [Measure.map_apply (by fun_prop) (by measurability)]
        apply measure_mono
        intro ω ⟨t, ht, a, hpc, hle⟩
        rw [empMean] at hle
        exact ⟨a, t, ht, hpc, sqrt_two_mul_le hpc hle⟩
    _ = (P.map E ⊗ₘ condDistrib (trajectory A R') E P) S := by
        rw [← compProd_map_condDistrib (by fun_prop)]
    _ = ∫⁻ e, condDistrib (trajectory A R') E P e (Prod.mk e ⁻¹' S) ∂(P.map E) :=
        Measure.compProd_apply (by measurability)
    _ ≤ ∫⁻ e, ENNReal.ofReal (2 * Fintype.card (Fin K) * (n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [h.ae_IsAlgEnvSeq] with e he
        exact Bandits.prob_abs_sumRewards_sub_pullCount_mul_ge_le_of_Fintype hσ2 (hs e) he hδ
    _ = ENNReal.ofReal (2 * K * (n - 1) * δ) := by
      simp [Measure.map_apply h.measurable_E]

lemma prob_abs_empMean_bestAction_sub_actionMean_ge_le (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / (pullCount A (bestAction κ E ω) t ω)) ≤
        |empMean A R' (bestAction κ E ω) t ω - actionMean κ E (bestAction κ E ω) ω|}
      ≤ ENNReal.ofReal (2 * (n - 1) * δ) := by
  have := h.measurable_E
  have := h.measurable_A
  have := h.measurable_R
  let S := {(e, τ) | ∃ t < n, pullCount IT.action (bestAction κ id e) t τ ≠ 0 ∧
    √(2 * pullCount IT.action (bestAction κ id e) t τ * σ2 * Real.log (1 / δ)) ≤
      |sumRewards IT.action IT.reward (bestAction κ id e) t τ -
        pullCount IT.action (bestAction κ id e) t τ * actionMean κ id (bestAction κ id e) e|}
  calc
    _ ≤ (P.map (fun ω ↦ (E ω, trajectory A R' ω))) S := by
        rw [Measure.map_apply (by fun_prop) (by measurability)]
        apply measure_mono
        intro ω ⟨t, ht, hpc, hle⟩
        rw [empMean] at hle
        exact ⟨t, ht, hpc, sqrt_two_mul_le hpc hle⟩
    _ = (P.map E ⊗ₘ condDistrib (trajectory A R') E P) S := by
        rw [← compProd_map_condDistrib (by fun_prop)]
    _ = ∫⁻ e, condDistrib (trajectory A R') E P e (Prod.mk e ⁻¹' S) ∂(P.map E) :=
        Measure.compProd_apply (by measurability)
    _ ≤ ∫⁻ e, ENNReal.ofReal (2 * (n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [h.ae_IsAlgEnvSeq] with e he
        exact Bandits.prob_abs_sumRewards_sub_pullCount_mul_ge_le (ν := κ.sectR e) hσ2 (hs e _) he
          hδ
    _ = ENNReal.ofReal (2 * (n - 1) * δ) := by
      simp [Measure.map_apply h.measurable_E]

end HasSubgaussianMGF

end IsBayesAlgEnvSeq

section IsAlgEnvSeq

noncomputable
def bayesStationaryEnv (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R)
    [IsMarkovKernel κ] : Environment α (𝓔 × R) where
  feedback n :=
    let g : (Iic n → α × 𝓔 × R) × α → 𝓔 × α := fun (h, a) => ((h ⟨0, by simp⟩).2.1, a)
    (Kernel.deterministic (Prod.fst ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const _ Q) ⊗ₖ κ.swapLeft

variable [Nonempty α] [Nonempty 𝓔] [Nonempty R]
variable [StandardBorelSpace α] [StandardBorelSpace 𝓔] [StandardBorelSpace R]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × α) R} [IsMarkovKernel κ]
variable {alg : Algorithm α R} {A : ℕ → Ω → α} {R' : ℕ → Ω → 𝓔 × R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsAlgEnvSeq.isBayesAlgEnvSeq
    (h : IsAlgEnvSeq A R' (alg.prod_left 𝓔) (bayesStationaryEnv Q κ) P) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (R' 0 ω).1) A (fun n ω ↦ (R' n ω).2) P where
  measurable_E := (h.measurable_R 0).fst
  measurable_A := h.measurable_A
  measurable_R n := (h.measurable_R n).snd
  hasLaw_env := by
    apply HasCondDistrib.hasLaw_of_const
    simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
  hasCondDistrib_action_zero := by
    have hc : HasCondDistrib (fun ω ↦ (R' 0 ω).1) (A 0) (Kernel.const _ Q) P := by
      simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
    simpa [h.hasLaw_action_zero.map_eq, Algorithm.prod_left] using hc.swap_const
  hasCondDistrib_reward_zero :=
    h.hasCondDistrib_reward_zero.of_compProd.comp_right MeasurableEquiv.prodComm
  hasCondDistrib_action n := by
    let f : (Iic n → α × 𝓔 × R) → 𝓔 × (Iic n → α × R) :=
      fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
    have hc : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n)
        (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P :=
      h.hasCondDistrib_action n
    exact hc.comp_left (f := f)
  hasCondDistrib_reward n := by
    let f : (Iic n → α × 𝓔 × R) × α → (Iic n → α × R) × 𝓔 × α :=
      fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), (p.1 ⟨0, by simp⟩).2.1, p.2)
    have hc : HasCondDistrib (fun ω ↦ (R' (n + 1) ω).2)
        (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
        ((Kernel.prodMkLeft ((Iic n) → α × R) κ).comap f (by fun_prop)) P := by
      simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_reward n).snd
    exact hc.comp_left (by fun_prop)

end IsAlgEnvSeq

namespace IT

noncomputable
def bayesTrajMeasure (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) : Measure (ℕ → α × 𝓔 × R) :=
  trajMeasure (alg.prod_left 𝓔) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesTrajMeasure
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R) [IsMarkovKernel κ]
    (alg : Algorithm α R) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (ω 0).2.1) action (fun n ω ↦ (ω n).2.2)
       (bayesTrajMeasure Q κ alg) := (isAlgEnvSeq_trajMeasure _ _).isBayesAlgEnvSeq

noncomputable
def bayesTrajMeasurePosterior [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R) [IsMarkovKernel κ]
    (alg : Algorithm α R) (n : ℕ) : Kernel (Iic n → α × R) 𝓔 :=
  condDistrib (fun ω ↦ (ω 0).2.1) (IsAlgEnvSeq.hist action (fun n ω ↦ (ω n).2.2) n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

end IT

end Learning
