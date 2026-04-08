/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.Bandit.SumRewards
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.SequentialLearning.AlgorithmDensity

/-! # The Thompson Sampling Algorithm -/

open MeasureTheory ProbabilityTheory Finset Learning

open scoped NNReal

namespace Bandits

variable {K : ℕ}
variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]

namespace TS

noncomputable
def policy (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ) [IsMarkovKernel κ]
    (hK : 0 < K) (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (IT.bayesTrajMeasurePosterior Q κ (uniformAlgorithm hK) n).map (IsBayesAlgEnvSeq.bestAction κ id)

instance {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
    {hK : 0 < K} (n : ℕ) : IsMarkovKernel (policy Q κ hK n) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

noncomputable
def initialPolicy (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ)
    [IsMarkovKernel κ] (hK : 0 < K) : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (IsBayesAlgEnvSeq.bestAction κ id)

instance {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
    {hK : 0 < K} : IsProbabilityMeasure (initialPolicy Q κ hK) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

end TS

noncomputable
def tsAlgorithm (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ)
    [IsMarkovKernel κ] (hK : 0 < K) : Algorithm (Fin K) ℝ where
  policy := TS.policy Q κ hK
  p0 := TS.initialPolicy Q κ hK

namespace TS

section UCB

variable {Ω : Type*}
variable {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → ℝ}
variable {l u σ2 δ : ℝ}

noncomputable
def ucb (A : ℕ → Ω → Fin K) (R' : ℕ → Ω → ℝ) (l u σ2 δ : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  if pullCount A a n ω = 0 then u
  else max l (min u (empMean A R' a n ω + √(2 * σ2 * Real.log (1 / δ) / (pullCount A a n ω))))

@[fun_prop]
lemma measurable_ucb [MeasurableSpace Ω] {a : Fin K} {n : ℕ} (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R' t)) : Measurable (ucb A R' l u σ2 δ a n) :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

lemma ucb_mem_Icc (h : l ≤ u) {a : Fin K} {n : ℕ} {ω : Ω} :
    ucb A R' l u σ2 δ a n ω ∈ Set.Icc l u := by
  unfold ucb
  grind

noncomputable
def ucb' (n : ℕ) (h : Iic n → Fin K × ℝ) (l u σ2 δ : ℝ) (a : Fin K) : ℝ :=
  if pullCount' n h a = 0 then u
  else max l (min u (empMean' n h a + √(2 * σ2 * Real.log (1 / δ) / (pullCount' n h a))))

@[fun_prop]
lemma measurable_uncurry_ucb' {n : ℕ} :
    Measurable (fun p : (Iic n → Fin K × ℝ) × Fin K ↦ ucb' n p.1 l u σ2 δ p.2) :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

lemma ucb_succ_eq_ucb' {a : Fin K} {n : ℕ} {ω : Ω} :
    ucb A R' l u σ2 δ a (n + 1) ω = ucb' n (IsAlgEnvSeq.hist A R' n ω) l u σ2 δ a := by
  have hp : pullCount A a (n + 1) ω = pullCount' n (IsAlgEnvSeq.hist A R' n ω) a :=
    pullCount_add_one_eq_pullCount'
  have he : empMean A R' a (n + 1) ω = empMean' n (IsAlgEnvSeq.hist A R' n ω) a :=
    empMean_add_one_eq_empMean'
  rw [ucb, ucb', hp, he]

/-- Helper for `sum_ucb_sub_mean_le`. -/
private lemma sum_sqrt_le {ι : Type*} {c : ι → ℝ} (s : Finset ι) (hc : ∀ i, 0 ≤ c i) :
    ∑ i ∈ s, √(c i) ≤ √(#s * ∑ i ∈ s, c i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s hc (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, sum_const, nsmul_eq_mul] at h
  rwa [Real.sqrt_mul (by positivity), mul_comm]

/-- Helper for `sum_ucb_sub_mean_le`. -/
private lemma sum_inv_sqrt_le {n : ℕ} (h : 0 < n) : ∑ k ∈ range (n + 1), 1 / √k ≤ 2 * √n - 1 := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn : n = 0
    · rw [hn]
      simp
      norm_num
    · have hi := ih (Nat.pos_of_ne_zero hn)
      suffices 1 / √↑(n + 1) ≤ 2 * (√↑(n + 1) - √n) by linarith
      push_cast
      field_simp
      have : √(n + 1) * √(n + 1) = (n + 1) := Real.mul_self_sqrt (by positivity)
      have : √n * √n = n := Real.mul_self_sqrt (by positivity)
      nlinarith

/-- This bound could be improved slightly. -/
lemma sum_ucb_sub_mean_le {n : ℕ} {ω : Ω} (μ : Fin K → ℝ) (hμ : ∀ a, μ a ∈ Set.Icc l u) (hi : l ≤ u)
    (hc : ∀ s < n, pullCount A (A s ω) s ω ≠ 0 → |empMean A R' (A s ω) s ω - μ (A s ω)|
      < √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω))) :
    ∑ s ∈ range n, (ucb A R' l u σ2 δ (A s ω) s ω - μ (A s ω))
      ≤ (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by
  let S₀ := {s ∈ range n | pullCount A (A s ω) s ω = 0}
  let S₁ := {s ∈ range n | pullCount A (A s ω) s ω ≠ 0}
  have hu : S₀ ∪ S₁ = range n := filter_union_filter_not_eq _ _
  have hd : Disjoint S₀ S₁ := disjoint_filter_filter_not _ _ _
  rw [← hu, sum_union hd]
  gcongr
  · calc ∑ s ∈ S₀, (ucb A R' l u σ2 δ (A s ω) s ω - μ (A s ω))
        ≤ ∑ s ∈ S₀, (u - l) :=
          have (s : ℕ) : ucb A R' l u σ2 δ (A s ω) s ω ∈ Set.Icc l u := ucb_mem_Icc hi
          sum_le_sum (by grind)
      _ = ∑ s ∈ range n, if pullCount A (A s ω) s ω = 0 then (u - l) else 0 := by
          rw [sum_filter]
      _ = ∑ a, ∑ j ∈ range (pullCount A a n ω), if j = 0 then (u - l) else 0 :=
          sum_comp_pullCount (fun j => if j = 0 then (u - l) else 0) n ω
      _ ≤ ∑ a, (u - l) := by
          gcongr
          rw [sum_ite_eq']
          grind
      _ = (u - l) * K := by
          rw [Fin.sum_const, nsmul_eq_mul, mul_comm]
  · calc ∑ s ∈ S₁, (ucb A R' l u σ2 δ (A s ω) s ω - μ (A s ω))
          ≤ ∑ s ∈ S₁, 2 * √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω)) := by
            gcongr with s hs
            unfold ucb
            grind
        _ ≤ ∑ s ∈ range n, 2 * √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω)) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) * ∑ s ∈ range n, (1 / √(pullCount A (A s ω) s ω)) := by
            rw [mul_sum]
            congr with s
            rw [Real.sqrt_div' _ (by positivity)]
            ring
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) *
              ∑ a, ∑ j ∈ range (pullCount A a n ω), (1 / √j) := by
            rw [sum_comp_pullCount (fun j => 1 / √j)]
        _ ≤ 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * ∑ a, √(pullCount A a n ω)) := by
            rw [mul_sum _ _ 2]
            gcongr with a
            by_cases ha : pullCount A a n ω = 0
            · simp [ha]
            · have hi := sum_inv_sqrt_le (Nat.pos_of_ne_zero ha)
              rw [sum_range_succ] at hi
              have : 0 ≤ 1 / √(pullCount A a n ω) := by positivity
              linarith
        _ ≤ 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * √(K * ∑ a, (pullCount A a n ω))) := by
            gcongr
            have h := sum_sqrt_le Finset.univ (fun a => Nat.cast_nonneg (pullCount A a n ω))
            rw [Finset.card_fin] at h
            exact_mod_cast h
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * √(K * n)) := by
            congr
            exact sum_pullCount (ω := ω)
        _ = 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by
            ring_nf
            rw [← Real.sqrt_mul' _ (by positivity)]
            ring_nf

end UCB

end TS

end Bandits

namespace Learning.IsBayesAlgEnvSeq

variable {K : ℕ} [Nonempty (Fin K)]
variable {𝓔 Ω : Type*} [MeasurableSpace 𝓔] [MeasurableSpace Ω]
variable {Q : Measure 𝓔} {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ] {alg : Algorithm (Fin K) ℝ}
variable {E : Ω → 𝓔} {A : ℕ → Ω → (Fin K)} {R' : ℕ → Ω → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma prob_abs_sumRewards_sub_pullCount_mul_actionMean_ge_le
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) {σ2 : ℝ≥0}
    (hσ2 : 0 < σ2) (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ a, ∃ t < n, pullCount A a t ω ≠ 0 ∧
      √(2 * pullCount A a t ω * σ2 * Real.log (1 / δ)) ≤
        |sumRewards A R' a t ω - pullCount A a t ω * actionMean κ E a ω|}
      ≤ ENNReal.ofReal (2 * K * (n - 1) * δ) := by
  have := h.measurable_E
  have := h.measurable_A
  have := h.measurable_R
  let B e := {τ | ∃ a, ∃ t < n, pullCount IT.action a t τ ≠ 0 ∧
    √(2 * pullCount IT.action a t τ * σ2 * Real.log (1 / δ)) ≤
      |sumRewards IT.action IT.reward a t τ - pullCount IT.action a t τ * actionMean κ id a e|}
  calc P ((fun ω ↦ (E ω, trajectory A R' ω)) ⁻¹' {(e, τ) :  𝓔 × (ℕ → Fin K × ℝ) | τ ∈ B e})
    _ = (P.map (fun ω ↦ (E ω, trajectory A R' ω))) {(e, τ) :  𝓔 × (ℕ → Fin K × ℝ) | τ ∈ B e} :=
        (Measure.map_apply (by fun_prop) (by measurability)).symm
    _ = (P.map E ⊗ₘ condDistrib (trajectory A R') E P) {(e, τ) :  𝓔 × _ | τ ∈ B e} := by
        rw [← compProd_map_condDistrib (by fun_prop)]
    _ = ∫⁻ e, (condDistrib (trajectory A R') E P e) (B e) ∂(P.map E) := by
        rw [Measure.compProd_apply (by measurability)]
        rfl
    _ ≤ ∫⁻ e, ENNReal.ofReal (2 * (Fintype.card (Fin K)) * (n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [h.ae_IsAlgEnvSeq] with e he
        exact Bandits.prob_abs_sumRewards_sub_pullCount_mul_ge_le_of_Fintype hσ2 (hs e) he hδ
    _ = ENNReal.ofReal (2 * K * (n - 1) * δ) := by
        simp [lintegral_const, Measure.map_apply h.measurable_E]

lemma prob_abs_sumRewards_bestAction_sub_pullCount_mul_actionMean_ge_le
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
      √(2 * pullCount A (bestAction κ E ω) t ω * σ2 * Real.log (1 / δ)) ≤
        |sumRewards A R' (bestAction κ E ω) t ω -
          pullCount A (bestAction κ E ω) t ω * actionMean κ E (bestAction κ E ω) ω|}
      ≤ ENNReal.ofReal (2 * (n - 1) * δ) := by
  by_cases hn : n = 0
  · simp [hn]
  let B (a : Fin K) (t : ℕ) (e : 𝓔) := {ω : ℕ → (Fin K) × ℝ |
    pullCount IT.action a t ω ≠ 0 ∧
      √(2 * pullCount IT.action a t ω * σ2 * Real.log (1 / δ)) ≤
        |sumRewards IT.action IT.reward a t ω -
          pullCount IT.action a t ω * actionMean κ id a e|}
  have : {p : 𝓔 × (ℕ → (Fin K) × ℝ) |
      p.2 ∈ ⋃ t ∈ Finset.range n, B (bestAction κ id p.1) t p.1} =
    ⋃ a : Fin K, ((bestAction κ id ∘ Prod.fst) ⁻¹' {a} ∩
      ⋃ t ∈ Finset.range n,
        (fun p : 𝓔 × (ℕ → (Fin K) × ℝ) ↦ (pullCount IT.action a t p.2,
          sumRewards IT.action IT.reward a t p.2, actionMean κ Prod.fst a p)) ⁻¹'
          {u : ℕ × ℝ × ℝ | u.1 ≠ 0 ∧
            √(2 * u.1 * σ2 * Real.log (1 / δ)) ≤ |u.2.1 - u.1 * u.2.2|}) := by
    ext p
    simp only [B, actionMean, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Finset.mem_range]
    constructor
    · intro ⟨t, ht, hm⟩
      exact ⟨bestAction κ id p.1, rfl, t, ht, hm⟩
    · rintro ⟨a, ha, t, ht, hm⟩
      exact ⟨t, ht, ha ▸ hm⟩
  calc P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
        √(2 * pullCount A (bestAction κ E ω) t ω * σ2 * Real.log (1 / δ)) ≤
          |sumRewards A R' (bestAction κ E ω) t ω -
            pullCount A (bestAction κ E ω) t ω * actionMean κ E (bestAction κ E ω) ω|}
    _ = P ((fun ω ↦ (E ω, trajectory A R' ω)) ⁻¹'
          {p | p.2 ∈ ⋃ t ∈ Finset.range n, B (bestAction κ id p.1) t p.1}) := by
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Finset.mem_range, Set.mem_preimage,
          Set.mem_iUnion, B, actionMean, exists_prop]
        rfl
    _ = (P.map (fun ω ↦ (E ω, trajectory A R' ω)))
          {p | p.2 ∈ ⋃ t ∈ Finset.range n, B (bestAction κ id p.1) t p.1} :=
        (Measure.map_apply (h.measurable_E.prodMk
          (measurable_trajectory h.measurable_A h.measurable_R)) (by measurability)).symm
    _ = (P.map E ⊗ₘ condDistrib (trajectory A R') E P)
          {p | p.2 ∈ ⋃ t ∈ Finset.range n, B (bestAction κ id p.1) t p.1} := by
        rw [(compProd_map_condDistrib
          (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable).symm]
    _ = ∫⁻ e, (condDistrib (trajectory A R') E P e)
          (⋃ t ∈ Finset.range n, B (bestAction κ id e) t e) ∂(P.map E) := by
        rw [Measure.compProd_apply (by measurability)]
        rfl
    _ ≤ ∫⁻ _, ENNReal.ofReal (2 * (n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [ae_IsAlgEnvSeq h] with e he
        have : {ω | ∃ t < n, ω ∈ B (bestAction κ id e) t e} =
            ⋃ t ∈ Finset.range n, B (bestAction κ id e) t e := by
          ext ω
          simp [Finset.mem_range]
        simp only [← this, B, Set.mem_setOf_eq]
        exact Bandits.prob_abs_sumRewards_sub_pullCount_mul_ge_le hσ2
          (by simp only [Kernel.sectR_apply]; exact hs e _) he hδ
    _ = ENNReal.ofReal (2 * (n - 1) * δ) := by
        rw [lintegral_const, Measure.map_apply h.measurable_E .univ]
        simp [measure_univ]

omit [Nonempty (Fin K)] [MeasurableSpace 𝓔] [MeasurableSpace Ω] in
private lemma abs_sumRewards_sub_pullCount_mul_ge {a : Fin K} {n : ℕ} {ω : Ω}
    {μ σ2 δ : ℝ} (hpc : pullCount A a n ω ≠ 0)
    (h : √(2 * σ2 * Real.log (1 / δ) / pullCount A a n ω) ≤
      |empMean A R' a n ω - μ|) :
    √(2 * pullCount A a n ω * σ2 * Real.log (1 / δ)) ≤
      |sumRewards A R' a n ω - pullCount A a n ω * μ| := by
  have hk : (0 : ℝ) < pullCount A a n ω :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hpc)
  simp only [empMean] at h
  calc √(2 * pullCount A a n ω * σ2 * Real.log (1 / δ))
    _ ≤ √(2 * σ2 * Real.log (1 / δ) / pullCount A a n ω) * pullCount A a n ω := by
      by_cases hc : 0 ≤ 2 * σ2 * Real.log (1 / δ)
      · apply le_of_eq
        have : 2 * pullCount A a n ω * σ2 * Real.log (1 / δ) =
            2 * σ2 * Real.log (1 / δ) / pullCount A a n ω * pullCount A a n ω ^ 2 := by
          field_simp
        rw [this, Real.sqrt_mul (div_nonneg hc hk.le), Real.sqrt_sq hk.le]
      · rw [Real.sqrt_eq_zero_of_nonpos (by push_neg at hc; nlinarith)]
        exact mul_nonneg (Real.sqrt_nonneg _) hk.le
    _ ≤ |sumRewards A R' a n ω / pullCount A a n ω - μ| * pullCount A a n ω :=
      mul_le_mul_of_nonneg_right h hk.le
    _ = |sumRewards A R' a n ω - pullCount A a n ω * μ| := by
      have h_div : sumRewards A R' a n ω / ↑(pullCount A a n ω) - μ =
          (sumRewards A R' a n ω - pullCount A a n ω * μ) / pullCount A a n ω := by
        field_simp
      rw [h_div, abs_div, abs_of_pos hk, div_mul_cancel₀ _ (ne_of_gt hk)]

lemma prob_abs_empMean_sub_actionMean_ge_le
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) {σ2 : ℝ≥0}
    (hσ2 : 0 < σ2) (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, ∃ a, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / pullCount A a t ω) ≤
        |empMean A R' a t ω - actionMean κ E a ω|}
      ≤ ENNReal.ofReal (2 * K * (n - 1) * δ) :=
  calc _
    _ ≤ P {ω | ∃ a, ∃ t < n, pullCount A a t ω ≠ 0 ∧
          √(2 * pullCount A a t ω * σ2 * Real.log (1 / δ)) ≤
            |sumRewards A R' a t ω - pullCount A a t ω * actionMean κ E a ω|} := by
        apply measure_mono
        intro ω ⟨t, ht, a, hpc, hle⟩
        exact ⟨a, t, ht, hpc, abs_sumRewards_sub_pullCount_mul_ge hpc hle⟩
    _ ≤ _ := h.prob_abs_sumRewards_sub_pullCount_mul_actionMean_ge_le hσ2 hs hδ n

lemma prob_abs_empMean_bestAction_sub_actionMean_ge_le
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / (pullCount A (bestAction κ E ω) t ω : ℝ)) ≤
        |empMean A R' (bestAction κ E ω) t ω - actionMean κ E (bestAction κ E ω) ω|}
      ≤ ENNReal.ofReal (2 * (n - 1) * δ) :=
  calc _
    _ ≤ P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
          √(2 * pullCount A (bestAction κ E ω) t ω * σ2 * Real.log (1 / δ)) ≤
            |sumRewards A R' (bestAction κ E ω) t ω -
              pullCount A (bestAction κ E ω) t ω *
                actionMean κ E (bestAction κ E ω) ω|} := by
        apply measure_mono
        intro ω ⟨t, ht, hpc, hle⟩
        exact ⟨t, ht, hpc, abs_sumRewards_sub_pullCount_mul_ge hpc hle⟩
    _ ≤ _ :=
        h.prob_abs_sumRewards_bestAction_sub_pullCount_mul_actionMean_ge_le
          hσ2 hs hδ n

end Learning.IsBayesAlgEnvSeq

namespace Bandits.TS

variable {K : ℕ}
variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable (hK : 0 < K)
variable {Ω : Type*} [MeasurableSpace Ω]
variable (E : Ω → 𝓔) (A : ℕ → Ω → (Fin K)) (R' : ℕ → Ω → ℝ)
variable (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ) [IsMarkovKernel κ]
variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma ts_identity [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P) (t : ℕ) :
    condDistrib (A (t + 1)) (IsAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
    condDistrib (IsBayesAlgEnvSeq.bestAction κ E) (IsAlgEnvSeq.hist A R' t) P := by
  have h_ba_comp : IsBayesAlgEnvSeq.bestAction κ E
      = IsBayesAlgEnvSeq.bestAction κ id ∘ E := rfl
  rw [h_ba_comp]
  have hm := IsBayesAlgEnvSeq.measurable_bestAction (κ := κ) measurable_id
  have h_comp := condDistrib_comp (mβ := MeasurableSpace.pi) (μ := P)
    (IsAlgEnvSeq.hist A R' t) h.measurable_E.aemeasurable hm
  have h_map : (condDistrib E (IsAlgEnvSeq.hist A R' t) P).map
      (IsBayesAlgEnvSeq.bestAction κ id) =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
      (IT.bayesTrajMeasurePosterior Q κ (uniformAlgorithm hK) t).map
        (IsBayesAlgEnvSeq.bestAction κ id) := by
    filter_upwards [(h.hasCondDistrib_env_hist
      (IT.isBayesAlgEnvSeq_bayesTrajMeasure Q κ (uniformAlgorithm hK))
      (absolutelyContinuous_uniformAlgorithm hK _) t).condDistrib_eq]
      with x hx
    simp only [Kernel.map_apply _ hm, IT.bayesTrajMeasurePosterior, hx]
  exact (h.hasCondDistrib_action' t).condDistrib_eq.trans (h_comp.trans h_map).symm

lemma bayesRegret_le_of_delta [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {l u : ℝ} (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    P[IsBayesAlgEnvSeq.regret κ E A n]
      ≤ (u - l) * ↑K + 2 * (↑K + 1) * (u - l) * n ^ 2 * δ +
        4 * √(2 * ↑σ2 * Real.log (1 / δ) * ↑K * ↑n) := by
  have ⟨h1, h2⟩ := hm (Classical.arbitrary _) (Classical.arbitrary _)
  have hlo : l ≤ u := h1.trans h2
  let bestArm := IsBayesAlgEnvSeq.bestAction κ E
  let armMean := IsBayesAlgEnvSeq.actionMean κ E
  let uc := ucb A R' l u (↑σ2) δ
  set Eδ : Set Ω := {ω | ∀ s < n, ∀ a, pullCount A a s ω ≠ 0 →
    |empMean A R' a s ω - armMean a ω|
      < √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ))}
  set Fδ : Set Ω := {ω | ∀ s < n, pullCount A (bestArm ω) s ω ≠ 0 →
    |empMean A R' (bestArm ω) s ω - armMean (bestArm ω) ω|
      < √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A (bestArm ω) s ω : ℝ))}
  have hm_ucb : ∀ a t, Measurable (ucb A R' l u (↑σ2) δ a t) :=
    fun _ _ ↦ measurable_ucb h.measurable_A h.measurable_R
  have hm_arm : ∀ a, Measurable (IsBayesAlgEnvSeq.actionMean κ E a) :=
    fun a ↦ IsBayesAlgEnvSeq.measurable_actionMean (a := a) h.measurable_E
  have hm_best : Measurable (IsBayesAlgEnvSeq.bestAction κ E) :=
    IsBayesAlgEnvSeq.measurable_bestAction h.measurable_E
  have h_first_bound : ∀ ω,
      |∑ s ∈ range n, (armMean (bestArm ω) ω - uc (bestArm ω) s ω)|
        ≤ n * (u - l) := fun ω ↦
    calc |∑ s ∈ range n, (armMean (bestArm ω) ω - uc (bestArm ω) s ω)|
        ≤ ∑ s ∈ range n, |armMean (bestArm ω) ω - uc (bestArm ω) s ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (u - l) := by
          gcongr with s _
          exact abs_sub_le_of_le_of_le (hm _ _).1 (hm _ _).2
            ((ucb_mem_Icc hlo).1)
            (ucb_mem_Icc hlo).2
      _ = ↑n * (u - l) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_second_bound : ∀ ω,
      |∑ s ∈ range n, (uc (A s ω) s ω - armMean (A s ω) ω)|
        ≤ n * (u - l) := fun ω ↦
    calc |∑ s ∈ range n, (uc (A s ω) s ω - armMean (A s ω) ω)|
        ≤ ∑ s ∈ range n, |uc (A s ω) s ω - armMean (A s ω) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (u - l) := by
          gcongr with s _
          exact abs_sub_le_of_le_of_le (ucb_mem_Icc hlo).1
            (ucb_mem_Icc hlo).2 (hm _ _).1 (hm _ _).2
      _ = ↑n * (u - l) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_int_sum1 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (armMean (bestArm ω) ω - uc (bestArm ω) s ω)) P := by
    apply Integrable.of_bound (C := ↑n * (u - l))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin hm_arm hm_best).sub
          (measurable_apply_fin (fun a ↦ hm_ucb a s) hm_best)).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_first_bound ω
  have h_int_sum2 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (uc (A s ω) s ω - armMean (A s ω) ω)) P := by
    apply Integrable.of_bound (C := ↑n * (u - l))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin (fun a ↦ hm_ucb a s) (h.measurable_A s)).sub
          (measurable_apply_fin hm_arm (h.measurable_A s))).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_second_bound ω
  have h_swap :
      P[IsBayesAlgEnvSeq.regret κ E A n] =
      P[fun ω ↦ ∑ s ∈ range n,
        (armMean (bestArm ω) ω - uc (bestArm ω) s ω)] +
      P[fun ω ↦ ∑ s ∈ range n,
        (uc (A s ω) s ω - armMean (A s ω) ω)] := by
    have h_int_ucb : ∀ s {f : Ω → Fin K}, Measurable f →
        Integrable (fun ω ↦ uc (f ω) s ω) P := fun s {_} hf ↦
      ⟨(measurable_apply_fin (fun a ↦ hm_ucb a s) hf).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact abs_le_max_abs_abs (ucb_mem_Icc hlo).1
            (ucb_mem_Icc hlo).2)⟩
    have h_int_ucb_sub : ∀ s, Integrable (fun ω ↦ uc (A s ω) s ω - uc (bestArm ω) s ω) P :=
      fun s ↦ (h_int_ucb s (h.measurable_A s)).sub (h_int_ucb s hm_best)
    have h_ucb_zero : ∀ a (ω : Ω), ucb A R' l u (↑σ2) δ a 0 ω = u := by
      intro a ω; unfold ucb; simp [pullCount_zero]
    have h_ucb_swap : ∀ s, ∫ ω, (uc (A s ω) s ω - uc (bestArm ω) s ω) ∂P = 0 := by
      intro s
      cases s with
      | zero =>
        have : ∀ ω, uc (A 0 ω) 0 ω - uc (bestArm ω) 0 ω = 0 := fun ω ↦ by
          change ucb A R' l u (↑σ2) δ _ 0 ω - ucb A R' l u (↑σ2) δ _ 0 ω = 0
          simp [h_ucb_zero]
        exact (integral_congr_ae (ae_of_all _ this)).trans (integral_zero _ _)
      | succ t =>
        have hts := ts_identity hK E A R' Q κ P h t
        have h_map_eq : P.map (fun ω ↦ (IsAlgEnvSeq.hist A R' t ω, A (t + 1) ω)) =
            P.map (fun ω ↦ (IsAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestAction κ E ω)) := by
          rw [← compProd_map_condDistrib (hY := (h.measurable_A (t + 1)).aemeasurable),
              ← compProd_map_condDistrib (hY := hm_best.aemeasurable)]
          exact Measure.compProd_congr hts
        have h_int_eq : ∀ (f : (Iic t → Fin K × ℝ) × Fin K → ℝ), Measurable f →
            ∫ ω, f (IsAlgEnvSeq.hist A R' t ω, A (t + 1) ω) ∂P =
            ∫ ω, f (IsAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestAction κ E ω) ∂P := by
          intro f hf
          have hm_hist := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t
          rw [← integral_map
                (hm_hist.prodMk (h.measurable_A (t + 1))).aemeasurable
                hf.aestronglyMeasurable,
              ← integral_map
                (hm_hist.prodMk hm_best).aemeasurable
                hf.aestronglyMeasurable,
              h_map_eq]
        let g : (Iic t → Fin K × ℝ) × Fin K → ℝ :=
          fun p ↦ ucb' t p.1 l u (↑σ2) δ p.2
        have hg_eq : ∀ a (ω : Ω), ucb A R' l u (↑σ2) δ a (t + 1) ω =
            g (IsAlgEnvSeq.hist A R' t ω, a) := fun _ _ ↦ ucb_succ_eq_ucb'
        have hg_meas : Measurable g := measurable_uncurry_ucb'
        rw [show (fun ω ↦ uc (A (t + 1) ω) (t + 1) ω -
            uc (bestArm ω) (t + 1) ω) =
            fun ω ↦ (fun ω ↦ uc (A (t + 1) ω) (t + 1) ω) ω -
              (fun ω ↦ uc (bestArm ω) (t + 1) ω) ω from rfl,
          integral_sub (h_int_ucb (t + 1) (h.measurable_A (t + 1)))
            (h_int_ucb (t + 1) hm_best),
          funext fun ω ↦ hg_eq _ _, funext fun ω ↦ hg_eq _ _,
          h_int_eq g hg_meas, sub_self]
    have h_ucb_sum_zero : ∫ ω, ∑ s ∈ range n,
        (uc (A s ω) s ω - uc (bestArm ω) s ω) ∂P = 0 := by
      rw [integral_finset_sum _ (fun s _ ↦ h_int_ucb_sub s)]
      exact Finset.sum_eq_zero fun s _ ↦ h_ucb_swap s
    have h_int_gap : Integrable (fun ω ↦ IsBayesAlgEnvSeq.regret κ E A n ω) P :=
      IsBayesAlgEnvSeq.integrable_regret h.measurable_E (h.measurable_A) hm
    simp_rw [IsBayesAlgEnvSeq.regret_eq_sum_gap, IsBayesAlgEnvSeq.gap_eq_sub] at h_int_gap ⊢
    have h_pw : ∀ ω, (∑ s ∈ range n, (armMean (bestArm ω) ω - uc (bestArm ω) s ω)) +
        (∑ s ∈ range n, (uc (A s ω) s ω - armMean (A s ω) ω)) =
        (∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω)) +
        (∑ s ∈ range n, (uc (A s ω) s ω - uc (bestArm ω) s ω)) := by
      intro ω
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intros; ring
    have h_int_ucb_swap : Integrable
        (fun ω ↦ ∑ s ∈ range n, (uc (A s ω) s ω - uc (bestArm ω) s ω)) P :=
      integrable_finset_sum _ fun s _ ↦ h_int_ucb_sub s
    calc ∫ ω, ∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω) ∂P
        = ∫ ω, ((∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω)) +
            (∑ s ∈ range n, (uc (A s ω) s ω - uc (bestArm ω) s ω))) ∂P := by
          rw [integral_add h_int_gap h_int_ucb_swap, h_ucb_sum_zero, add_zero]
      _ = ∫ ω, ((∑ s ∈ range n, (armMean (bestArm ω) ω - uc (bestArm ω) s ω)) +
            (∑ s ∈ range n, (uc (A s ω) s ω - armMean (A s ω) ω))) ∂P := by
          congr 1; ext ω; linarith [h_pw ω]
      _ = _ := integral_add h_int_sum1 h_int_sum2
  have h_first_Fδ : ∀ ω ∈ Fδ,
      ∑ s ∈ range n, (armMean (bestArm ω) ω - uc (bestArm ω) s ω)
        ≤ 0 := by
    intro ω hω
    apply Finset.sum_nonpos
    intro s hs
    have : armMean (bestArm ω) ω ≤ uc (bestArm ω) s ω := by
      simp only [armMean, uc]; unfold ucb
      split_ifs with h0
      · exact (hm (E ω) (bestArm ω)).2
      · have := abs_lt.mp ((hω s (mem_range.mp hs)) h0)
        exact le_max_of_le_right (le_min (hm (E ω) (bestArm ω)).2 (by linarith))
    linarith
  have h_second_Eδ : ∀ ω ∈ Eδ,
      ∑ s ∈ range n, (uc (A s ω) s ω - armMean (A s ω) ω)
        ≤ (u - l) * ↑K + 4 * √(2 * ↑σ2 * Real.log (1 / δ) * ↑K * ↑n) := by
    intro ω hω
    exact sum_ucb_sub_mean_le (fun a ↦ armMean a ω) (hm (E ω)) hlo
      (fun s hs hpc => hω s hs (A s ω) hpc)
  have h_prob : P Eδᶜ ≤ ENNReal.ofReal (2 * K * n * δ) := by
    have : Eδᶜ = {ω | ∃ s < n, ∃ a, pullCount A a s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
        |empMean A R' a s ω - armMean a ω|} := by
      ext ω; simp only [Eδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push_neg; rfl
    rw [this]
    exact (h.prob_abs_empMean_sub_actionMean_ge_le hσ2 hs hδ n).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) K]))
  have hm_emp : ∀ a s, Measurable (fun ω ↦ empMean A R' a s ω) :=
    fun a s ↦ measurable_empMean (fun n ↦ h.measurable_A n) (fun n ↦ h.measurable_R n) a s
  have hm_pc : ∀ a s, Measurable (fun ω ↦ (pullCount A a s ω : ℝ)) :=
    fun a s ↦ measurable_from_top.comp (measurable_pullCount (fun n ↦ h.measurable_A n) a s)
  have h_arm_meas : ∀ s a, MeasurableSet {ω : Ω | pullCount A a s ω ≠ 0 →
      |empMean A R' a s ω - armMean a ω|
        < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} := by
    intro s a
    have : {ω : Ω | pullCount A a s ω ≠ 0 →
        |empMean A R' a s ω - armMean a ω|
          < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} =
        {ω | (pullCount A a s ω : ℝ) = 0} ∪ {ω |
          |empMean A R' a s ω - armMean a ω|
            < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, Nat.cast_eq_zero]; tauto
    rw [this]
    exact .union (hm_pc a s (measurableSet_singleton _))
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have hEδ_meas : MeasurableSet Eδ := by
    simp only [Eδ, Set.setOf_forall]
    exact .iInter fun s ↦ .iInter fun _ ↦ .iInter fun a ↦ h_arm_meas s a
  have hFδ_meas : MeasurableSet Fδ := by
    simp only [Fδ, Set.setOf_forall]
    refine .iInter fun s ↦ .iInter fun _ ↦ ?_
    convert MeasurableSet.iUnion fun a ↦
      (hm_best (measurableSet_singleton a)).inter (h_arm_meas s a) using 1
    ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩
  have h_prob_F : P Fδᶜ ≤ ENNReal.ofReal (2 * ↑n * δ) := by
    have : Fδᶜ = {ω | ∃ s < n, pullCount A (bestArm ω) s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A (bestArm ω) s ω : ℝ)) ≤
          |empMean A R' (bestArm ω) s ω - armMean (bestArm ω) ω|} := by
      ext ω; simp only [Fδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push_neg; rfl
    rw [this]
    exact (h.prob_abs_empMean_bestAction_sub_actionMean_ge_le hσ2 hs hδ n).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [hδ.le]))
  rw [h_swap]
  set f1 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (armMean (bestArm ω) ω - uc (bestArm ω) s ω)
  set f2 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (uc (A s ω) s ω - armMean (A s ω) ω)
  set B := (u - l) * ↑K + 4 * √(2 * ↑σ2 * Real.log (1 / δ) * ↑K * ↑n)
  have h1g : ∫ ω in Fδ, f1 ω ∂P ≤ 0 :=
    setIntegral_nonpos hFδ_meas fun ω hω ↦ h_first_Fδ ω hω
  have h1b : ∫ ω in Fδᶜ, f1 ω ∂P ≤ ↑n * (u - l) * P.real Fδᶜ := by
    have := setIntegral_mono_on (hf := h_int_sum1.integrableOn) (hg := integrableOn_const)
      hFδ_meas.compl fun ω _ ↦ (abs_le.mp (h_first_bound ω)).2
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have h2g : ∫ ω in Eδ, f2 ω ∂P ≤ B := by
    have hB : 0 ≤ B := by have : 0 ≤ u - l := sub_nonneg.mpr hlo; positivity
    have := setIntegral_mono_on (hf := h_int_sum2.integrableOn)
      (hg := integrableOn_const) hEδ_meas
      fun ω hω ↦ h_second_Eδ ω hω
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact le_trans this (mul_le_of_le_one_right hB measureReal_le_one)
  have h2b : ∫ ω in Eδᶜ, f2 ω ∂P ≤ ↑n * (u - l) * P.real Eδᶜ := by
    have := setIntegral_mono_on (hf := h_int_sum2.integrableOn) (hg := integrableOn_const)
      hEδ_meas.compl fun ω _ ↦ (abs_le.mp (h_second_bound ω)).2
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hPF : P.real Fδᶜ ≤ 2 * ↑n * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h_prob_F
  have hPE : P.real Eδᶜ ≤ 2 * ↑K * ↑n * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h_prob
  rw [(integral_add_compl hFδ_meas h_int_sum1).symm,
    (integral_add_compl hEδ_meas h_int_sum2).symm]
  have : 0 ≤ ↑n * (u - l) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hPF this,
    mul_le_mul_of_nonneg_left hPE this,
    measureReal_nonneg (μ := P) (s := Fδᶜ),
    measureReal_nonneg (μ := P) (s := Eδᶜ)]

lemma bayesRegret_le [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {lo hi : ℝ} (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc lo hi)) (t : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A t]
      ≤ (3 * K + 2) * (hi - lo) + 8 * √(σ2 * K * t * Real.log t) := by
  have ⟨h1, h2⟩ := hm (Classical.arbitrary _) (Classical.arbitrary _)
  have hlo : lo ≤ hi := h1.trans h2
  by_cases ht : t = 0
  · simp [ht, IsBayesAlgEnvSeq.regret, Bandits.regret]
    nlinarith [sub_nonneg.mpr hlo, Nat.cast_pos (α := ℝ).mpr hK,
      Real.sqrt_nonneg (↑σ2 * ↑K * (0 : ℝ) * Real.log (0 : ℝ))]
  by_cases ht1_eq : t = 1
  · subst ht1_eq
    simp only [Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
    calc P[IsBayesAlgEnvSeq.regret κ E A 1]
        ≤ hi - lo := by
          rw [IsBayesAlgEnvSeq.regret_eq_sum_gap']
          simp only [Finset.range_one, Finset.sum_singleton]
          exact (integral_mono_of_nonneg
            (ae_of_all _ fun ω ↦ IsBayesAlgEnvSeq.gap_nonneg_of_le (fun e a ↦ (hm e a).2))
            (integrable_const _)
            (ae_of_all _ fun ω ↦ IsBayesAlgEnvSeq.gap_le_of_mem_Icc hm)).trans (by simp)
      _ ≤ (3 * ↑K + 2) * (hi - lo) := by
          nlinarith [Nat.one_le_cast (α := ℝ).mpr (Nat.one_le_of_lt hK),
            sub_nonneg.mpr hlo]
  -- For t ≥ 2, we have δ = 1/t² < 1
  · have ht2 : 2 ≤ t := by omega
    have htpos : (0 : ℝ) < t := by positivity
    have _ht1 : (1 : ℝ) ≤ t := by exact_mod_cast Nat.pos_of_ne_zero ht
    have hδ : (0 : ℝ) < 1 / (t : ℝ) ^ 2 := by positivity
    -- First term: (hi-lo)*K + 2*(K+1)*(hi-lo)*t²*(1/t²) = (3K+2)*(hi-lo)
    have h_first : (hi - lo) * ↑K + 2 * (↑K + 1) * (hi - lo) * ↑t ^ 2 * (1 / (↑t) ^ 2)
        = (3 * ↑K + 2) * (hi - lo) := by
      field_simp; ring
    -- Second term simplification: log(1/(1/t²)) = log(t²) = 2 log(t)
    have h_log : Real.log (1 / (1 / (↑t : ℝ) ^ 2)) = 2 * Real.log ↑t := by
      rw [one_div_one_div, Real.log_pow]; norm_cast
    calc P[IsBayesAlgEnvSeq.regret κ E A t]
        ≤ (hi - lo) * ↑K + 2 * (↑K + 1) * (hi - lo) * ↑t ^ 2 * (1 / (↑t) ^ 2)
          + 4 * √(2 * ↑σ2 * Real.log (1 / (1 / (↑t) ^ 2)) * ↑K * ↑t) :=
          bayesRegret_le_of_delta (hK := hK) (E := E) (A := A) (R' := R') (Q := Q)
            (κ := κ) (P := P) h hσ2 hs hm t (1 / (↑t) ^ 2) hδ
      _ = (3 * ↑K + 2) * (hi - lo) + 8 * √(↑σ2 * ↑K * ↑t * Real.log ↑t) := by
          rw [h_first, h_log]; congr 1
          rw [show (2 : ℝ) * ↑σ2 * (2 * Real.log ↑t) * ↑K * ↑t =
            (2 : ℝ) ^ 2 * (↑σ2 * ↑K * ↑t * Real.log ↑t) from by ring,
            Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
          ring

end Bandits.TS
