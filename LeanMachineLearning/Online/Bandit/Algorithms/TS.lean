/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithms.Uniform
public import LeanMachineLearning.SequentialLearning.AlgorithmDensity

/-! # The Thompson Sampling Algorithm -/

@[expose] public section

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

variable (hK : 0 < K)
variable {Ω : Type*}
variable {E : Ω → 𝓔} {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → ℝ}
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]

lemma hasCondDistrib_action [Nonempty (Fin K)] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n)
      (condDistrib (IsBayesAlgEnvSeq.bestAction κ E) (IsAlgEnvSeq.hist A R' n) P) P where
  aemeasurable_fst := (h.measurable_A (n + 1)).aemeasurable
  aemeasurable_snd := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  condDistrib_eq := by
    have hm : Measurable (IsBayesAlgEnvSeq.bestAction κ id) := by fun_prop
    calc
      _ =ᵐ[P.map (IsAlgEnvSeq.hist A R' n)]
          (IT.bayesTrajMeasurePosterior Q κ (uniformAlgorithm hK) n).map
            (IsBayesAlgEnvSeq.bestAction κ id) :=
          (h.hasCondDistrib_action' n).condDistrib_eq
      _ =ᵐ[P.map (IsAlgEnvSeq.hist A R' n)]
          (condDistrib E (IsAlgEnvSeq.hist A R' n) P).map
            (IsBayesAlgEnvSeq.bestAction κ id) := by
          filter_upwards [(h.hasCondDistrib_env_hist
            (IT.isBayesAlgEnvSeq_bayesTrajMeasure Q κ (uniformAlgorithm hK))
            (absolutelyContinuous_uniformAlgorithm hK _) n).condDistrib_eq] with _ hc
          simp_rw [Kernel.map_apply _ hm, IT.bayesTrajMeasurePosterior, hc]
      _ =ᵐ[P.map (IsAlgEnvSeq.hist A R' n)]
          condDistrib (IsBayesAlgEnvSeq.bestAction κ E) (IsAlgEnvSeq.hist A R' n) P :=
          (condDistrib_comp (IsAlgEnvSeq.hist A R' n) h.measurable_E.aemeasurable hm).symm

variable {l u σ2 δ : ℝ}

section UCB

noncomputable
def ucb (A : ℕ → Ω → Fin K) (R' : ℕ → Ω → ℝ) (l u σ2 δ : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  if pullCount A a n ω = 0 then u
  else max l (min u (empMean A R' a n ω + √(2 * σ2 * Real.log (1 / δ) / (pullCount A a n ω))))

@[simp]
lemma ucb_zero {a : Fin K} {ω : Ω} : ucb A R' l u σ2 δ a 0 ω = u := by
  simp [ucb]

lemma ucb_mem_Icc (h : l ≤ u) {a : Fin K} {n : ℕ} {ω : Ω} :
    ucb A R' l u σ2 δ a n ω ∈ Set.Icc l u := by
  unfold ucb
  grind

@[fun_prop]
lemma measurable_ucb [MeasurableSpace Ω] {a : Fin K} {n : ℕ} (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R' t)) : Measurable (ucb A R' l u σ2 δ a n) :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

@[fun_prop]
lemma measurable_uncurry_ucb_comp [MeasurableSpace Ω] (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R' t)) {f : Ω → Fin K} (hf : Measurable f) {g : Ω → ℕ}
    (hg : Measurable g) : Measurable (fun ω ↦ ucb A R' l u σ2 δ (f ω) (g ω) ω) := by
  change Measurable ((fun aω ↦ ucb A R' l u σ2 δ aω.1 (g aω.2) aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  apply measurable_from_prod_countable_right
  intro a
  change Measurable ((fun tω ↦ ucb A R' l u σ2 δ a tω.1 tω.2) ∘ fun ω ↦ (g ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun _ ↦ measurable_ucb hA hR)

@[fun_prop]
lemma integrable_uncurry_ucb_comp [MeasurableSpace Ω] (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R' t)) {f : Ω → Fin K} (hf : Measurable f) {g : Ω → ℕ}
    (hg : Measurable g) {P : Measure Ω} [IsFiniteMeasure P] :
    Integrable (fun ω ↦ ucb A R' l u σ2 δ (f ω) (g ω) ω) P := by
  refine ⟨(measurable_uncurry_ucb_comp hA hR hf hg).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := max |l| |u|)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
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

section IntegralRegret

variable [Nonempty (Fin K)]
variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_ucb_action_eq_integral_ucb_bestAction
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P) (n : ℕ) :
    P[fun ω ↦ ucb A R' l u σ2 δ (A n ω) n ω] =
      P[fun ω ↦ ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) n ω] := by
  have := h.measurable_A
  have := h.measurable_E
  have := h.measurable_R
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let u' (ha : (Iic n → Fin K × ℝ) × Fin K) := ucb' n ha.1 l u σ2 δ ha.2
  calc
    _  = P[fun ω ↦ u' (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)] := by
        simp_rw [u', ucb_succ_eq_ucb']
    _ = ∫ ha, u' ha ∂P.map (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) := by
        rw [← integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ ha, u' ha ∂P.map
          (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, IsBayesAlgEnvSeq.bestAction κ E ω)) := by
        rw [← compProd_map_condDistrib (by fun_prop), ← compProd_map_condDistrib (by fun_prop),
            Measure.compProd_congr (hasCondDistrib_action hK h n).condDistrib_eq]
    _ = P[fun ω ↦ ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) (n + 1) ω] := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        simp_rw [u', ucb_succ_eq_ucb']

lemma integral_regret_eq_add (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (n : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A n] =
      P[fun ω ↦ ∑ t ∈ range n,
        (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
          ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) t ω)] +
      P[fun ω ↦ ∑ t ∈ range n,
        (ucb A R' l u σ2 δ (A t ω) t ω - IsBayesAlgEnvSeq.actionMean κ E (A t ω) ω)] := by
  have hua (t : ℕ) : Integrable (fun ω ↦ ucb A R' l u σ2 δ (A t ω) t ω) P :=
    integrable_uncurry_ucb_comp h.measurable_A h.measurable_R (h.measurable_A t) measurable_const
  have hub (t : ℕ) :
      Integrable (fun ω ↦ ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) t ω) P :=
    integrable_uncurry_ucb_comp h.measurable_A h.measurable_R
      (IsBayesAlgEnvSeq.measurable_bestAction h.measurable_E) measurable_const
  have haa (t : ℕ) : Integrable (fun ω ↦ IsBayesAlgEnvSeq.actionMean κ E (A t ω) ω) P :=
    IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_E (h.measurable_A t) hm
  have hab :
    Integrable (fun ω ↦ IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω) P :=
      IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_E
        (IsBayesAlgEnvSeq.measurable_bestAction h.measurable_E) hm
  calc
    _  = (∑ t ∈ range n,
          ∫ ω, IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω ∂P) -
            ∑ t ∈ range n, ∫ ω, IsBayesAlgEnvSeq.actionMean κ E (A t ω) ω ∂P := by
        simp_rw [IsBayesAlgEnvSeq.regret_eq_sum_gap, IsBayesAlgEnvSeq.gap_eq_sub]
        rw [integral_finset_sum _ (by fun_prop), ← Finset.sum_sub_distrib]
        simp_rw [integral_sub hab (haa _)]
    _ = ((∑ t ∈ range n,
              ∫ ω, IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω ∂P) -
            ∑ t ∈ range n,
              ∫ ω, ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) t ω ∂P) +
          ((∑ t ∈ range n, ∫ ω, ucb A R' l u σ2 δ (A t ω) t ω ∂P) -
            ∑ t ∈ range n, ∫ ω, IsBayesAlgEnvSeq.actionMean κ E (A t ω) ω ∂P) := by
        simp [integral_ucb_action_eq_integral_ucb_bestAction hK h]
    _ = (∑ t ∈ range n,
            ∫ ω, IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
              ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) t ω ∂P) +
          ∑ t ∈ range n, ∫ ω, ucb A R' l u σ2 δ (A t ω) t ω -
            IsBayesAlgEnvSeq.actionMean κ E (A t ω) ω ∂P := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        simp_rw [← integral_sub hab (hub _), ← integral_sub (hua _) (haa _)]
    _ = _ := by
        rw [← integral_finset_sum _ (by fun_prop), ← integral_finset_sum _ (by fun_prop)]

lemma integral_sum_range_actionMean_bestAction_sub_ucb_bestAction_le
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    (hlu : l ≤ u) (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) ⟨σ2, hσ2.le⟩ (κ (e, a)))
    (hδ : 0 < δ) (n : ℕ) :
    P[fun ω ↦ ∑ s ∈ range n,
      (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
        ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω)] ≤
      2 * (u - l) * n ^ 2 * δ := by
  have := h.measurable_A
  have := h.measurable_E
  have := h.measurable_R
  set Fδ := {ω | ∀ t < n, pullCount A (IsBayesAlgEnvSeq.bestAction κ E ω) t ω ≠ 0 →
    |empMean A R' (IsBayesAlgEnvSeq.bestAction κ E ω) t ω -
        IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω|
      < √(2 * σ2 * Real.log (1 / δ) / (pullCount A (IsBayesAlgEnvSeq.bestAction κ E ω) t ω))}
  have hFδ_meas : MeasurableSet Fδ := by measurability
  have h_int : Integrable (fun ω ↦ ∑ s ∈ range n,
      (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
        ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω)) P :=
    integrable_finset_sum _ fun s _ ↦
      (IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_E (by fun_prop) hm).sub
        (integrable_uncurry_ucb_comp h.measurable_A h.measurable_R (by fun_prop)
          measurable_const)
  calc P[fun ω ↦ ∑ s ∈ range n,
          (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
            ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω)]
      = (∫ ω in Fδ, ∑ s ∈ range n,
            (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
              ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω) ∂P) +
          ∫ ω in Fδᶜ, ∑ s ∈ range n,
            (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
              ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω) ∂P :=
        (integral_add_compl hFδ_meas h_int).symm
    _ ≤ 0 + ∫ ω in Fδᶜ, ∑ s ∈ range n,
            (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
              ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω) ∂P := by
        gcongr
        apply setIntegral_nonpos hFδ_meas
        intro ω hω
        apply Finset.sum_nonpos
        intro s hs
        have : IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω ≤
            ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω := by
          unfold ucb
          split_ifs with h0
          · exact (hm (E ω) (IsBayesAlgEnvSeq.bestAction κ E ω)).2
          · have := abs_lt.mp ((hω s (mem_range.mp hs)) h0)
            exact le_max_of_le_right
              (le_min (hm (E ω) (IsBayesAlgEnvSeq.bestAction κ E ω)).2 (by linarith))
        linarith
    _ ≤ 0 + ∫ _ω in Fδᶜ, n * (u - l) ∂P := by
        apply add_le_add le_rfl
        apply setIntegral_mono_on h_int.integrableOn integrableOn_const hFδ_meas.compl
        intro ω _
        refine le_of_le_of_eq (Finset.sum_le_card_nsmul (range n) _ (u - l) fun s _ ↦ ?_) ?_
        · have h1 : IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω ≤ u :=
            (hm _ _).2
          have h2 : l ≤ ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω :=
            (ucb_mem_Icc hlu).1
          linarith
        · rw [Finset.card_range, nsmul_eq_mul]
    _ = 0 + n * (u - l) * P.real Fδᶜ := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ 0 + n * (u - l) * (2 * n * δ) := by
        gcongr
        · nlinarith
        · apply ENNReal.toReal_le_of_le_ofReal (by positivity)
          have : Fδᶜ = {ω | ∃ s < n, pullCount A (IsBayesAlgEnvSeq.bestAction κ E ω) s ω ≠ 0 ∧
              √(2 * σ2 * Real.log (1 / δ) /
                (pullCount A (IsBayesAlgEnvSeq.bestAction κ E ω) s ω : ℝ)) ≤
                |empMean A R' (IsBayesAlgEnvSeq.bestAction κ E ω) s ω -
                  IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω|} := by
            ext ω; simp only [Fδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push Not; rfl
          rw [this]
          exact (h.prob_abs_empMean_bestAction_sub_actionMean_ge_le hσ2 hs hδ n).trans
            (ENNReal.ofReal_le_ofReal (by nlinarith [hδ.le]))
    _ = 2 * (u - l) * n ^ 2 * δ := by ring

lemma integral_sum_range_ucb_action_sub_actionMean_action_le
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    (hlu : l ≤ u) (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) ⟨σ2, hσ2.le⟩ (κ (e, a)))
    (hδ : 0 < δ) (n : ℕ) :
    P[fun ω ↦ ∑ s ∈ range n,
      (ucb A R' l u σ2 δ (A s ω) s ω - IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω)] ≤
      (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) + 2 * K * (u - l) * n ^ 2 * δ := by
  have := h.measurable_A
  have := h.measurable_E
  have := h.measurable_R
  set Eδ := {ω | ∀ t < n, ∀ a, pullCount A a t ω ≠ 0 →
    |empMean A R' a t ω - IsBayesAlgEnvSeq.actionMean κ E a ω|
      < √(2 * σ2 * Real.log (1 / δ) / (pullCount A a t ω))}
  have hEδ_meas : MeasurableSet Eδ := by measurability
  have h_int : Integrable (fun ω ↦ ∑ s ∈ range n,
      (ucb A R' l u σ2 δ (A s ω) s ω - IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω)) P :=
    integrable_finset_sum _ fun s _ ↦
      (integrable_uncurry_ucb_comp h.measurable_A h.measurable_R (h.measurable_A s)
          measurable_const).sub
        (IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_E (h.measurable_A s) hm)
  calc P[fun ω ↦ ∑ s ∈ range n,
          (ucb A R' l u σ2 δ (A s ω) s ω - IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω)]
      = (∫ ω in Eδ, ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω -
              IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω) ∂P) +
          ∫ ω in Eδᶜ, ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω -
              IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω) ∂P :=
        (integral_add_compl hEδ_meas h_int).symm
    _ ≤ (∫ _ω in Eδ, (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) ∂P) +
          ∫ ω in Eδᶜ, ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω -
              IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω) ∂P := by
        apply add_le_add _ le_rfl
        apply setIntegral_mono_on h_int.integrableOn integrableOn_const hEδ_meas
        intro ω hω
        exact sum_ucb_sub_mean_le (fun a ↦ IsBayesAlgEnvSeq.actionMean κ E a ω) (hm (E ω)) hlu
          fun s hs hpc ↦ hω s hs (A s ω) hpc
    _ = ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) * P.real Eδ +
          ∫ ω in Eδᶜ, ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω -
              IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω) ∂P := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) +
          ∫ ω in Eδᶜ, ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω -
              IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω) ∂P := by
        apply add_le_add _ le_rfl
        exact mul_le_of_le_one_right
          (by have : 0 ≤ u - l := sub_nonneg.mpr hlu; positivity) measureReal_le_one
    _ ≤ ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) +
          ∫ _ω in Eδᶜ, n * (u - l) ∂P := by
        apply add_le_add le_rfl
        apply setIntegral_mono_on h_int.integrableOn integrableOn_const hEδ_meas.compl
        intro ω _
        refine le_of_le_of_eq (Finset.sum_le_card_nsmul (range n) _ (u - l) fun s _ ↦ ?_) ?_
        · have h1 : ucb A R' l u σ2 δ (A s ω) s ω ≤ u := (ucb_mem_Icc hlu).2
          have h2 : l ≤ IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω := (hm _ _).1
          linarith
        · rw [Finset.card_range, nsmul_eq_mul]
    _ = ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) +
          n * (u - l) * P.real Eδᶜ := by
        rw [setIntegral_const, smul_eq_mul]; ring
    _ ≤ ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) +
          n * (u - l) * (2 * K * n * δ) := by
        gcongr
        · nlinarith
        · apply ENNReal.toReal_le_of_le_ofReal (by positivity)
          have : Eδᶜ = {ω | ∃ s < n, ∃ a, pullCount A a s ω ≠ 0 ∧
              √(2 * σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
              |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E a ω|} := by
            ext ω; simp only [Eδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push Not; rfl
          rw [this]
          exact (h.prob_abs_empMean_sub_actionMean_ge_le hσ2 hs hδ n).trans
            (ENNReal.ofReal_le_ofReal
              (by nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) K]))
    _ = (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) +
          2 * K * (u - l) * n ^ 2 * δ := by ring

lemma integral_regret_le_of_delta_pos
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P) (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) ⟨σ2, hσ2.le⟩ (κ (e, a)))
    (hlu : l ≤ u) (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (hδ : 0 < δ) (n : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A n] ≤
      (u - l) * K + 2 * (K + 1) * (u - l) * n ^ 2 * δ +
        4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by
  calc P[IsBayesAlgEnvSeq.regret κ E A n]
      = P[fun ω ↦ ∑ s ∈ range n,
            (IsBayesAlgEnvSeq.actionMean κ E (IsBayesAlgEnvSeq.bestAction κ E ω) ω -
              ucb A R' l u σ2 δ (IsBayesAlgEnvSeq.bestAction κ E ω) s ω)] +
          P[fun ω ↦ ∑ s ∈ range n,
            (ucb A R' l u σ2 δ (A s ω) s ω - IsBayesAlgEnvSeq.actionMean κ E (A s ω) ω)] :=
        integral_regret_eq_add (hK := hK) (σ2 := σ2) (δ := δ) h hm n
    _ ≤ 2 * (u - l) * n ^ 2 * δ +
          ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) +
            2 * K * (u - l) * n ^ 2 * δ) :=
        add_le_add
          (integral_sum_range_actionMean_bestAction_sub_ucb_bestAction_le
            (hK := hK) (σ2 := σ2) (δ := δ) h hlu hm hσ2 hs hδ n)
          (integral_sum_range_ucb_action_sub_actionMean_action_le
            (hK := hK) (σ2 := σ2) (δ := δ) h hlu hm hσ2 hs hδ n)
    _ = (u - l) * K + 2 * (K + 1) * (u - l) * n ^ 2 * δ +
          4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by ring

lemma integral_regret_le
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ hK) E A R' P)
    (hlu : l ≤ u) (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (hσ2 : 0 < σ2)
    (hs : ∀ e a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) ⟨σ2, hσ2.le⟩ (κ (e, a))) (n : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A n]
      ≤ (3 * K + 2) * (u - l) + 8 * √(σ2 * K * n * Real.log n) := by
  by_cases ht : n = 0
  · simp [ht, IsBayesAlgEnvSeq.regret, Bandits.regret]
    nlinarith
  by_cases ht1_eq : n = 1
  · calc P[IsBayesAlgEnvSeq.regret κ E A n]
        = P[IsBayesAlgEnvSeq.regret κ E A 1] := by rw [ht1_eq]
      _ ≤ u - l := by
          rw [IsBayesAlgEnvSeq.regret_eq_sum_gap']
          simp only [Finset.range_one, Finset.sum_singleton]
          exact (integral_mono_of_nonneg
            (ae_of_all _ fun ω ↦ IsBayesAlgEnvSeq.gap_nonneg_of_le (fun e a ↦ (hm e a).2))
            (integrable_const _)
            (ae_of_all _ fun ω ↦ IsBayesAlgEnvSeq.gap_le_of_mem_Icc hm)).trans (by simp)
      _ ≤ (3 * K + 2) * (u - l) + 8 * √(σ2 * K * n * Real.log n) := by
          rw [ht1_eq]
          simp only [Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
          nlinarith
  · calc P[IsBayesAlgEnvSeq.regret κ E A n]
        ≤ (u - l) * K + 2 * (K + 1) * (u - l) * n ^ 2 * (1 / (n : ℝ) ^ 2)
            + 4 * √(2 * σ2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) * K * n) :=
          integral_regret_le_of_delta_pos (δ := 1 / n ^ 2) hK h hσ2 hs hlu hm (by positivity) n
      _ = (3 * K + 2) * (u - l)
            + 4 * √(2 * σ2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) * K * n) := by
          congr 1
          field_simp
          ring
      _ = (3 * K + 2) * (u - l) + 4 * √(2 * σ2 * (2 * Real.log n) * K * n) := by
          rw [one_div_one_div, Real.log_pow]
          norm_cast
      _ = (3 * K + 2) * (u - l) + 4 * √((2 : ℝ) ^ 2 * (σ2 * K * n * Real.log n)) := by
          congr 2
          ring_nf
      _ = (3 * K + 2) * (u - l) + 4 * (2 * √(σ2 * K * n * Real.log n)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      _ = (3 * K + 2) * (u - l) + 8 * √(σ2 * K * n * Real.log n) := by
          ring

end IntegralRegret

end TS

end Bandits
