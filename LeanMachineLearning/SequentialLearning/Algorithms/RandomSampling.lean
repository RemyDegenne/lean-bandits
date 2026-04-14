/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanMachineLearning.ForMathlib.ENNReal
import LeanMachineLearning.ForMathlib.IndepFun
import LeanMachineLearning.Optimization.Algorithms.Utils.Tuple
import LeanMachineLearning.SequentialLearning.EvaluationEnv

open MeasureTheory ProbabilityTheory Learning Finset ENNReal Filter

open scoped Topology

/-!
# Random Sampling

Implementation of the _Random Sampling_ algorithm, which samples from a fixed probability
measure at each iteration.

## Main definitions

* `randomSampling`: The random sampling algorithm that samples from a fixed distribution at
each iteration.

## Main statements

The main results about the random sampling algorithm are stated using the `evalEnv` evaluation
environment, which rewards actions using a measurable function `f`.

- `hasLaw_actions`: Each action follows the distribution μ.
- `hasLaw_rewards`: Each reward follows the distribution μ.map f.
- `iIndep_actions`: Actions are mutually independent across time steps.
- `iIndep_rewards`: Rewards are mutually independent across time steps.
- `actions_tendsto_any`: The minimum distance from sampled actions to any point in α tends to zero
  in measure.
- `rewards_tendsto_any`: The minimum distance from rewards to any value of `f` tends to zero in
  measure.
- `tendsto_min`: The minimum reward converges in measure to the global minimum value.
- `tendsto_max`: The maximum reward converges in measure to the global maximum value.
-/

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β] [Nonempty β] {μ : Measure α} [IsProbabilityMeasure μ] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

open Set in
/-- The Pure Random Search algorithm. -/
@[simps]
noncomputable def randomSampling (μ : Measure α) [IsProbabilityMeasure μ] : Algorithm α β where
  policy _ := Kernel.const _ μ
  p0 := μ

namespace randomSampling

variable {A : ℕ → Ω → α} {R : ℕ → Ω → β} {f : α → β} (hf : Measurable f)

/-- Each action follows the distribution μ. -/
lemma hasLaw_actions (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hf) P) (n : ℕ) :
    HasLaw (A n) μ P := by
  by_cases hn : n = 0
  · rw [hn]
    exact h.hasLaw_action_zero
  · push Not at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact hasLaw_of_hasCondDistrib_const <| h.hasCondDistrib_action k

/-- Each reward follows the distribution μ.map f. -/
lemma hasLaw_rewards (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hf) P) (n : ℕ) :
    HasLaw (R n) (μ.map f) P := by
  refine HasLaw.congr ?_ (IsAlgEnvSeq.reward_ae_eq_eval_action hf h n)
  have hA := h.measurable_A n
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.map_map hf hA, (hasLaw_actions hf h n).map_eq]

/-- Actions are mutually independent. -/
lemma iIndep_actions (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hf) P) :
    iIndepFun A P := by
  have hA := h.measurable_A
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have condDistrib_eq := (h.hasCondDistrib_action n).condDistrib_eq
  simp only [randomSampling_policy] at condDistrib_eq
  have law_eq := (hasLaw_actions hf h (n + 1)).map_eq
  rw [← law_eq, ← indepFun_iff_condDistrib_eq_const ?_ (by fun_prop)] at condDistrib_eq
  · have meas_fst : Measurable (fun (f : Iic n → α × β) ↦ (fun i ↦ (f i).1)) := by
      fun_prop
    exact (condDistrib_eq.comp meas_fst measurable_id).symm
  · exact (IsAlgEnvSeq.measurable_hist (h.measurable_A) (h.measurable_R) n).aemeasurable

/-- Rewards are mutually independent. -/
lemma iIndep_rewards (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hf) P) :
    iIndepFun R P :=
  have (n : ℕ) : f ∘ A n =ᵐ[P] R n :=
    (IsAlgEnvSeq.reward_ae_eq_eval_action hf h n).symm
  iIndepFun.congr this <| (iIndep_actions hf h).comp _ (fun _ ↦ hf)

variable [PseudoMetricSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
  [μ.IsOpenPosMeasure]

/-- The minimum distance from sampled actions to any point tends to zero. -/
theorem actions_tendsto_any (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hf) P) (a : α) :
    ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ Tuple.min (fun (j : Iic i) ↦ dist (A j.1 x) a)}) atTop (𝓝 0) := by
  set randomSampling_alg := randomSampling (β := β) μ
  intro ε hε
  refine tendsto_zero_le (g := fun n ↦ P (⋂ i ∈ Iic n, {x | ε ≤ dist (A i x) a})) ?_ ?_
  · have inter_prod (n : ℕ) : P (⋂ j ∈ Iic n, {x | ε ≤ dist (A j x) a}) =
        ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} := by
      refine iIndepSet.meas_biInter ?_ _
      rw [iIndepSet_iff_meas_biInter fun i ↦ ?_]
      · intro s
        have iIndep_actions := randomSampling.iIndep_actions hf h
        rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at iIndep_actions
        have meas_dist : ∀ i ∈ s, MeasurableSet {x | ε ≤ dist x a} := by
          intro i hs
          measurability
        specialize iIndep_actions s meas_dist
        simpa only [Set.preimage] using iIndep_actions
      · have hAi := h.measurable_A i
        measurability
    simp_rw [inter_prod]
    have prod_law (n : ℕ) : ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} =
        ∏ j ∈ Iic n, μ {x | ε ≤ dist x a} := by
      refine prod_congr rfl fun j hj ↦ ?_
      have hlaw (n : ℕ) : HasLaw (A n) μ P := randomSampling.hasLaw_actions hf h n
      rw [← (hlaw j).map_eq, P.map_apply]
      · simp
      · exact h.measurable_A j
      · measurability
    simp_rw [prod_law]
    simp only [prod_const, Nat.card_Iic]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one ?_ |> Tendsto.comp <| tendsto_add_atTop_nat 1
    have compl : {x | ε ≤ dist x a} = {x | dist x a < ε}ᶜ := by
      ext a
      simp
    rw [compl, measure_compl (by measurability) (by simp), measure_univ]
    refine ENNReal.sub_lt_self (by simp) (by simp) ?_
    exact (Metric.measure_ball_pos μ a hε).ne'
  · intro n
    refine measure_mono ?_
    simp only [mem_Iic, Set.subset_iInter_iff, Set.setOf_subset_setOf]
    intro i hi ω (hω : ε ≤ Tuple.min (fun (j : Iic n) ↦ dist (A j.1 ω) a))
    simp_all only [univ_eq_attach, le_inf'_iff, mem_attach, forall_const, Subtype.forall, mem_Iic]

variable [PseudoMetricSpace β] [BorelSpace β] (hfc : Continuous f)

/-- The minimum distance from image of actions to any value tends to zero. -/
lemma image_actions_tendsto_any (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P) (a : α) :
    ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ Tuple.min (fun (j : Iic i) ↦ dist (f (A j.1 x)) (f a))}) atTop (𝓝 0) := by
  intro ε hε
  have hf := hfc.measurable
  rw [Metric.continuous_iff] at hfc
  obtain ⟨δ, hδ, hfc⟩ := hfc a ε hε
  refine actions_tendsto_any hf h a δ hδ |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← Tuple.argmin_spec]
  set j := Tuple.argmin (fun (i : Iic n) ↦ dist (A i.1 ω) a)
  by_contra! h_contra
  specialize hfc (A j.1 ω) h_contra
  have := Tuple.min_le (fun (j : Iic n) ↦ dist (f (A (j) ω)) (f a)) j
  linarith

/-- The minimum distance from rewards to any value tends to zero. -/
lemma rewards_tendsto_any (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P) (a : α) :
    ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ Tuple.min (fun (j : Iic i) ↦ dist (R j.1 x) (f a))}) atTop (𝓝 0) := by
  intro ε hε
  convert image_actions_tendsto_any hfc h a ε hε using 2 with n
  refine measure_congr ?_
  let g : ((Iic n) → β) → ℝ := fun r ↦ Tuple.min (fun i ↦ dist (r i) (f a))
  filter_upwards [IsAlgEnvSeq.reward_ae_eq_evals_actions_comp hfc.measurable h g] with ω hω
  simp only [eq_iff_iff]
  change ε ≤ Tuple.min (fun (j : Iic n) ↦ dist (R j ω) (f a)) ↔
    ε ≤ Tuple.min (fun (j : Iic n) ↦ dist (f (A j ω)) (f a))
  simp [g, hω]

variable {R : ℕ → Ω → ℝ} {f : α → ℝ} (hfc : Continuous f) {a : α}

/-- The minimum function value converges to the global minimum. -/
lemma tendsto_min₀ (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P)
    (hf_min : ∀ x, f a ≤ f x) : TendstoInMeasure P (fun n ω ↦
      Tuple.min (fun (i : Iic n) ↦ f (A i.1 ω))) atTop (fun _ ↦ f a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine image_actions_tendsto_any hfc h a ε hε |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← Tuple.argmin_spec]
  set j := Tuple.argmin (fun (i : Iic n) ↦ dist (f (A i ω)) (f a))
  have : dist (Tuple.min fun (i : Iic n) ↦ f (A i ω)) (f a) ≤ dist (f (A j ω)) (f a) := by
    rw [← Tuple.argmin_spec]
    set k := Tuple.argmin (fun (i : Iic n) ↦ f (A i ω))
    have := hf_min (A k ω)
    have : f (A k ω) ≤ f (A j ω) :=
      Tuple.argmin_le (fun (i : Iic n) ↦ f (A i ω)) j
    simp [Real.dist_eq]
    grind
  have := hω.trans this
  by_contra! h_contra
  linarith

/-- The minimum reward converges to the global minimum value. -/
lemma tendsto_min (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P)
    (hf_min : ∀ x, f a ≤ f x) : TendstoInMeasure P (fun n ω ↦
      Tuple.min (fun (i : Iic n) ↦ R i.1 ω)) atTop (fun _ ↦ f a) := by
  refine TendstoInMeasure.congr_left (fun n ↦ ?_) <| tendsto_min₀ hfc h hf_min
  filter_upwards [IsAlgEnvSeq.reward_ae_eq_evals_actions_comp hfc.measurable h Tuple.min] with ω hω
  rw [← hω]

/-- The maximum function value converges to the global maximum. -/
lemma tendsto_max₀ (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P)
    (hf_max : ∀ x, f x ≤ f a) : TendstoInMeasure P (fun n ω ↦
      Tuple.max (fun (i : Iic n) ↦ f (A i.1 ω))) atTop (fun _ ↦ f a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine image_actions_tendsto_any hfc h a ε hε |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← Tuple.argmin_spec]
  set j := Tuple.argmin (fun (i : Iic n) ↦ dist (f (A i ω)) (f a))
  have : dist (Tuple.max fun (i : Iic n) ↦ f (A i ω)) (f a) ≤ dist (f (A j ω)) (f a) := by
    rw [← Tuple.argmax_spec]
    set k := Tuple.argmax (fun (i : Iic n) ↦ f (A i ω))
    have := hf_max (A k ω)
    have : f (A j ω) ≤ f (A k ω) :=
      Tuple.le_argmax (fun (i : Iic n) ↦ f (A i ω)) j
    simp [Real.dist_eq]
    grind
  have := hω.trans this
  by_contra! h_contra
  linarith

/-- The maximum reward converges to the global maximum value. -/
lemma tendsto_max (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv hfc.measurable) P)
    (hf_max : ∀ x, f x ≤ f a) :
    TendstoInMeasure P (fun n ω ↦ Tuple.max (fun (i : Iic n) ↦ R i.1 ω)) atTop (fun _ ↦ f a) := by
  refine TendstoInMeasure.congr_left (fun n ↦ ?_) <| tendsto_max₀ hfc h hf_max
  filter_upwards [IsAlgEnvSeq.reward_ae_eq_evals_actions_comp hfc.measurable h Tuple.max] with ω hω
  rw [← hω]

end randomSampling
