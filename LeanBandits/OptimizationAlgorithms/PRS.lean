/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.ForMathlib.ENNReal
import LeanBandits.ForMathlib.IndepFun
import LeanBandits.OptimizationAlgorithms.Utils.Tuple
import LeanBandits.SequentialLearning.EvaluationEnv

open MeasureTheory ProbabilityTheory Learning Finset ENNReal Filter

open scoped Topology

/-!
# PRS: Pure Random Search
Implementation of the _Pure Random Search_ algorithm, which samples from a fixe probability measure
at each iteration.
-/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

open Set in
@[simps]
noncomputable
def PRS (μ : Measure α) [IsProbabilityMeasure μ] : Algorithm α β where
  policy _ := Kernel.const _ μ
  p0 := μ

namespace PRS

section

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β] [Nonempty β]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → α} {R : ℕ → Ω → β} {f : α → β} (hf : Measurable f) {μ : Measure α}
  [IsProbabilityMeasure μ] (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P)

lemma hasLaw_actions (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) (n : ℕ) : HasLaw (A n) μ P := by
  by_cases hn : n = 0
  · rw [hn]
    exact h.hasLaw_action_zero
  · push_neg at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact hasLaw_of_hasCondDistrib_const <| h.hasCondDistrib_action k

lemma hasLaw_rewards (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) (n : ℕ) :
    HasLaw (R n) (μ.map f) P := by
  refine HasLaw.congr ?_ (IsAlgEnvSeq.reward_eq_eval_action hf h n)
  have hA := h.measurable_A n
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.map_map hf hA, (hasLaw_actions hf h n).map_eq]

lemma iIndep_actions (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) :
    iIndepFun A P := by
  have hA := h.measurable_A
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have condDistrib_eq := (h.hasCondDistrib_action n).condDistrib_eq
  have law_eq := (hasLaw_actions hf h (n + 1)).map_eq
  simp only [PRS_policy] at condDistrib_eq
  rw [← law_eq, ← indepFun_iff_condDistrib_eq_const ?_ (by fun_prop)] at condDistrib_eq
  · have meas_fst : Measurable (fun (f : Iic n → α × β) ↦ (fun i ↦ (f i).1)) := by
      fun_prop
    exact (condDistrib_eq.comp meas_fst measurable_id).symm
  · exact (IsAlgEnvSeq.measurable_hist (h.measurable_A) (h.measurable_R) n).aemeasurable

variable [PseudoMetricSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
  [μ.IsOpenPosMeasure]

theorem tendsto_any (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) (a : α) :
    ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ Tuple.min (fun (j : Iic i) ↦ dist (A j.1 x) a)}) atTop (𝓝 0) := by
  set PRS_alg := PRS (β := β) μ
  intro ε hε
  refine tendsto_zero_le (g := fun n ↦ P (⋂ i ∈ Iic n, {x | ε ≤ dist (A i x) a})) ?_ ?_
  · have inter_prod (n : ℕ) : P (⋂ j ∈ Iic n, {x | ε ≤ dist (A j x) a}) =
        ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} := by
      refine iIndepSet.meas_biInter ?_ _
      rw [iIndepSet_iff_meas_biInter fun i ↦ ?_]
      · intro s
        have iIndep_actions := PRS.iIndep_actions hf h
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
      have hlaw (n : ℕ) : HasLaw (A n) μ P := PRS.hasLaw_actions hf h n
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

end

section Real

variable [StandardBorelSpace α] [Nonempty α] [PseudoMetricSpace α] [OpensMeasurableSpace α]
  [SecondCountableTopology α] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {f : α → ℝ} (hfc : Continuous f)
  {μ : Measure α} [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hfc.measurable) P) {a : α}

lemma tendsto_min (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hfc.measurable) P)
    (hf_min : ∀ x, f a ≤ f x) :
    TendstoInMeasure P (fun n ω ↦ Tuple.min (fun (i : Iic n) ↦ R i.1 ω)) atTop (fun _ ↦ f a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hf := hfc.measurable
  rw [Metric.continuous_iff] at hfc
  obtain ⟨δ, hδ, hfc⟩ := hfc a ε hε
  have (n : ℕ) : P {x | ε ≤ dist (Tuple.min fun (i : Iic n) ↦ R i x) (f a)} =
      P {x | ε ≤ dist (Tuple.min fun (i : Iic n) ↦ f (A i x)) (f a)} := by
    refine measure_congr ?_
    filter_upwards [IsAlgEnvSeq.reward_eq_evals_actions_comp hf h Tuple.min] with ω hω
    simp only [eq_iff_iff]
    change ε ≤ dist (Tuple.min fun (i : Iic n) ↦ R (↑i) ω) (f a) ↔
      ε ≤ dist (Tuple.min fun (i : Iic n) ↦ f (A ↑i ω)) (f a)
    rw [hω]
  simp_rw [this]
  refine tendsto_any hf h a δ hδ |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← Tuple.argmin_spec]
  set j := Tuple.argmin (fun (i : Iic n) ↦ dist (A i ω) a)
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
  specialize hfc (A j ω) h_contra
  linarith

lemma tendsto_max (h : IsAlgEnvSeq A R (PRS μ) (evalEnv hfc.measurable) P)
    (hf_max : ∀ x, f x ≤ f a) :
    TendstoInMeasure P (fun n ω ↦ Tuple.max (fun (i : Iic n) ↦ R i.1 ω)) atTop (fun _ ↦ f a) := by
  have hmf_min (x : α) : -f a ≤ -f x := by
    specialize hf_max x
    linarith
  have := tendsto_min (continuous_neg_iff.mpr hfc) (IsAlgEnvSeq.neg hfc.measurable h) hmf_min
  rw [tendstoInMeasure_iff_dist] at this ⊢
  intro ε hε
  specialize this ε hε
  have dist_neg (n : ℕ) : {x | ε ≤ dist (Tuple.max fun (i : Iic n) ↦ R i x) (f a)} =
      {x | ε ≤ dist (-(Tuple.max fun (i : Iic n) ↦ R i x)) (-f a)} := by
    simp [dist_neg_neg]
  simp_rw [dist_neg]
  convert this with n ω
  exact Tuple.neg_max_eq_min_neg _

end Real

end PRS
