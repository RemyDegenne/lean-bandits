/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.Algorithm
import LeanBandits.OptimizationAlgorithms.Utils.Tuple
import LeanBandits.SequentialLearning.EvaluationEnv
import LeanBandits.ForMathlib.IndepFun
import Mathlib

open MeasureTheory ProbabilityTheory Learning

/-!
# PRS: Pure Random Search
Implementation of the _Pure Random Search_ algorithm, which samples from the uniform
distribution on the input space at each iteration.
-/

section -- Move this somewhere else

lemma hasLaw_of_hasCondDistrib_const {β' Ω' Ω'' : Type*}
    [MeasurableSpace β'] [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    [MeasurableSpace Ω'']
    {X : Ω'' → β'} {Y : Ω'' → Ω'} {μ : Measure Ω'}
    {Q : Measure Ω''} [IsProbabilityMeasure Q] [SFinite μ]
    (h : HasCondDistrib Y X (Kernel.const _ μ) Q) : HasLaw Y μ Q := by
    obtain ⟨hY, hX, h⟩ := h
    refine ⟨hY, ?_⟩
    have h_snd : (Q.map (fun ω => (X ω, Y ω))).snd = μ := by
      have h_map : Q.map (fun ω => (X ω, Y ω)) = (Q.map X) ⊗ₘ (Kernel.const _ μ) :=
        have h_map : Q.map (fun ω => (X ω, Y ω)) = (Q.map X) ⊗ₘ (condDistrib Y X Q) :=
        (compProd_map_condDistrib hY).symm
        h_map.trans (Measure.compProd_congr h)
      rw [h_map, MeasureTheory.Measure.snd_compProd]
      simp [MeasureTheory.Measure.map_apply_of_aemeasurable hX]
    rwa [Measure.snd_map_prodMk₀ hX] at h_snd

open ENNReal Filter Topology in
lemma ENNReal.tendsto_zero_le {α : Type*} {f g : α → ℝ≥0∞} {ι : Filter α}
    (hg : Tendsto g ι (𝓝 0)) (h : f ≤ g) : Tendsto f ι (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ 0) tendsto_const_nhds hg ?_ h
  intro
  simp

end

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

open Set in
@[simps]
noncomputable
def PRS (μ : Measure α) [IsProbabilityMeasure μ] : Algorithm α β where
  policy _ := Kernel.const _ μ
  p0 := μ

namespace PRS

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β] [Nonempty β]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → α} {R : ℕ → Ω → β} {f : α → β} (hf : Measurable f) {μ : Measure α}
  [IsProbabilityMeasure μ]

lemma hasLaw_action
    (h' : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P)
    (n : ℕ) : HasLaw (A n) (PRS (β := β) μ).p0 P := by
  by_cases hn : n = 0
  · rw [hn]
    exact h'.hasLaw_action_zero
  · push_neg at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact hasLaw_of_hasCondDistrib_const <| h'.hasCondDistrib_action k

open Finset in
lemma iIndep_actions (h' : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) :
    iIndepFun A P := by
  have hA := h'.measurable_A
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have condDistrib_eq := (h'.hasCondDistrib_action n).condDistrib_eq
  have law_eq := (hasLaw_action hf h' (n + 1)).map_eq
  simp only [PRS_p0, PRS_policy] at law_eq condDistrib_eq
  rw [← law_eq, ← indepFun_iff_condDistrib_eq_const ?_ (by fun_prop)] at condDistrib_eq
  · have meas_fst : Measurable (fun (f : Iic n → α × β) ↦ (fun i ↦ (f i).1)) := by
      fun_prop
    exact (condDistrib_eq.comp meas_fst measurable_id).symm
  · exact (IsAlgEnvSeq.measurable_hist (h'.measurable_A) (h'.measurable_R) n).aemeasurable

variable [PseudoMetricSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
  [μ.IsOpenPosMeasure]

open Finset Preorder Filter Topology ENNReal in
/-- The probability of sampling points at distance at least ε from a given point goes to zero
as the number of samples goes to infinity. -/
theorem convergence (h' : IsAlgEnvSeq A R (PRS μ) (evalEnv hf) P) (a : α) :
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
        have iIndep_actions := PRS.iIndep_actions hf h'
        rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at iIndep_actions
        have meas_dist : ∀ i ∈ s, MeasurableSet {x | ε ≤ dist x a} := by
          intro i hs
          measurability
        specialize iIndep_actions s meas_dist
        simpa only [Set.preimage] using iIndep_actions
      · have hAi := h'.measurable_A i
        measurability
    simp_rw [inter_prod]
    have prod_law (n : ℕ) : ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} =
        ∏ j ∈ Iic n, μ {x | ε ≤ dist x a} := by
      refine prod_congr rfl fun j hj ↦ ?_
      have hlaw (n : ℕ) : HasLaw (A n) μ P := PRS.hasLaw_action hf h' n
      rw [← (hlaw j).map_eq, P.map_apply]
      · simp
      · exact h'.measurable_A j
      · measurability
    simp_rw [prod_law]
    simp only [prod_const, Nat.card_Iic]
    refine Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one ?_) (tendsto_add_atTop_nat 1)
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
    unfold Tuple.min at hω
    simp_all

end PRS
