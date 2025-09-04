/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit
import LeanBandits.Regret

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

section Aux

variable {α β Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β}
  {X : α → β} {Y : α → Ω}

lemma ProbabilityTheory.condDistrib_comp_map [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hY, Measure.snd_map_prodMk₀ hX]

lemma MeasureTheory.Measure.comp_congr {κ η : Kernel α β} (h : ∀ᵐ a ∂μ, κ a = η a) :
    κ ∘ₘ μ = η ∘ₘ μ :=
  Measure.bind_congr_right h

end Aux

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [MeasurableSingletonClass α]

omit [DecidableEq α] [MeasurableSingletonClass α] in
@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

omit [DecidableEq α] [MeasurableSingletonClass α] in
@[fun_prop]
lemma _root_.Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf

@[fun_prop]
lemma measurable_pullCount (a : α) (t : ℕ) : Measurable (fun k ↦ pullCount k a t) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun k : ℕ → α ↦ if k s = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_stepsUntil (a : α) (m : ℕ) : Measurable (fun k ↦ stepsUntil k a m) := by
  classical
  have h_union : {k' | ∃ s, pullCount k' a (s + 1) = m}
      = ⋃ s : ℕ, {k' | pullCount k' a (s + 1) = m} := by ext; simp
  have h_meas_set : MeasurableSet {k' | ∃ s, pullCount k' a (s + 1) = m} := by
    rw [h_union]
    exact MeasurableSet.iUnion fun s ↦ (measurableSet_singleton _).preimage (by fun_prop)
  simp_rw [stepsUntil_eq_dite]
  suffices Measurable fun k ↦ if h : k ∈ {k' | ∃ s, pullCount k' a (s + 1) = m}
      then (Nat.find h : ℕ∞) else ⊤ by convert this
  refine Measurable.dite (s := {k' : ℕ → α | ∃ s, pullCount k' a (s + 1) = m})
    (f := fun x ↦ (Nat.find x.2 : ℕ∞)) (g := fun _ ↦ ⊤) ?_ (by fun_prop) h_meas_set
  refine Measurable.coe_nat_enat ?_
  refine measurable_find _ fun k ↦ ?_
  suffices MeasurableSet {x : ℕ → α | pullCount x a (k + 1) = m} by
    have : Subtype.val ''
          {x : {k' : ℕ → α | ∃ s, pullCount k' a (s + 1) = m} | pullCount x a (k + 1) = m}
        = {x : ℕ → α | pullCount x a (k + 1) = m} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.coe_setOf, Set.mem_image, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
      exact fun h ↦ ⟨_, h⟩
    refine (MeasurableEmbedding.subtype_coe h_meas_set).measurableSet_image.mp ?_
    rw [this]
    exact (measurableSet_singleton _).preimage (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_stepsUntil'' (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) ↦ stepsUntil (arm · ω) a m) :=
  (measurable_stepsUntil a m).comp (by fun_prop)

lemma measurable_stepsUntil' (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ stepsUntil (arm · ω.1) a m) :=
  (measurable_stepsUntil'' a m).comp measurable_fst

@[fun_prop]
lemma measurable_rewardByCount (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ rewardByCount a m ω.1 ω.2) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' a m
  · fun_prop
  · change Measurable ((fun p : ℕ × (ℕ → α × ℝ) ↦ reward p.1 p.2)
      ∘ (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ ((stepsUntil (arm · ω.1) a m).toNat, ω.1)))
    have : Measurable fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦
        ((stepsUntil (arm · ω.1) a m).toNat, ω.1) :=
      (measurable_stepsUntil' a m).toNat.prodMk (by fun_prop)
    exact Measurable.comp (by fun_prop) this

lemma condDistrib_rewardByCount_stepsUntil {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
        (Bandit.measure alg ν)
      =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)] Kernel.const _ (ν a) := by
  sorry

/-- The reward received at the `m`-th pull of arm `a` has law `ν a`. -/
lemma hasLaw_rewardByCount {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    HasLaw (fun ω ↦ rewardByCount a m ω.1 ω.2) (ν a) (Bandit.measure alg ν) where
  map_eq := by
    have h_condDistrib :
        condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
          (Bandit.measure alg ν)
        =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)]
          Kernel.const _ (ν a) := condDistrib_rewardByCount_stepsUntil a m
    calc (Bandit.measure alg ν).map (fun ω ↦ rewardByCount a m ω.1 ω.2)
    _ = (condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
          (Bandit.measure alg ν))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) := by
      rw [condDistrib_comp_map (by fun_prop) (by fun_prop)]
    _ = (Kernel.const _ (ν a))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) :=
      Measure.comp_congr h_condDistrib
    _ = ν a := by
      have : IsProbabilityMeasure
          ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) :=
        isProbabilityMeasure_map (by fun_prop)
      simp

lemma identDistrib_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (n m : ℕ) :
    IdentDistrib (fun ω ↦ rewardByCount a n ω.1 ω.2) (fun ω ↦ rewardByCount a m ω.1 ω.2)
      (Bandit.measure alg ν) (Bandit.measure alg ν) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount a n).map_eq, (hasLaw_rewardByCount a m).map_eq]

lemma iIndepFun_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    iIndepFun (fun (p : α × ℕ) ω ↦ rewardByCount p.1 p.2 ω.1 ω.2) (Bandit.measure alg ν) := by
  sorry

end Bandits
