/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.SequentialLearning.FiniteActions

/-! # Tools to build bandit algorithms

-/

open MeasureTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_pullCount' (n : ℕ) (a : α) :
    Measurable (fun h : Iic n → α × ℝ ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_sumRewards' (n : ℕ) (a : α) :
    Measurable (fun h ↦ sumRewards' n h a) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then (h s).2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean' (n : ℕ) (a : α) :
    Measurable (fun h ↦ empMean' n h a) := by
  unfold empMean'
  fun_prop

end Bandits
