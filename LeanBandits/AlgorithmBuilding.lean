/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Metrizable.Basic

/-! # Tools to build bandit algorithms

-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

/-- Number of pulls of arm `a` up to (and including) time `n`. -/
noncomputable
def pullCount' (n : ℕ) (h : Iic n → α × ℝ) (a : α) := #{s | (h s).1 = a}

/-- Sum of rewards of arm `a` up to (and including) time `n`. -/
noncomputable
def sumRewards' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  ∑ s, if (h s).1 = a then (h s).2 else 0

/-- Empirical mean of arm `a` at time `n`. -/
noncomputable
def empMean' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  (sumRewards' n h a) / (pullCount' n h a)

omit [MeasurableSpace α] in
lemma pullCount'_eq_sum (n : ℕ) (h : Iic n → α × ℝ) (a : α) :
    pullCount' n h a = ∑ s : Iic n, if (h s).1 = a then 1 else 0 := by simp [pullCount']

@[fun_prop]
lemma measurable_pullCount' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_sumRewards' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ sumRewards' n h a) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then (h s).2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ empMean' n h a) := by
  unfold empMean'
  fun_prop

end Bandits
