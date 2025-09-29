/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Regret
import LeanBandits.AlgorithmBuilding

/-!
# Equalities between definitions of random variables used in bandit algorithms

-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ} (hK : 0 < K)

lemma pullCount_add_one_eq_pullCount' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} :
    pullCount a (n + 1) h = pullCount' n (fun i ↦ h i) a := by
  rw [pullCount_eq_sum, pullCount'_eq_sum]
  unfold arm
  rw [Finset.sum_coe_sort (f := fun s ↦ if (h s).1 = a then 1 else 0) (Iic n)]
  congr with m
  simp only [mem_range, mem_Iic]
  grind

lemma pullCount_eq_pullCount' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} (hn : n ≠ 0) :
    pullCount a n h = pullCount' (n - 1) (fun i ↦ h i) a := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    rw [pullCount_add_one_eq_pullCount']
    have : n + 1 - 1 = n := by simp
    exact this ▸ rfl

lemma sumRewards_add_one_eq_sumRewards' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} :
    sumRewards a (n + 1) h = sumRewards' n (fun i ↦ h i) a := by
  unfold sumRewards sumRewards' arm reward
  rw [Finset.sum_coe_sort (f := fun s ↦ if (h s).1 = a then (h s).2 else 0) (Iic n)]
  congr with m
  simp only [mem_range, mem_Iic]
  grind

lemma sumRewards_eq_sumRewards' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} (hn : n ≠ 0) :
    sumRewards a n h = sumRewards' (n - 1) (fun i ↦ h i) a := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    rw [sumRewards_add_one_eq_sumRewards']
    have : n + 1 - 1 = n := by simp
    exact this ▸ rfl

lemma empMean_add_one_eq_empMean' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} :
    empMean a (n + 1) h = empMean' n (fun i ↦ h i) a := by
  unfold empMean empMean'
  rw [sumRewards_add_one_eq_sumRewards', pullCount_add_one_eq_pullCount']

lemma empMean_eq_empMean' {a : Fin K} {n : ℕ} {h : ℕ → Fin K × ℝ} (hn : n ≠ 0) :
    empMean a n h = empMean' (n - 1) (fun i ↦ h i) a := by
  unfold empMean empMean'
  rw [sumRewards_eq_sumRewards' hn, pullCount_eq_pullCount' hn]

end Bandits
