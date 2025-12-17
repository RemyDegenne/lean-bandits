/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace HasSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ} {c cX cY : ℝ≥0}

section Sum

variable {ι ι' : Type*} {X : ι → Ω → ℝ} {cX : ι → ℝ≥0} {s : Finset ι}
  {Y : ι' → Ω → ℝ} {cY : ι' → ℝ≥0} {t : Finset ι'}

lemma measure_sum_le_sum_le [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (fun ω ↦ ∑ j ∈ t, Y j ω) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ Real.exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  have hX_int i (his : i ∈ s) : Integrable (X i) μ := by
    have h_int := (hX_subG i his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  have hY_int j (his : j ∈ t) : Integrable (Y j) μ := by
    have h_int := (hY_subG j his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  refine (measureReal_le_le_exp
    (cX := ∑ i ∈ s, cX i) (cY := ∑ j ∈ t, cY j) ?_ ?_ h_indep_sum ?_).trans_eq ?_
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - μ[X i])) (∑ i ∈ s, cX i) μ by
      convert this
      rw [integral_finset_sum _ hX_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hX_subG
    exact hX_indep.comp (g := fun i x ↦ x - μ[X i]) (by fun_prop)
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ j ∈ t, (Y j ω - μ[Y j])) (∑ j ∈ t, cY j) μ by
      convert this
      rw [integral_finset_sum _ hY_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hY_subG
    exact hY_indep.comp (g := fun i x ↦ x - μ[Y i]) (by fun_prop)
  · rwa [integral_finset_sum _ hX_int, integral_finset_sum _ hY_int]
  · congr
    · rw [integral_finset_sum _ hY_int]
    · rw [integral_finset_sum _ hX_int]

lemma measure_sum_le_sum_le' [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ Real.exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  refine measure_sum_le_sum_le hX_indep hY_indep hX_subG hY_subG ?_ h_le
  exact h_indep_sum.comp (φ := fun p ↦ ∑ i ∈ s, p i) (ψ := fun p ↦ ∑ j ∈ t, p j)
    (by fun_prop) (by fun_prop)

end Sum

end HasSubgaussianMGF

end ProbabilityTheory
