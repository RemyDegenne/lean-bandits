/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

theorem mgf_const_mul {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}
    {t : ℝ} (α : ℝ) : mgf (fun ω ↦ α * X ω) μ t = mgf X μ (α * t) := by
  rw [← mgf_smul_left]
  rfl

namespace Kernel.HasSubgaussianMGF

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma id_map_iff (hX : Measurable X) :
    HasSubgaussianMGF X c κ ν ↔ HasSubgaussianMGF id c (κ.map X) ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor
    · intro t
      rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
        Measure.deterministic_comp_eq_map]
      rw [integrable_map_measure (by fun_prop) hX.aemeasurable]
      exact h.integrable_exp_mul t
    · simp_rw [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable]
      exact h.mgf_le
  · have : X = id ∘ X := rfl
    rw [this]
    exact .of_map hX h

protected lemma const_mul (h : HasSubgaussianMGF X c κ ν) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * c) κ ν where
  integrable_exp_mul t := by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    specialize hω (t * r)
    rw [mgf_const_mul, mul_comm]
    refine hω.trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring

end Kernel.HasSubgaussianMGF

namespace HasSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubgaussianMGF X c μ ↔ HasSubgaussianMGF id c (μ.map X) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor
    · intro t
      rw [integrable_map_measure (by fun_prop) hX]
      exact h.integrable_exp_mul t
    · intro t
      rw [mgf_id_map hX]
      exact h.mgf_le t
  · have : X = id ∘ X := rfl
    rw [this]
    exact .of_map hX h

lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (hX : HasSubgaussianMGF X c μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubgaussianMGF Y c μ' := by
  rw [id_map_iff hXY.aemeasurable_fst] at hX
  rwa [id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

protected lemma const_mul (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * c) μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r

lemma sub_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : IndepFun X Y μ) :
    HasSubgaussianMGF (fun ω ↦ X ω - Y ω) (cX + cY) μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

end HasSubgaussianMGF

end ProbabilityTheory
