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

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`, then `X` is integrable. -/
lemma integrable_of_mem_interior_integrableExpSet
    {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    Integrable X μ := by
  simpa using integrable_pow_of_mem_interior_integrableExpSet h 1

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

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ} {c cX cY : ℝ≥0}

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

lemma sub_of_indepFun (hX : HasSubgaussianMGF X cX μ) (hY : HasSubgaussianMGF Y cY μ)
    (hindep : IndepFun X Y μ) :
    HasSubgaussianMGF (fun ω ↦ X ω - Y ω) (cX + cY) μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

-- todo: name
lemma measure_le_le (hX : HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) cX μ)
    (hY : HasSubgaussianMGF (fun ω ↦ Y ω - μ[Y]) cY μ)
    (hindep : IndepFun X Y μ) (h_le : μ[Y] ≤ μ[X]) :
    μ.real {ω | X ω ≤ Y ω} ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
  calc μ.real {ω | X ω ≤ Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) ≤ (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω ↦ (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      ?_
    · rw [add_comm cX]
      refine sub_of_indepFun hY hX ?_
      exact hindep.symm.comp (φ := fun x ↦ x - μ[Y]) (ψ := fun x ↦ x - μ[X])
        (by fun_prop) (by fun_prop)
    · grind
    · congr 2
      grind

lemma integrableExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) :
    integrableExpSet X μ = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact hX.integrable_exp_mul t

lemma integrable (hX : HasSubgaussianMGF X c μ) : Integrable X μ := by
  refine integrable_of_mem_interior_integrableExpSet ?_
  simp [integrableExpSet_eq_univ hX]

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
  refine (measure_le_le (cX := ∑ i ∈ s, cX i) (cY := ∑ j ∈ t, cY j) ?_ ?_ h_indep_sum ?_).trans_eq
    ?_
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

end Sum

end HasSubgaussianMGF

end ProbabilityTheory
