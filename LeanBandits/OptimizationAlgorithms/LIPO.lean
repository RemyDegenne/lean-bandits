/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.OptimizationAlgorithms.Utils.Tuple
import LeanBandits.OptimizationAlgorithms.Utils.Uniform
import LeanBandits.OptimizationAlgorithms.Utils.EuclideanSpace
import LeanBandits.SequentialLearning.Algorithm

open MeasureTheory ProbabilityTheory Finset NNReal Learning

/-!
# LIPO: Lipschitz Optimization
Implementation of the _LIPO_ algorithm
[(_Global optimization of Lipschitz functions_, Malherbe et al. 2017)](https://arxiv.org/abs/1703.02628)
defined on a measurable subset of a Euclidean space, with finite and non-zero measure.
The algorithm samples from the uniform distribution on the set of potential maximizers of
the function at each iteration.
-/

variable {d : ℕ} {α : Set (ℝᵈ d)} (mes_α : MeasurableSet α) (mα₁ : ℙ α ≠ ⊤) (κ : ℝ≥0)

namespace LIPO

noncomputable instance : MeasureSpace α := Measure.Subtype.measureSpace

instance : MeasurableSpace α := by infer_instance

instance i₁ : IsFiniteMeasure (ℙ : Measure α) := by
  rw [isFiniteMeasure_iff ℙ, Measure.Subtype.volume_univ]
  · exact mα₁.lt_top
  · exact mes_α.nullMeasurableSet

variable {n : ℕ} (data : Iic n → α × ℝ)

/-- The set of potential maximizers for the LIPO algorithm.
Given observed data points and function values, this set contains all points `x` where
the maximum observed value is at most the minimum Lipschitz upper bound across all observations.
The upper bound at `x` from observation `i` is `f(xᵢ) + κ · d(xᵢ, x)`, where `κ` is the
Lipschitz constant. -/
def potential_max : Set α :=
  {x | Tuple.max (fun i ↦ (data i).2) ≤ Tuple.min (fun i ↦ (data i).2 + κ * dist (data i).1 x)}

lemma measurableSet_potential_max_prod :
    MeasurableSet {p : (Iic n → α × ℝ) × α | p.2 ∈ potential_max κ p.1} := by
  unfold potential_max
  simp only [Set.mem_setOf_eq, measurableSet_setOf]
  refine Measurable.le' ?_ ?_
  · fun_prop
  · fun_prop

include mes_α mα₁ in
lemma measurable_volume_potential_max_inter (s : Set α) (hs : MeasurableSet s) :
    Measurable (fun data : Iic n → α × ℝ ↦ ℙ (potential_max κ data ∩ s)) := by
  set E := {p : (Iic n → α × ℝ) × α | p.2 ∈ potential_max κ p.1 ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_potential_max_prod κ).inter (measurableSet_preimage measurable_snd hs)
  have := i₁ mes_α mα₁
  exact measurable_measure_prodMk_left hE_meas

/-- Markov kernel that samples uniformly from the set of potential maximizers.
This kernel forms the core sampling strategy of LIPO: at each iteration, given the observed
data, it samples the next query point uniformly from `potential_max`. -/
noncomputable def potential_max_kernel : Kernel (Iic n → α × ℝ) α := by
  refine ⟨fun data ↦ uniform <| potential_max κ data, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [Measure.smul_apply, MeasureTheory.Measure.restrict_apply hs, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_volume_potential_max_inter mes_α mα₁ κ Set.univ (MeasurableSet.univ)
    simp [Set.inter_univ]
  · convert measurable_volume_potential_max_inter mes_α mα₁ κ s hs using 1
    simp [Set.inter_comm]

end LIPO

open LIPO

variable (mα₀ : ℙ α ≠ 0)

/- We suppose that the set of potential maximizers has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable (h : ∀ n (data : Iic n → α × ℝ), ℙ (potential_max κ data) ≠ 0)

/-- The LIPO (LIPschitz Optimization) algorithm for global optimization.
This algorithm optimizes an unknown function assuming only that it has a finite Lipschitz
constant `κ`. It starts with a uniform initial distribution and iteratively samples from
the set of potential maximizers, ensuring consistency and convergence to the global optimum
[(Malherbe et al., 2017)](https://arxiv.org/abs/1703.02628). -/
noncomputable def LIPO : Algorithm α ℝ where
  policy _ := potential_max_kernel mes_α mα₁ κ
  p0 := uniform Set.univ
  hp0 := by
    have := i₁ mes_α mα₁
    refine uniform_is_prob_measure ?_
    rwa [Measure.Subtype.volume_univ mes_α.nullMeasurableSet]
  h_policy n := by
    refine ⟨fun data => ?_⟩
    have := i₁ mes_α mα₁
    exact uniform_is_prob_measure <| h n data
