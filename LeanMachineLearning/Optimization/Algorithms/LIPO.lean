/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Optimization.Algorithms.Utils.Tuple
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# LIPO: Lipschitz Optimization

Implementation of the _LIPO_ algorithm
[(_Global optimization of Lipschitz functions_,
Malherbe et al. 2017)](https://arxiv.org/abs/1703.02628)
defined on a measurable space with a metric. The algorithm samples from an arbitrary
probability measure on the set of potential maximizers of the function at each iteration.

## Main definitions

* `potential_max`: The set of potential maximizers for the LIPO algorithm.
* `potential_max_kernel`: The Markov kernel that samples from the set of potential maximizers
  according to a given measure `μ`.
* `LIPO`: The LIPO algorithm that samples from the set of potential maximizers using a given
  probability measure at each iteration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset NNReal Learning

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α) [IsProbabilityMeasure μ] {n : ℕ} (κ : ℝ≥0)
  (data : Iic n → α × ℝ)

namespace LIPO

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

lemma measurable_potential_max_inter {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun data : Iic n → α × ℝ ↦ μ (potential_max κ data ∩ s)) := by
  set E := {p : (Iic n → α × ℝ) × α | p.2 ∈ potential_max κ p.1 ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_potential_max_prod κ).inter (measurableSet_preimage measurable_snd hs)
  exact measurable_measure_prodMk_left hE_meas

/-- Markov kernel sampling from the set of potential maximizers according to μ. -/
noncomputable def potential_max_kernel : Kernel (Iic n → α × ℝ) α := by
  refine ⟨fun data ↦ cond μ <| potential_max κ data, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_potential_max_inter μ κ (MeasurableSet.univ)
    simp [Set.inter_univ]
  · simp_rw [μ.restrict_apply hs]
    convert measurable_potential_max_inter μ κ hs using 1
    simp [Set.inter_comm]

end LIPO

open LIPO

/- We suppose that the set of potential maximizers has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable (h : ∀ n (data : Iic n → α × ℝ), μ (potential_max κ data) ≠ 0)

/-- The LIPO (LIPschitz Optimization) algorithm for global optimization.
This algorithm optimizes an unknown function assuming only that it has a finite Lipschitz
constant `κ`. It starts with an arbitrary probability measure `μ` as initial distribution and
iteratively samples from the set of potential maximizers, ensuring consistency and convergence to
the global optimum [(Malherbe et al., 2017)](https://arxiv.org/abs/1703.02628). -/
noncomputable def LIPO : Algorithm α ℝ where
  policy _ := potential_max_kernel μ κ
  p0 := μ
  h_policy n := ⟨fun data => cond_isProbabilityMeasure (h n data)⟩
