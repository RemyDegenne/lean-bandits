/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanMachineLearning.OptimizationAlgorithms.Utils.Tuple
import LeanMachineLearning.SequentialLearning.Algorithm


open MeasureTheory ProbabilityTheory Finset NNReal Learning

/-!
# RankOpt: A Ranking Approach to Global Optimization

Implementation of the _RankOpt_ algorithm
[(_A Ranking Approach to Global Optimization_,
Malherbe et al. 2017)](https://arxiv.org/pdf/1603.04381)
defined on a measurable space. The algorithm samples from an arbitrary probability measure
on the set of potential maximizers of the function at each iteration.

## Main definitions

* `RankRule`: A rank rule is a measurable function that compares pairs of points.
  It returns 1 if the first point is ranked higher, -1 if lower, and 0 if equal.
* `potential_max`: The set of potential maximizers for the RankOpt algorithm.
* `potential_max_kernel`: The Markov kernel that samples from the set of potential maximizers
  according to a given measure `μ`.
* `RankOpt`: The RankOpt algorithm that samples from the set of potential maximizers using a given
  probability measure at each iteration.
-/

section RankRule

/-- A rank rule is a measurable function that compares pairs of points.
It returns 1 if the first point is ranked higher, -1 if lower, and 0 if equal. -/
def RankRule (α : Type*) [MeasurableSpace α] :=
  {f : α → α → ({-1, 0, 1} : Set ℝ) // Measurable <| Function.uncurry f}

end RankRule

variable {α β : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] {n : ℕ}
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [LinearOrder β]
  [SecondCountableTopology β] [OpensMeasurableSpace β] [OrderClosedTopology β]
  (data : Iic n → α × β)

namespace RankOpt

/-- Computes the ranking from observed function values.
Returns 1 if `y₁ > y₂`, 0 if `y₁ = y₂`, and -1 if `y₁ < y₂`. -/
noncomputable def ranking_data (y₁ y₂ : β) := if y₂ < y₁ then 1 else if y₂ = y₁ then 0 else -1

/-- Indicator function checking if two rankings agree.
Returns 1 if both values are equal, 0 otherwise. -/
noncomputable abbrev rindicator (r₁ r₂ : ℝ) := if r₁ = r₂ then (1 : ℝ) else 0

/-- Computes the ranking loss for a rank rule.
Measures the agreement between a candidate rule `r` and the rankings induced by the observed
function values on all pairs of data points, normalized by the number of pairs. -/
noncomputable def ranking_loss (r : RankRule α) :=
  2 * (n * (n + 1) : ℝ)⁻¹ * ∑ ij ∈ {(i, j) : Iic n × Iic n | i ≤ j},
    rindicator (r.1 (data ij.1).1 (data ij.2).1) (ranking_data (data ij.1).2 (data ij.2).2)

/-- The point in the observed data with the maximum function value. -/
noncomputable abbrev argmax_f := (data <| Tuple.argmax (fun i ↦ (data i).2)).1

/-- The set of potential maximizers for the RankOpt algorithm.
Contains all points `x` for which there exists a ranking rule `r` in the hypothesis class `𝓡`
that: (1) has zero ranking loss (perfectly consistent with the observed data),
and (2) ranks `x` at least as high as the current best observed point. -/
def potential_max (𝓡 : Set (RankRule α)) :=
    {x | ∃ (r : 𝓡), ranking_loss data r = 0 ∧ 0 ≤ (r.1.1 x (argmax_f data)).1}

lemma measurableSet_potential_max_prod {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable) :
    MeasurableSet {p : (Iic n → α × β) × α | p.2 ∈ potential_max p.1 𝓡} := by
  simp only [potential_max, Set.mem_setOf_eq, measurableSet_setOf]
  have : Countable (𝓡) := h𝓡.to_subtype
  refine Measurable.exists fun r ↦ (.and ?_ ?_)
  · simp only [ranking_loss]
    refine Measurable.eq ?_ measurable_const
    refine Measurable.const_mul (measurable_sum _ fun i hi ↦ ?_) _
    simp only [rindicator]
    refine Measurable.ite (measurableSet_eq_fun ?_ ?_) measurable_const measurable_const
    · have := r.1.2
      fun_prop
    · simp only [ranking_data]
      have : Measurable (fun (z : ℤ) ↦ (z : ℝ)) := by fun_prop
      refine this.comp ?_
      refine Measurable.ite ?_ measurable_const <| .ite ?_ measurable_const measurable_const
      · measurability
      · measurability
  · refine Measurable.le' measurable_const ?_
    have : Measurable (fun x : ({-1, 0, 1} : Set ℝ) ↦ (x : ℝ)) := by fun_prop
    refine this.comp (r.1.2.comp (measurable_snd.prodMk ?_))
    suffices Measurable (fun p : Iic n → α × β ↦ (p <| Tuple.argmax (fun i ↦ (p i).2)).1) by
      exact this.comp measurable_fst
    have h_eval : Measurable (fun p : (Iic n → α × β) × Iic n ↦ (p.1 p.2).1) := by
      suffices Measurable (fun p : (Iic n → α × β) × Iic n ↦ p.1 p.2) by
        fun_prop
      exact measurable_from_prod_countable_left fun i ↦ measurable_pi_apply i
    refine h_eval.comp (Measurable.prodMk ?_ ?_)
    · fun_prop
    · change Measurable (fun p : Iic n → α × β ↦ Tuple.argmax (fun i ↦ (p i).2))
      suffices Measurable (fun u : Iic n → β ↦ Tuple.argmax u) by
        fun_prop
      refine measurable_to_countable' fun i ↦ ?_
      simp only [Set.preimage, Set.mem_singleton_iff]
      let Maximizers {n : ℕ} (u : Iic n → β) : Set (Iic n) := {i | u i = Tuple.max u}
      have : {u : Iic n → β | Tuple.argmax u = i} = ⋃ (S)
          (hS : ∀ x, Maximizers x = S → Tuple.argmax x = i), {u | Maximizers u = S} := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
        constructor
        · intro hu x hx
          rw [← hu]
          unfold Tuple.argmax
          exact Classical.choose.congr_simp hx (Tuple.exists_argmax x)
        · intro h
          exact h u rfl
      rw [this]
      refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
      refine measurableSet_eq_fun (by fun_prop) measurable_const

lemma measurable_potential_max_inter {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable)
    {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun data : Iic n → α × β ↦ μ (potential_max data 𝓡 ∩ s)) := by
  set E := {p : (Iic n → α × β) × α | p.2 ∈ potential_max p.1 𝓡 ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_potential_max_prod h𝓡).inter (measurableSet_preimage measurable_snd hs)
  exact measurable_measure_prodMk_left hE_meas

/-- Markov kernel sampling from the set of potential maximizers according to μ. -/
noncomputable def potential_max_kernel {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable) :
    Kernel (Iic n → α × β) α := by
  refine ⟨fun data ↦ cond μ <| potential_max data 𝓡, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_potential_max_inter (β := β) μ h𝓡 (MeasurableSet.univ)
    simp [Set.inter_univ]
  · simp_rw [μ.restrict_apply hs]
    convert measurable_potential_max_inter (β := β) μ h𝓡 hs using 1
    simp [Set.inter_comm]

end RankOpt

open RankOpt

/- We suppose that the set of potential maximizers has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable)
  (h : ∀ n (data : Iic n → α × β), μ (potential_max data 𝓡) ≠ 0)

/-- The RankOpt algorithm for global optimization.
This algorithm uses a ranking approach to optimize an unknown function. It maintains a hypothesis
class `𝓡` of ranking rules. It starts with an arbitrary probability measure `μ` as initial
distribution and samples from the set of points that could be optimal according to ranking rules
consistent with the observed data [(Malherbe et al., 2017)](https://arxiv.org/pdf/1603.04381). -/
noncomputable def RankOpt : Algorithm α β where
  policy _ := potential_max_kernel μ h𝓡
  p0 := μ
  h_policy n := ⟨fun data => cond_isProbabilityMeasure (h n data)⟩
