/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.UniformOn
import LeanBandits.SequentialLearning.Algorithm

/-! # The Uniform Algorithm -/

open MeasureTheory ProbabilityTheory Learning

namespace Bandits

variable {K : ℕ} {hK : 0 < K}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def uniformAlgorithm (hK : 0 < K) : Algorithm (Fin K) ℝ :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin K))) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  { policy _ := Kernel.const _ (uniformOn Set.univ)
    p0 := uniformOn Set.univ }

/-- The uniform algorithm gives positive probability to every action. -/
lemma uniformAlgorithm_p0_pos (a : Fin K) : (uniformAlgorithm hK).p0 {a} > 0 := by
  simp only [uniformAlgorithm, uniformOn]
  refine cond_pos_of_inter_ne_zero MeasurableSet.univ ?_
  simp only [Set.univ_inter, Measure.count_singleton, ne_eq, one_ne_zero, not_false_eq_true]

/-- The uniform algorithm's policy gives positive probability to every action. -/
lemma uniformAlgorithm_policy_pos {n : ℕ} (h : Finset.Iic n → Fin K × ℝ) (a : Fin K) :
    (uniformAlgorithm hK).policy n h {a} > 0 := by
  simp only [uniformAlgorithm, Kernel.const_apply, uniformOn]
  refine cond_pos_of_inter_ne_zero MeasurableSet.univ ?_
  simp only [Set.univ_inter, Measure.count_singleton, ne_eq, one_ne_zero, not_false_eq_true]

end Bandits
