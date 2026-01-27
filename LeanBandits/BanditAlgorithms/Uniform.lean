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

variable {K : ℕ}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def uniformAlgorithm (hK : 0 < K) : Algorithm (Fin K) ℝ :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin K))) :=
    uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
  { policy _ := Kernel.const _ (uniformOn Set.univ)
    p0 := uniformOn Set.univ }

end Bandits
