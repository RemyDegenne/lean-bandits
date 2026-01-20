/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.Distributions.Uniform
import LeanBandits.SequentialLearning.Algorithm

open ProbabilityTheory
open Learning

variable {K : ℕ} (hK : 0 < K)

noncomputable
def uniformAlgorithm : Algorithm (Fin K) ℝ :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  { policy _ := Kernel.const _ (PMF.uniformOfFintype (Fin K)).toMeasure
    p0 := (PMF.uniformOfFintype (Fin K)).toMeasure }
