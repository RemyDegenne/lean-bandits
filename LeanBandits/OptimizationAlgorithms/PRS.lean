/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.Algorithm

open MeasureTheory ProbabilityTheory Learning Set

/-!
# PRS: Pure Random Search
Implementation of the _Pure Random Search_ algorithm, which samples from the uniform
distribution on the input space at each iteration.
-/

variable {α β : Type*} [MeasureSpace α] [IsFiniteMeasure (ℙ : Measure α)]
  [NeZero (ℙ : Measure α)] [MeasurableSpace β]

noncomputable
def PRS : Algorithm α β where
  policy _ := Kernel.const _ ((ℙ (univ : Set α))⁻¹ • ℙ)
  p0 := (ℙ (univ : Set α))⁻¹ • ℙ
  h_policy _ := ⟨fun _ ↦ by simp [isProbabilityMeasure_iff]⟩
  hp0 := by simp [isProbabilityMeasure_iff]
