
/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

@[expose] public section

open MeasureTheory

/-- Two deterministic kernels are equal if and only if their underlying functions are equal. -/
@[simp]
lemma ProbabilityTheory.Kernel.deterministic_eq_deterministic_iff
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.SeparatesPoints β]
    {f g : α → β} {hf : Measurable f} {hg : Measurable g} :
    Kernel.deterministic f hf = Kernel.deterministic g hg ↔ f = g := by
  simp [Kernel.ext_iff, Kernel.deterministic_apply, dirac_eq_dirac_iff, funext_iff]
