
/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MapComap

@[expose] public section

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[simp]
lemma ProbabilityTheory.Kernel.prodMkLeft_eq_prodMkLeft [h_nonempty : Nonempty γ]
    (κ ν : Kernel α β) :
    κ.prodMkLeft γ = ν.prodMkLeft γ ↔ κ = ν := by
  simp only [Kernel.ext_iff, Kernel.prodMkLeft_apply, Prod.forall]
  exact ⟨fun h b ↦ h h_nonempty.some b, fun h _ b ↦ h b⟩

end ProbabilityTheory.Kernel
