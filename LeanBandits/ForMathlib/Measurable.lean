/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Measurability lemmas
-/

namespace MeasureTheory

lemma measurable_comp_comap {α β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    (f : α → β) {g : β → γ} (hg : Measurable g) :
    Measurable[mβ.comap f] (g ∘ f) := by
  rw [measurable_iff_comap_le, ← MeasurableSpace.comap_comp]
  refine MeasurableSpace.comap_mono ?_
  rw [← measurable_iff_comap_le]
  exact hg

end MeasureTheory
