/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic

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

lemma MeasurableSet.imp {α : Type*} {mα : MeasurableSpace α} {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x → q x} := by
  have h_eq : {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x} := by
    ext x
    grind
  rw [h_eq]
  exact MeasurableSet.union hs.compl ht

lemma MeasurableSet.iff {α : Type*} {mα : MeasurableSpace α} {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ↔ q x} := by
  have h_eq : {x | p x ↔ q x} = ({x | p x}ᶜ ∪ {x | q x}) ∩ ({x | q x}ᶜ ∪ {x | p x}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    grind
  rw [h_eq]
  exact (MeasurableSet.union hs.compl ht).inter (MeasurableSet.union ht.compl hs)

end MeasureTheory
