/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib

open Finset

namespace Tuple

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

abbrev max : α := univ.sup' (by simp) f

abbrev min : α := univ.inf' (by simp) f

lemma le_max (x : ι) : f x ≤ max f := by
  simp only [le_sup'_iff, mem_univ, true_and]
  exact ⟨x, le_refl _⟩

lemma min_le (x : ι) : min f ≤ f x := by
  simp only [inf'_le_iff, mem_univ, true_and]
  exact ⟨x, le_refl _⟩

instance {n : ℕ} : Nonempty (Iic n) := Nonempty.intro ⟨0, insert_eq_self.mp rfl⟩

/-- TODO: generalize -/
lemma neg_max_eq_min_neg {n : ℕ} (u : Iic n → ℝ) : -(max u) = min (-u) := by
  sorry

variable {n : ℕ} (u : Iic n → α)

lemma exists_argmax : ∃ i, u i = max u := by
  have : Nonempty (Iic n) := inferInstance
  let A := u '' Set.univ
  suffices h : univ.sup' (by simp) u ∈ A by
    obtain ⟨x, -, h⟩ := h
    exact ⟨x, h⟩
  refine sup'_mem A (fun x hx y hy ↦ ?_) _ _ u fun i _ ↦ ?_
  · cases max_choice x y with
    | inl l => simp_all
    | inr r => simp_all
  · simp [A]

noncomputable def argmax := (exists_argmax u).choose

lemma argmax_spec : u (argmax u) = max u :=
  (exists_argmax u).choose_spec

lemma le_argmax (x : Iic n) : u x ≤ u (argmax u) := by
  rw [argmax_spec u]
  exact le_max u x

lemma exists_argmin : ∃ i, u i = min u := by
  have : Nonempty (Iic n) := inferInstance
  let A := u '' Set.univ
  suffices h : univ.inf' (by simp) u ∈ A by
    obtain ⟨x, -, h⟩ := h
    exact ⟨x, h⟩
  refine inf'_mem A (fun x hx y hy ↦ ?_) _ _ u fun i _ ↦ ?_
  · cases min_choice x y with
    | inl l => simp_all
    | inr r => simp_all
  · simp [A]

noncomputable def argmin := (exists_argmin u).choose

lemma argmin_spec : u (argmin u) = min u :=
  (exists_argmin u).choose_spec

lemma argmin_le (x : Iic n) : u (argmin u) ≤ u x := by
  rw [argmin_spec u]
  exact min_le u x

variable [MeasurableSpace α]

@[fun_prop]
lemma measurable_max : Measurable (fun (t : Iic n → ℝ) => Tuple.max t) := by
  have : Nonempty (Iic n) := inferInstance
  simp_all only [mem_Iic, nonempty_subtype]
  fun_prop

@[fun_prop]
lemma measurable_min : Measurable (fun (t : Iic n → ℝ) => Tuple.min t) := by
  have : Nonempty (Iic n) := inferInstance
  simp_all only [mem_Iic, nonempty_subtype]
  fun_prop


end Tuple
