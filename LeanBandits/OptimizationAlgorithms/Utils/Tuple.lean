/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib

open Finset

namespace Tuple

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

def max : α := univ.sup' (by simp) f

def min : α := univ.inf' (by simp) f

instance {n : ℕ} : Nonempty (Iic n) := Nonempty.intro ⟨0, insert_eq_self.mp rfl⟩

lemma exists_argmax {n : ℕ} (u : Iic n → α) : ∃ i, u i = max u := by
  have : Nonempty (Iic n) := inferInstance
  unfold max
  let A := u '' Set.univ
  suffices h : univ.sup' (by simp) u ∈ A by
    obtain ⟨x, -, h⟩ := h
    exact ⟨x, h⟩
  refine sup'_mem A (fun x hx y hy ↦ ?_) _ _ u fun i _ ↦ ?_
  · cases max_choice x y with
    | inl l => simp_all
    | inr r => simp_all
  · simp [A]

noncomputable def argmax {n : ℕ} (u : Iic n → α) := (exists_argmax u).choose

lemma argmax_spec {n : ℕ} (u : Iic n → α) : u (argmax u) = max u :=
  (exists_argmax u).choose_spec

variable [MeasurableSpace α]

@[fun_prop]
lemma measurable_max {n : ℕ} : Measurable (fun (t : Iic n → ℝ) => Tuple.max t) := by
  unfold Tuple.max
  have : Nonempty (Iic n) := inferInstance
  simp_all only [mem_Iic, nonempty_subtype]
  fun_prop

@[fun_prop]
lemma measurable_min_fst {n : ℕ} : Measurable (fun (t : Iic n → ℝ) => Tuple.min t) := by
  unfold Tuple.min
  have : Nonempty (Iic n) := inferInstance
  simp_all only [mem_Iic, nonempty_subtype]
  fun_prop


end Tuple
