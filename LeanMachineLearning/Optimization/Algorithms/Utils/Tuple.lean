/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

open Finset

namespace Tuple

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

/-- The maximum value of a tuple. -/
abbrev max : α := univ.sup' (by simp) f

/-- The minimum value of a tuple. -/
abbrev min : α := univ.inf' (by simp) f

lemma le_max (x : ι) : f x ≤ max f := le_sup' _ (by simp)

lemma min_le (x : ι) : min f ≤ f x := inf'_le _ (by simp)

instance {n : ℕ} : Nonempty (Iic n) := ⟨0, insert_eq_self.mp rfl⟩

variable {n : ℕ} (u : Iic n → α)

lemma exists_argmax : ∃ i, u i = max u := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (by simp : Finset.univ.Nonempty) u
  exact ⟨i, hi.symm⟩

/-- The index of the maximum value of a tuple. -/
noncomputable def argmax := (exists_argmax u).choose

lemma argmax_spec : u (argmax u) = max u :=
  (exists_argmax u).choose_spec

lemma le_argmax (x : Iic n) : u x ≤ u (argmax u) := by
  rw [argmax_spec u]
  exact le_max u x

lemma exists_argmin : ∃ i, u i = min u := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (by simp : Finset.univ.Nonempty) u
  exact ⟨i, hi.symm⟩

/-- The index of the minimum value of a tuple. -/
noncomputable def argmin := (exists_argmin u).choose

lemma argmin_spec : u (argmin u) = min u :=
  (exists_argmin u).choose_spec

lemma argmin_le (x : Iic n) : u (argmin u) ≤ u x := by
  rw [argmin_spec u]
  exact min_le u x

lemma neg_max_eq_min_neg [AddGroup α] [AddLeftMono α] [AddRightMono α] {n : ℕ} (u : Iic n → α) :
    -(max u) = min (-u) := by
  simp only [max, univ_eq_attach, min, Pi.neg_apply]
  refine le_antisymm ?_ ?_
  · simp only [le_inf'_iff, mem_attach, neg_le_neg_iff, le_sup'_iff, true_and, Subtype.exists,
    mem_Iic, forall_const, Subtype.forall]
    intro i hi
    exact ⟨i, hi, le_rfl⟩
  · simp only [inf'_le_iff, mem_attach, neg_le_neg_iff, sup'_le_iff, forall_const, Subtype.forall,
    mem_Iic, true_and, Subtype.exists]
    exact ⟨argmax u, by grind, fun i hi ↦ le_argmax u ⟨i, mem_Iic.mpr hi⟩⟩

variable [MeasurableSpace α]

variable [TopologicalSpace α] [BorelSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]

@[fun_prop]
lemma measurable_max [ContinuousSup α] : Measurable (fun (t : Iic n → α) => max t) := by
  fun_prop

@[fun_prop]
lemma measurable_min [ContinuousInf α] : Measurable (fun (t : Iic n → α) => min t) := by
  fun_prop

@[fun_prop]
lemma measurable_argmax [MeasurableEq α] [ContinuousSup α] :
    Measurable fun (u : Iic n → α) ↦ argmax u := by
  refine measurable_to_countable' fun i ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff]
  let Maximizers {n : ℕ} (u : Iic n → α) : Set (Iic n) := {j | u j = max u}
  have : {u : Iic n → α | argmax u = i} = ⋃ (S)
      (hS : ∀ x, Maximizers x = S → argmax x = i), {u | Maximizers u = S} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
    constructor
    · intro hu x hx
      rw [← hu]
      exact Classical.choose.congr_simp hx (exists_argmax x)
    · intro h
      exact h u rfl
  rw [this]
  refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
  exact measurableSet_eq_fun (by fun_prop) measurable_const

@[fun_prop]
lemma measurable_argmin [MeasurableEq α] [ContinuousInf α] :
    Measurable fun (u : Iic n → α) ↦ argmin u := by
  refine measurable_to_countable' fun i ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff]
  let Minimizers {n : ℕ} (u : Iic n → α) : Set (Iic n) := {j | u j = Tuple.min u}
  have : {u : Iic n → α | argmin u = i} = ⋃ (S)
      (hS : ∀ x, Minimizers x = S → argmin x = i), {u | Minimizers u = S} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
    constructor
    · intro hu x hx
      rw [← hu]
      exact Classical.choose.congr_simp hx (exists_argmin x)
    · intro h
      exact h u rfl
  rw [this]
  refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
  exact measurableSet_eq_fun (by fun_prop) measurable_const

end Tuple
