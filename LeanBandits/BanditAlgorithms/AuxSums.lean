/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

open Finset

lemma sum_mod_range {K : ℕ} (hK : 0 < K) (a : Fin K) :
    (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) = 1 := by
  have h_iff (s : ℕ) (hs : s < K) : ⟨s % K, Nat.mod_lt _ hK⟩ = a ↔ s = a := by
    simp only [Nat.mod_eq_of_lt hs, Fin.ext_iff]
  calc (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
  _ = ∑ s ∈ range K, if s = a then 1 else 0 := sum_congr rfl fun s hs ↦ by grind
  _ = _ := by
    rw [sum_ite_eq']
    simp

lemma sum_mod_range_mul {K : ℕ} (hK : 0 < K) (m : ℕ) (a : Fin K) :
    (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) = m := by
  induction m with
  | zero => simp
  | succ n hn =>
    calc (∑ s ∈ range (K * (n + 1)), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
    _ = (∑ s ∈ range (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by ring_nf
    _ = (∑ s ∈ range (K * n), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
        + (∑ s ∈ Ico (K * n) (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      rw [sum_range_add_sum_Ico]
      grind
    _ = n + (∑ s ∈ Ico (K * n) (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      rw [hn]
    _ = n + (∑ s ∈ range K, if ⟨(s + K * n) % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      congr 1
      let e : ℕ ↪ ℕ := ⟨fun i : ℕ ↦ i + K * n, fun i j hij ↦ by grind⟩
      have : Finset.map e (range K) = Ico (K * n) (K * n + K) := by
        ext x
        simp only [mem_map, mem_range, Function.Embedding.coeFn_mk, mem_Ico, e]
        refine ⟨fun h ↦ by grind, fun h ↦ ?_⟩
        use x - K * n
        grind
      rw [← this, Finset.sum_map]
      congr
    _ = n + (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by simp
    _ = n + 1 := by rw [sum_mod_range hK]
