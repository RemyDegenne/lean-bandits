/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib
import LeanBandits.Bandit

/-!
# Regret

-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} {ν : Kernel α ℝ} {k : ℕ → α} {t : ℕ} {a : α}
  [DecidableEq α]

/-! ### Definitions of regret, gaps, pull counts -/

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
def regret (ν : Kernel α ℝ) (k : ℕ → α) (t : ℕ) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (k s))[id]

/-- Gap of an arm `a`: difference between the highest mean of the arms and the mean of `a`. -/
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

omit [DecidableEq α] in
lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

/-- Number of times arm `a` was pulled up to time `t` (excluding `t`). -/
noncomputable def pullCount [DecidableEq α] (k : ℕ → α) (a : α) (t : ℕ) : ℕ :=
  #(filter (fun s ↦ k s = a) (range t))

open Classical in
lemma monotone_pullCount (k : ℕ → α) (a : α) : Monotone (pullCount k a) :=
  fun _ _ _ ↦ card_le_card (filter_subset_filter _ (by simpa))

lemma pullCount_eq_pullCount_add_one (k : ℕ → α) (t : ℕ) :
    pullCount k (k t) (t + 1) = pullCount k (k t) t + 1 := by
  simp [pullCount, range_succ, filter_insert]

lemma pullCount_eq_pullCount (k : ℕ → α) (a : α) (t : ℕ) (h : k t ≠ a) :
    pullCount k a (t + 1) = pullCount k a t := by
  simp [pullCount, range_succ, filter_insert, h]

lemma pullCount_eq_sum (k : ℕ → α) (a : α) (t : ℕ) :
    pullCount k a t = ∑ s ∈ range t, if k s = a then 1 else 0 := by simp [pullCount]

/-- Number of steps until arm `a` was pulled exactly `m` times. -/
noncomputable
def stepsUntil (k : ℕ → α) (a : α) (m : ℕ) : ℕ∞ := sInf ((↑) '' {s | pullCount k a (s + 1) = m})

lemma stepsUntil_eq_dite (k : ℕ → α) (a : α) (m : ℕ) [Decidable (∃ s, pullCount k a (s + 1) = m)] :
    stepsUntil k a m =
      if h : ∃ s, pullCount k a (s + 1) = m then (Nat.find h : ℕ∞) else ⊤ := by
  unfold stepsUntil
  split_ifs with h
  · refine le_antisymm ?_ ?_
    · refine sInf_le ?_
      simpa using Nat.find_spec h
    · simp only [le_sInf_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Nat.cast_le, Nat.find_le_iff]
      exact fun n hn ↦  ⟨n, le_rfl, hn⟩
  · push_neg at h
    suffices {s | pullCount k a (s + 1) = m} = ∅ by simp [this]
    ext s
    simpa using (h s)

lemma stepsUntil_pullCount_le (k : ℕ → α) (a : α) (t : ℕ) :
    stepsUntil k a (pullCount k a (t + 1)) ≤ t := by
  rw [stepsUntil]
  exact csInf_le (OrderBot.bddBelow _) ⟨t, rfl, rfl⟩

lemma stepsUntil_pullCount_eq (k : ℕ → α) (t : ℕ) :
    stepsUntil k (k t) (pullCount k (k t) (t + 1)) = t := by
  apply le_antisymm (stepsUntil_pullCount_le k (k t) t)
  suffices ∀ t', pullCount k (k t) (t' + 1) = pullCount k (k t) t + 1 → t ≤ t' by
    simpa [stepsUntil, pullCount_eq_pullCount_add_one]
  exact fun t' h ↦ Nat.le_of_lt_succ ((monotone_pullCount k (k t)).reflect_lt (h ▸ lt_add_one _))

/-- Reward obtained when pulling arm `a` for the `m`-th time. -/
noncomputable
def rewardByCount (a : α) (m : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) : ℝ :=
  match (stepsUntil (arm · h) a m) with
  | ⊤ => z m a
  | (n : ℕ) => reward n h

lemma rewardByCount_eq_ite (a : α) (m : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    rewardByCount a m h z =
      if (stepsUntil (arm · h) a m) = ⊤ then z m a
      else reward (stepsUntil (arm · h) a m).toNat h := by
  unfold rewardByCount
  cases stepsUntil (arm · h) a m <;> simp

lemma rewardByCount_pullCount_add_one_eq_reward (t : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    rewardByCount (arm t h) (pullCount (arm · h) (arm t h) t + 1) h z = reward t h := by
  rw [rewardByCount, ← pullCount_eq_pullCount_add_one, stepsUntil_pullCount_eq]

lemma sum_rewardByCount_eq_sum_reward
    (a : α) (t : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    ∑ m ∈ Icc 1 (pullCount (arm · h) a t), rewardByCount a m h z =
      ∑ s ∈ range t, if (arm s h) = a then (reward s h) else 0 := by
  induction' t with t ht
  · simp [pullCount]
  by_cases hta : arm t h = a
  · rw [← hta] at ht ⊢
    rw [pullCount_eq_pullCount_add_one, sum_Icc_succ_top (Nat.le_add_left 1 _), ht]
    rw [sum_range_succ, if_pos rfl, rewardByCount_pullCount_add_one_eq_reward]
  · rwa [pullCount_eq_pullCount _ _ _ hta, sum_range_succ, if_neg hta, add_zero]

lemma sum_pullCount_mul [Fintype α] (k : ℕ → α) (f : α → ℝ) (t : ℕ) :
    ∑ a, pullCount k a t * f a = ∑ s ∈ range t, f (k s) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) k f

lemma sum_pullCount [Fintype α] : ∑ a, pullCount k a t = t := by
  suffices ∑ a, pullCount k a t * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν k t = ∑ a, pullCount k a t * gap ν a := by
  simp_rw [sum_pullCount_mul, regret, gap, sum_sub_distrib]
  simp

section BestArm

variable [Fintype α] [Nonempty α]

/-- Arm with the highest mean. -/
noncomputable def bestArm (ν : Kernel α ℝ) : α :=
  (exists_max_image univ (fun a ↦ (ν a)[id]) (univ_nonempty_iff.mpr inferInstance)).choose

omit [DecidableEq α] in
lemma le_bestArm (a : α) : (ν a)[id] ≤ (ν (bestArm ν))[id] :=
  (exists_max_image univ (fun a ↦ (ν a)[id])
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

omit [DecidableEq α] in
lemma gap_eq_bestArm_sub : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := by
  rw [gap]
  congr
  refine le_antisymm ?_ (le_ciSup (f := fun a ↦ (ν a)[id]) (by simp) (bestArm ν))
  exact ciSup_le le_bestArm

end BestArm

end Bandits
