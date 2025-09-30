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

variable {α : Type*} [DecidableEq α] {mα : MeasurableSpace α} {ν : Kernel α ℝ}
  {h : ℕ → α × ℝ} {m n t : ℕ} {a : α}

/-! ### Definitions of regret, gaps, pull counts -/

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
def regret (ν : Kernel α ℝ) (t : ℕ) (h : ℕ → α × ℝ) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (arm s h))[id]

/-- Gap of an arm `a`: difference between the highest mean of the arms and the mean of `a`. -/
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

omit [DecidableEq α] in
lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

/-- Number of times arm `a` was pulled up to time `t` (excluding `t`). -/
noncomputable def pullCount [DecidableEq α] (a : α) (t : ℕ) (h : ℕ → α × ℝ) : ℕ :=
  #(filter (fun s ↦ arm s h = a) (range t))

@[simp]
lemma pullCount_zero (a : α) (h : ℕ → α × ℝ) : pullCount a 0 h = 0 := by simp [pullCount]

lemma pullCount_one : pullCount a 1 h = if arm 0 h = a then 1 else 0 := by
  simp only [pullCount, range_one]
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨0, by simp [h]⟩
  · simp [h]

open Classical in
lemma monotone_pullCount (a : α) (h : ℕ → α × ℝ) : Monotone (pullCount a · h) :=
  fun _ _ _ ↦ card_le_card (filter_subset_filter _ (by simpa))

lemma pullCount_eq_pullCount_add_one (t : ℕ) (h : ℕ → α × ℝ) :
    pullCount (arm t h) (t + 1) h = pullCount (arm t h) t h + 1 := by
  simp [pullCount, range_succ, filter_insert]

lemma pullCount_eq_pullCount (ha : arm t h ≠ a) :  pullCount a (t + 1) h = pullCount a t h := by
  simp [pullCount, range_succ, filter_insert, ha]

lemma pullCount_add_one :
    pullCount a (t + 1) h = pullCount a t h + if arm t h = a then 1 else 0 := by
  split_ifs with h
  · rw [← h, pullCount_eq_pullCount_add_one]
  · rw [pullCount_eq_pullCount h, add_zero]

lemma pullCount_eq_sum (a : α) (t : ℕ) (h : ℕ → α × ℝ) :
    pullCount a t h = ∑ s ∈ range t, if arm s h = a then 1 else 0 := by simp [pullCount]

lemma pullCount_le (a : α) (t : ℕ) (h : ℕ → α × ℝ) : pullCount a t h ≤ t :=
  (card_filter_le _ _).trans_eq (by simp)

/-- Number of steps until arm `a` was pulled exactly `m` times. -/
noncomputable
def stepsUntil (a : α) (m : ℕ) (h : ℕ → α × ℝ) : ℕ∞ := sInf ((↑) '' {s | pullCount a (s + 1) h = m})

lemma stepsUntil_eq_top_iff : stepsUntil a m h = ⊤ ↔ ∀ s, pullCount a (s + 1) h ≠ m := by
  simp [stepsUntil, sInf_eq_top]

lemma stepsUntil_zero_of_ne (hka : arm 0 h ≠ a) : stepsUntil a 0 h = 0 := by
  unfold stepsUntil
  simp_rw [← bot_eq_zero, sInf_eq_bot, bot_eq_zero]
  intro n hn
  refine ⟨0, ?_, hn⟩
  simp only [Set.mem_image, Set.mem_setOf_eq, Nat.cast_eq_zero, exists_eq_right, zero_add]
  rw [← zero_add 1, pullCount_eq_pullCount hka]
  simp

lemma stepsUntil_zero_of_eq (hka : arm 0 h = a) : stepsUntil a 0 h = ⊤ := by
  rw [stepsUntil_eq_top_iff]
  suffices 0 < pullCount a 1 h by
    intro n hn
    refine lt_irrefl 0 ?_
    exact this.trans_le (le_trans (monotone_pullCount _ _ (by omega)) hn.le)
  rw [← hka, ← zero_add 1, pullCount_eq_pullCount_add_one]
  simp

lemma stepsUntil_eq_dite (a : α) (m : ℕ) (h : ℕ → α × ℝ)
    [Decidable (∃ s, pullCount a (s + 1) h = m)] :
    stepsUntil a m h =
      if h : ∃ s, pullCount a (s + 1) h = m then (Nat.find h : ℕ∞) else ⊤ := by
  unfold stepsUntil
  split_ifs with h'
  · refine le_antisymm ?_ ?_
    · refine sInf_le ?_
      simpa using Nat.find_spec h'
    · simp only [le_sInf_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Nat.cast_le, Nat.find_le_iff]
      exact fun n hn ↦ ⟨n, le_rfl, hn⟩
  · push_neg at h'
    suffices {s | pullCount a (s + 1) h = m} = ∅ by simp [this]
    ext s
    simpa using (h' s)

lemma stepsUntil_pullCount_le (h : ℕ → α × ℝ) (a : α) (t : ℕ) :
    stepsUntil a (pullCount a (t + 1) h) h ≤ t := by
  rw [stepsUntil]
  exact csInf_le (OrderBot.bddBelow _) ⟨t, rfl, rfl⟩

lemma stepsUntil_pullCount_eq (h : ℕ → α × ℝ) (t : ℕ) :
    stepsUntil (arm t h) (pullCount (arm t h) (t + 1) h) h = t := by
  apply le_antisymm (stepsUntil_pullCount_le h (arm t h) t)
  suffices ∀ t', pullCount (arm t h) (t' + 1) h = pullCount (arm t h) t h + 1 → t ≤ t' by
    simpa [stepsUntil, pullCount_eq_pullCount_add_one]
  exact fun t' h' ↦ Nat.le_of_lt_succ ((monotone_pullCount (arm t h) h).reflect_lt
    (h' ▸ lt_add_one _))

/-- If we pull arm `a` at time 0, the first time at which it is pulled once is 0. -/
lemma stepsUntil_one_of_eq (hka : arm 0 h = a) : stepsUntil a 1 h = 0 := by
  classical
  have h_pull : pullCount a 1 h = 1 := by simp [pullCount_one, hka]
  have h_le := stepsUntil_pullCount_le h a 0
  simpa [h_pull] using h_le

lemma stepsUntil_eq_zero_iff :
    stepsUntil a m h = 0 ↔ (m = 0 ∧ arm 0 h ≠ a) ∨ (m = 1 ∧ arm 0 h = a) := by
  classical
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have h_exists : ∃ s, pullCount a (s + 1) h = m := by
      by_contra! h_contra
      rw [← stepsUntil_eq_top_iff] at h_contra
      simp [h_contra] at h'
    simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, Nat.cast_eq_zero, Nat.find_eq_zero,
      zero_add] at h'
    rw [pullCount_one] at h'
    by_cases hka : arm 0 h = a
    · simp only [hka, ↓reduceIte] at h'
      simp [h'.symm, hka]
    · simp only [hka, ↓reduceIte] at h'
      simp [h'.symm, hka]
  · cases h' with
  | inl h =>
    rw [h.1, stepsUntil_zero_of_ne h.2]
  | inr h =>
    rw [h.1]
    exact stepsUntil_one_of_eq h.2

lemma arm_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount a (s + 1) h = m) :
    arm (stepsUntil a m h).toNat h = a := by
  classical
  simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, ENat.toNat_coe]
  have h_spec := Nat.find_spec h_exists
  have h_spec' n := Nat.find_min h_exists (m := n)
  by_cases h_zero : Nat.find h_exists = 0
  · simp only [h_zero, zero_add, not_lt_zero', IsEmpty.forall_iff, implies_true] at *
    by_contra h_ne
    rw [← zero_add 1, pullCount_eq_pullCount h_ne] at h_spec
    simp only [pullCount_zero] at h_spec
    exact hm h_spec.symm
  have h_pos : 0 < Nat.find h_exists := Nat.pos_of_ne_zero h_zero
  by_contra h_ne
  refine h_spec' (Nat.find h_exists - 1) ?_ ?_
  · simp [h_pos]
  rw [Nat.sub_add_cancel (by omega)]
  rwa [← pullCount_eq_pullCount]
  exact h_ne

lemma arm_eq_of_stepsUntil_eq_coe {ω : ℕ → α × ℝ} (hm : m ≠ 0)
    (h : stepsUntil a m ω = n) :
    arm n ω = a := by
  have : n = (stepsUntil a m ω).toNat := by simp [h]
  rw [this, arm_stepsUntil hm]
  by_contra! h_contra
  rw [← stepsUntil_eq_top_iff] at h_contra
  simp [h_contra] at h

lemma stepsUntil_eq_congr {h' : ℕ → α × ℝ} (h_eq : ∀ i ≤ n, arm i h = arm i h') :
    stepsUntil a m h = n ↔ stepsUntil a m h' = n := by
  sorry

lemma pullCount_stepsUntil_add_one (h_exists : ∃ s, pullCount a (s + 1) h = m) :
    pullCount a (stepsUntil a m h + 1).toNat h = m := by
  classical
  have h_eq := stepsUntil_eq_dite a m h
  simp only [h_exists, ↓reduceDIte] at h_eq
  have h' := Nat.find_spec h_exists
  rw [h_eq]
  rw [ENat.toNat_add (by simp) (by simp)]
  simp only [ENat.toNat_coe, ENat.toNat_one]
  exact h'

lemma pullCount_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount a (s + 1) h = m) :
    pullCount a (stepsUntil a m h).toNat h = m - 1 := by
  have h_arm := arm_eq_of_stepsUntil_eq_coe (n := (stepsUntil a m h).toNat) (a := a) (ω := h) hm ?_
  swap; · symm; simpa [stepsUntil_eq_top_iff]
  have h_add_one := pullCount_stepsUntil_add_one h_exists
  nth_rw 1 [← h_arm] at h_add_one
  rw [ENat.toNat_add ?_ (by simp), ENat.toNat_one, pullCount_eq_pullCount_add_one] at h_add_one
  swap; · simpa [stepsUntil_eq_top_iff]
  grind

section SumRewards

/-- Sum of rewards obtained when pulling arm `a` up to time `t` (exclusive). -/
def sumRewards (a : α) (t : ℕ) (h : ℕ → α × ℝ) : ℝ :=
  ∑ s ∈ range t, if (arm s h) = a then (reward s h) else 0

/-- Empirical mean reward obtained when pulling arm `a` up to time `t` (exclusive). -/
noncomputable
def empMean (a : α) (t : ℕ) (h : ℕ → α × ℝ) : ℝ := sumRewards a t h / pullCount a t h

lemma sumRewards_eq_pullCount_mul_empMean (h_pull : pullCount a t h ≠ 0) :
    sumRewards a t h = pullCount a t h * empMean a t h := by unfold empMean; field_simp

end SumRewards

section RewardByCount

/-- Reward obtained when pulling arm `a` for the `m`-th time. -/
noncomputable
def rewardByCount (a : α) (m : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) : ℝ :=
  match (stepsUntil a m h) with
  | ⊤ => z m a
  | (n : ℕ) => reward n h

lemma rewardByCount_eq_ite (a : α) (m : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    rewardByCount a m h z =
      if (stepsUntil a m h) = ⊤ then z m a else reward (stepsUntil a m h).toNat h := by
  unfold rewardByCount
  cases stepsUntil a m h <;> simp

lemma rewardByCount_of_stepsUntil_eq_top {ω : (ℕ → α × ℝ) × (ℕ → α → ℝ)}
    (h : stepsUntil a m ω.1 = ⊤) :
    rewardByCount a m ω.1 ω.2 = ω.2 m a := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_of_stepsUntil_eq_coe {ω : (ℕ → α × ℝ) × (ℕ → α → ℝ)}
    (h : stepsUntil a m ω.1 = n) :
    rewardByCount a m ω.1 ω.2 = reward n ω.1 := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_pullCount_add_one_eq_reward (t : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    rewardByCount (arm t h) (pullCount (arm t h) t h + 1) h z = reward t h := by
  rw [rewardByCount, ← pullCount_eq_pullCount_add_one, stepsUntil_pullCount_eq]

lemma sum_rewardByCount_eq_sumRewards
    (a : α) (t : ℕ) (h : ℕ → α × ℝ) (z : ℕ → α → ℝ) :
    ∑ m ∈ Icc 1 (pullCount a t h), rewardByCount a m h z = sumRewards a t h := by
  induction' t with t ht
  · simp [pullCount, sumRewards]
  by_cases hta : arm t h = a
  · rw [← hta] at ht ⊢
    rw [pullCount_eq_pullCount_add_one, sum_Icc_succ_top (Nat.le_add_left 1 _), ht]
    unfold sumRewards
    rw [sum_range_succ, if_pos rfl, rewardByCount_pullCount_add_one_eq_reward]
  · unfold sumRewards
    rwa [pullCount_eq_pullCount hta, sum_range_succ, if_neg hta, add_zero]

lemma sum_pullCount_mul [Fintype α] (h : ℕ → α × ℝ) (f : α → ℝ) (t : ℕ) :
    ∑ a, pullCount a t h * f a = ∑ s ∈ range t, f (arm s h) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) (arm · h) f

lemma sum_pullCount [Fintype α] : ∑ a, pullCount a t h = t := by
  suffices ∑ a, pullCount a t h * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν t h = ∑ a, pullCount a t h * gap ν a := by
  simp_rw [sum_pullCount_mul, regret, gap, sum_sub_distrib]
  simp

end RewardByCount

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

omit [DecidableEq α] in
@[simp]
lemma gap_bestArm : gap ν (bestArm ν) = 0 := by
  rw [gap_eq_bestArm_sub, sub_self]

end BestArm

end Bandits
