/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.Algorithm
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Martingale.BorelCantelli

/-!
# Bookkeeping definitions for finite action space sequential learning problems

If the number of actions is finite, it makes sense to define the number of times each action was
chosen, the time at which an action was chosen for the nth time, the value of the reward at that
time, the sum of rewards obtained for each action, the empirical mean reward for each action, etc.

For each definition that take as arguments a time `t : ℕ`, a history `h : ℕ → α × R`, and possibly
other parameters, we put the time and history at the end in this order, so that the definition can
be seen as a stochastic process indexed by time `t` on the measurable space `ℕ → α × R`.

-/

open MeasureTheory Finset

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R} [DecidableEq α]
  {a : α} {m n t : ℕ} {h : ℕ → α × R}

/-- Number of times action `a` was chosen up to time `t` (excluding `t`). -/
noncomputable
def pullCount (a : α) (t : ℕ) (h : ℕ → α × R) : ℕ :=
  #(filter (fun s ↦ action s h = a) (range t))

/-- Number of pulls of arm `a` up to (and including) time `n`.
This is the number of entries in `h` in which the arm is `a`. -/
noncomputable
def pullCount' (n : ℕ) (h : Iic n → α × R) (a : α) := #{s | (h s).1 = a}

@[simp]
lemma pullCount_zero (a : α) (h : ℕ → α × R) : pullCount a 0 h = 0 := by simp [pullCount]

lemma pullCount_one : pullCount a 1 h = if action 0 h = a then 1 else 0 := by
  simp only [pullCount, range_one]
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨0, by simp [h]⟩
  · simp [h]

lemma monotone_pullCount (a : α) (h : ℕ → α × R) : Monotone (pullCount a · h) :=
  fun _ _ _ ↦ card_le_card (filter_subset_filter _ (by simpa))

@[mono, gcongr]
lemma pullCount_mono (a : α) {n m : ℕ} (hnm : n ≤ m) (h : ℕ → α × R) :
    pullCount a n h ≤ pullCount a m h :=
  monotone_pullCount a h hnm

lemma pullCount_action_eq_pullCount_add_one (t : ℕ) (h : ℕ → α × R) :
    pullCount (action t h) (t + 1) h = pullCount (action t h) t h + 1 := by
  simp [pullCount, range_add_one, filter_insert]

lemma pullCount_eq_pullCount_of_action_ne (ha : action t h ≠ a) :
    pullCount a (t + 1) h = pullCount a t h := by
  simp [pullCount, range_add_one, filter_insert, ha]

lemma pullCount_add_one :
    pullCount a (t + 1) h = pullCount a t h + if action t h = a then 1 else 0 := by
  split_ifs with h
  · rw [← h, pullCount_action_eq_pullCount_add_one]
  · rw [pullCount_eq_pullCount_of_action_ne h, add_zero]

lemma pullCount_eq_sum (a : α) (t : ℕ) (h : ℕ → α × R) :
    pullCount a t h = ∑ s ∈ range t, if action s h = a then 1 else 0 := by simp [pullCount]

lemma pullCount'_eq_sum (n : ℕ) (h : Iic n → α × R) (a : α) :
    pullCount' n h a = ∑ s : Iic n, if (h s).1 = a then 1 else 0 := by simp [pullCount']

lemma pullCount_add_one_eq_pullCount' {n : ℕ} {h : ℕ → α × R} :
    pullCount a (n + 1) h = pullCount' n (fun i ↦ h i) a := by
  rw [pullCount_eq_sum, pullCount'_eq_sum]
  unfold action
  rw [Finset.sum_coe_sort (f := fun s ↦ if (h s).1 = a then 1 else 0) (Iic n)]
  congr with m
  simp only [mem_range, mem_Iic]
  grind

lemma pullCount_eq_pullCount' {n : ℕ} {h : ℕ → α × R} (hn : n ≠ 0) :
    pullCount a n h = pullCount' (n - 1) (fun i ↦ h i) a := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    rw [pullCount_add_one_eq_pullCount']
    have : n + 1 - 1 = n := by simp
    exact this ▸ rfl

lemma pullCount_le (a : α) (t : ℕ) (h : ℕ → α × R) : pullCount a t h ≤ t :=
  (card_filter_le _ _).trans_eq (by simp)

lemma pullCount_congr {h' : ℕ → α × R} (h_eq : ∀ i ≤ n, action i h = action i h') :
    pullCount a (n + 1) h = pullCount a (n + 1) h' := by
  unfold pullCount
  congr 1 with s
  simp only [mem_filter, mem_range, and_congr_right_iff]
  intro hs
  rw [Nat.lt_add_one_iff] at hs
  rw [h_eq s hs]

@[fun_prop]
lemma measurable_pullCount [MeasurableSingletonClass α] (a : α) (t : ℕ) :
    Measurable (fun h : ℕ → α × R ↦ pullCount a t h) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun h : ℕ → α × R ↦ if action s h = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_pullCount' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h : Iic n → α × R ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Iic n → α × R) ↦ if (h s).1 = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

-- TODO: replace this by leastGE
/-- Number of steps until action `a` was pulled exactly `m` times. -/
noncomputable
def stepsUntil (a : α) (m : ℕ) (h : ℕ → α × R) : ℕ∞ := sInf ((↑) '' {s | pullCount a (s + 1) h = m})

lemma stepsUntil_eq_top_iff : stepsUntil a m h = ⊤ ↔ ∀ s, pullCount a (s + 1) h ≠ m := by
  simp [stepsUntil, sInf_eq_top]

lemma stepsUntil_ne_top (h_exists : ∃ s, pullCount a (s + 1) h = m) : stepsUntil a m h ≠ ⊤ := by
  simpa [stepsUntil_eq_top_iff]

-- todo: this is in ℝ because of the limited def of leastGE
lemma stepsUntil_eq_leastGE (a : α) (m : ℕ) :
    stepsUntil a m = leastGE (fun n (h : ℕ → α × ℝ) ↦ pullCount a (n + 1) h) m := by
  sorry

lemma exists_pullCount_eq (h' : stepsUntil a m h ≠ ⊤) :
    ∃ s, pullCount a (s + 1) h = m := by
  by_contra! h_contra
  rw [← stepsUntil_eq_top_iff] at h_contra
  simp [h_contra] at h'

lemma stepsUntil_zero_of_ne (hka : action 0 h ≠ a) : stepsUntil a 0 h = 0 := by
  unfold stepsUntil
  simp_rw [← bot_eq_zero, sInf_eq_bot, bot_eq_zero]
  intro n hn
  refine ⟨0, ?_, hn⟩
  simp only [Set.mem_image, Set.mem_setOf_eq, Nat.cast_eq_zero, exists_eq_right, zero_add]
  rw [← zero_add 1, pullCount_eq_pullCount_of_action_ne hka]
  simp

lemma stepsUntil_zero_of_eq (hka : action 0 h = a) : stepsUntil a 0 h = ⊤ := by
  rw [stepsUntil_eq_top_iff]
  suffices 0 < pullCount a 1 h by
    intro n hn
    refine lt_irrefl 0 ?_
    exact this.trans_le (le_trans (monotone_pullCount _ _ (by omega)) hn.le)
  rw [← hka, ← zero_add 1, pullCount_action_eq_pullCount_add_one]
  simp

lemma stepsUntil_eq_dite (a : α) (m : ℕ) (h : ℕ → α × R)
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

lemma stepsUntil_pullCount_le (h : ℕ → α × R) (a : α) (t : ℕ) :
    stepsUntil a (pullCount a (t + 1) h) h ≤ t := by
  rw [stepsUntil]
  exact csInf_le (OrderBot.bddBelow _) ⟨t, rfl, rfl⟩

lemma stepsUntil_pullCount_eq (h : ℕ → α × R) (t : ℕ) :
    stepsUntil (action t h) (pullCount (action t h) (t + 1) h) h = t := by
  apply le_antisymm (stepsUntil_pullCount_le h (action t h) t)
  suffices ∀ t', pullCount (action t h) (t' + 1) h = pullCount (action t h) t h + 1 → t ≤ t' by
    simpa [stepsUntil, pullCount_action_eq_pullCount_add_one]
  exact fun t' h' ↦ Nat.le_of_lt_succ ((monotone_pullCount (action t h) h).reflect_lt
    (h' ▸ lt_add_one _))

/-- If we pull action `a` at time 0, the first time at which it is pulled once is 0. -/
lemma stepsUntil_one_of_eq (hka : action 0 h = a) : stepsUntil a 1 h = 0 := by
  classical
  have h_pull : pullCount a 1 h = 1 := by simp [pullCount_one, hka]
  have h_le := stepsUntil_pullCount_le h a 0
  simpa [h_pull] using h_le

lemma stepsUntil_eq_zero_iff :
    stepsUntil a m h = 0 ↔ (m = 0 ∧ action 0 h ≠ a) ∨ (m = 1 ∧ action 0 h = a) := by
  classical
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have h_exists : ∃ s, pullCount a (s + 1) h = m := exists_pullCount_eq (by simp [h'])
    simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, Nat.cast_eq_zero, Nat.find_eq_zero,
      zero_add] at h'
    rw [pullCount_one] at h'
    by_cases hka : action 0 h = a
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

lemma action_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount a (s + 1) h = m) :
    action (stepsUntil a m h).toNat h = a := by
  classical
  simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, ENat.toNat_coe]
  have h_spec := Nat.find_spec h_exists
  have h_spec' n := Nat.find_min h_exists (m := n)
  by_cases h_zero : Nat.find h_exists = 0
  · simp only [h_zero, zero_add, not_lt_zero', IsEmpty.forall_iff, implies_true] at *
    by_contra h_ne
    rw [← zero_add 1, pullCount_eq_pullCount_of_action_ne h_ne] at h_spec
    simp only [pullCount_zero] at h_spec
    exact hm h_spec.symm
  have h_pos : 0 < Nat.find h_exists := Nat.pos_of_ne_zero h_zero
  by_contra h_ne
  refine h_spec' (Nat.find h_exists - 1) ?_ ?_
  · simp [h_pos]
  rw [Nat.sub_add_cancel (by omega)]
  rwa [← pullCount_eq_pullCount_of_action_ne]
  exact h_ne

lemma action_eq_of_stepsUntil_eq_coe {ω : ℕ → α × R} (hm : m ≠ 0)
    (h : stepsUntil a m ω = n) :
    action n ω = a := by
  have : n = (stepsUntil a m ω).toNat := by simp [h]
  rw [this, action_stepsUntil hm]
  exact exists_pullCount_eq (by simp [h])

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
  have h_action := action_eq_of_stepsUntil_eq_coe (n := (stepsUntil a m h).toNat) (a := a) (ω := h)
    hm ?_
  swap; · symm; simpa [stepsUntil_eq_top_iff]
  have h_add_one := pullCount_stepsUntil_add_one h_exists
  nth_rw 1 [← h_action] at h_add_one
  rw [ENat.toNat_add ?_ (by simp), ENat.toNat_one, pullCount_action_eq_pullCount_add_one]
    at h_add_one
  swap; · simpa [stepsUntil_eq_top_iff]
  grind

lemma pullCount_lt_of_le_stepsUntil (a : α) {n m : ℕ} (h : ℕ → α × R)
    (h_exists : ∃ s, pullCount a (s + 1) h = m) (hn : n < stepsUntil a m h) :
    pullCount a (n + 1) h < m := by
  classical
  have h_eq := stepsUntil_eq_dite a m h
  simp only [h_exists, ↓reduceDIte] at h_eq
  rw [← ENat.coe_toNat (stepsUntil_ne_top h_exists)] at hn
  refine lt_of_le_of_ne ?_ ?_
  · calc pullCount a (n + 1) h
    _ ≤ pullCount a (stepsUntil a m h + 1).toNat h := by
      refine monotone_pullCount a h ?_
      rw [ENat.toNat_add (stepsUntil_ne_top h_exists) (by simp)]
      simp only [ENat.toNat_one, add_le_add_iff_right]
      exact mod_cast hn.le
    _ = m := pullCount_stepsUntil_add_one h_exists
  · refine Nat.find_min h_exists (m := n) ?_
    suffices n < (stepsUntil a m h).toNat by
      rwa [h_eq, ENat.toNat_coe] at this
    exact mod_cast hn

lemma pullCount_eq_of_stepsUntil_eq_coe {ω : ℕ → α × R} (hm : m ≠ 0)
    (h : stepsUntil a m ω = n) :
    pullCount a n ω = m - 1 := by
  have : n = (stepsUntil a m ω).toNat := by simp [h]
  rw [this, pullCount_stepsUntil hm]
  exact exists_pullCount_eq (by simp [h])

lemma pullCount_add_one_eq_of_stepsUntil_eq_coe {ω : ℕ → α × R}
    (h : stepsUntil a m ω = n) :
    pullCount a (n + 1) ω = m := by
  have : n + 1 = (stepsUntil a m ω + 1).toNat := by
    rw [ENat.toNat_add (by simp [h]) (by simp)]; simp [h]
  rw [this, pullCount_stepsUntil_add_one]
  exact exists_pullCount_eq (by simp [h])

lemma stepsUntil_eq_iff {ω : ℕ → α × R} (n : ℕ) :
    stepsUntil a m ω = n ↔
      pullCount a (n + 1) ω = m ∧ (∀ k < n, pullCount a (k + 1) ω < m) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h_exists : ∃ s, pullCount a (s + 1) ω = m := exists_pullCount_eq (by simp [h])
    refine ⟨pullCount_add_one_eq_of_stepsUntil_eq_coe h, fun k hk ↦ ?_⟩
    exact pullCount_lt_of_le_stepsUntil a ω h_exists (by rw [h]; exact mod_cast hk)
  · classical
    rw [stepsUntil_eq_dite a m ω, dif_pos ⟨n, h.1⟩]
    simp only [Nat.cast_inj]
    rw [Nat.find_eq_iff]
    exact ⟨h.1, fun k hk ↦ (h.2 k hk).ne⟩

lemma stepsUntil_eq_congr {h' : ℕ → α × R} (h_eq : ∀ i ≤ n, action i h = action i h') :
    stepsUntil a m h = n ↔ stepsUntil a m h' = n := by
  simp_rw [stepsUntil_eq_iff n]
  congr! 1
  · rw [pullCount_congr h_eq]
  · congr! 3 with k hk
    rw [pullCount_congr]
    grind

section RewardByCount

/-- Reward obtained when pulling action `a` for the `m`-th time.
If it is never pulled `m` times, the reward is given by the second component of `ω`, which in
applications will be indepedent with same law. -/
noncomputable
def rewardByCount (a : α) (m : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) : R :=
  match (stepsUntil a m ω.1) with
  | ⊤ => ω.2 m a
  | (n : ℕ) => reward n ω.1

lemma rewardByCount_eq_ite (a : α) (m : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) :
    rewardByCount a m ω =
      if (stepsUntil a m ω.1) = ⊤ then ω.2 m a else reward (stepsUntil a m ω.1).toNat ω.1 := by
  unfold rewardByCount
  cases stepsUntil a m ω.1 <;> simp

lemma rewardByCount_of_stepsUntil_eq_top {ω : (ℕ → α × R) × (ℕ → α → R)}
    (h : stepsUntil a m ω.1 = ⊤) :
    rewardByCount a m ω = ω.2 m a := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_of_stepsUntil_eq_coe {ω : (ℕ → α × R) × (ℕ → α → R)}
    (h : stepsUntil a m ω.1 = n) :
    rewardByCount a m ω = reward n ω.1 := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_pullCount_add_one_eq_reward (t : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) :
    rewardByCount (action t ω.1) (pullCount (action t ω.1) t ω.1 + 1) ω = reward t ω.1 := by
  rw [rewardByCount, ← pullCount_action_eq_pullCount_add_one, stepsUntil_pullCount_eq]

end RewardByCount

lemma sum_pullCount_mul [Fintype α] [Semiring R] (h : ℕ → α × R) (f : α → R) (t : ℕ) :
    ∑ a, pullCount a t h * f a = ∑ s ∈ range t, f (action s h) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) (action · h) f

-- todo: only in ℝ for now
lemma sum_pullCount [Fintype α] {h : ℕ → α × ℝ} : ∑ a, pullCount a t h = t := by
  suffices ∑ a, pullCount a t h * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

section SumRewards

/-- Sum of rewards obtained when pulling action `a` up to time `t` (exclusive). -/
def sumRewards (a : α) (t : ℕ) (h : ℕ → α × ℝ) : ℝ :=
  ∑ s ∈ range t, if action s h = a then reward s h else 0

/-- Sum of rewards of arm `a` up to (and including) time `n`. -/
noncomputable
def sumRewards' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  ∑ s, if (h s).1 = a then (h s).2 else 0

/-- Empirical mean reward obtained when pulling action `a` up to time `t` (exclusive). -/
noncomputable
def empMean (a : α) (t : ℕ) (h : ℕ → α × ℝ) : ℝ := sumRewards a t h / pullCount a t h

/-- Empirical mean of arm `a` at time `n`. -/
noncomputable
def empMean' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  (sumRewards' n h a) / (pullCount' n h a)

lemma sumRewards_eq_pullCount_mul_empMean {h : ℕ → α × ℝ} (h_pull : pullCount a t h ≠ 0) :
    sumRewards a t h = pullCount a t h * empMean a t h := by unfold empMean; field_simp

lemma sum_rewardByCount_eq_sumRewards (a : α) (t : ℕ) (ω : (ℕ → α × ℝ) × (ℕ → α → ℝ)) :
    ∑ m ∈ Icc 1 (pullCount a t ω.1), rewardByCount a m ω = sumRewards a t ω.1 := by
  induction t with
  | zero => simp [pullCount, sumRewards]
  | succ t ht =>
    by_cases hta : action t ω.1 = a
    · rw [← hta] at ht ⊢
      rw [pullCount_action_eq_pullCount_add_one, sum_Icc_succ_top (Nat.le_add_left 1 _), ht]
      unfold sumRewards
      rw [sum_range_succ, if_pos rfl, rewardByCount_pullCount_add_one_eq_reward]
    · unfold sumRewards
      rwa [pullCount_eq_pullCount_of_action_ne hta, sum_range_succ, if_neg hta, add_zero]

lemma sumRewards_add_one_eq_sumRewards' {n : ℕ} {h : ℕ → α × ℝ} :
    sumRewards a (n + 1) h = sumRewards' n (fun i ↦ h i) a := by
  unfold sumRewards sumRewards' action Learning.reward
  rw [Finset.sum_coe_sort (f := fun s ↦ if (h s).1 = a then (h s).2 else 0) (Iic n)]
  congr with m
  simp only [mem_range, mem_Iic]
  grind

lemma sumRewards_eq_sumRewards' {n : ℕ} {h : ℕ → α × ℝ} (hn : n ≠ 0) :
    sumRewards a n h = sumRewards' (n - 1) (fun i ↦ h i) a := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    rw [sumRewards_add_one_eq_sumRewards']
    have : n + 1 - 1 = n := by simp
    exact this ▸ rfl

lemma empMean_add_one_eq_empMean' {n : ℕ} {h : ℕ → α × ℝ} :
    empMean a (n + 1) h = empMean' n (fun i ↦ h i) a := by
  unfold empMean empMean'
  rw [sumRewards_add_one_eq_sumRewards', pullCount_add_one_eq_pullCount']

lemma empMean_eq_empMean' {n : ℕ} {h : ℕ → α × ℝ} (hn : n ≠ 0) :
    empMean a n h = empMean' (n - 1) (fun i ↦ h i) a := by
  unfold empMean empMean'
  rw [sumRewards_eq_sumRewards' hn, pullCount_eq_pullCount' hn]

@[fun_prop]
lemma measurable_sumRewards' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ sumRewards' n h a) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then (h s).2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ empMean' n h a) := by
  unfold empMean'
  fun_prop

end SumRewards

end Learning
