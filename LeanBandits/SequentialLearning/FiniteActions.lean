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

section PullCount

/-- Number of times action `a` was chosen up to time `t` (excluding `t`). -/
noncomputable
def pullCount (a : α) (t : ℕ) (h : ℕ → α × R) : ℕ :=
  #(filter (fun s ↦ action s h = a) (range t))

/-- Number of pulls of arm `a` up to (and including) time `n`.
This is the number of entries in `h` in which the arm is `a`. -/
noncomputable
def pullCount' (n : ℕ) (h : Iic n → α × R) (a : α) := #{s | (h s).1 = a}

@[simp]
lemma pullCount_zero (a : α) : pullCount a 0 (R := R) = 0 := by ext; simp [pullCount]

lemma pullCount_zero_apply (a : α) (h : ℕ → α × R) : pullCount a 0 h = 0 := by simp

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

lemma pullCount_lt_of_forall_ne (h_lt : ∀ s, pullCount a (s + 1) h ≠ t) (ht : t ≠ 0) :
    pullCount a n h < t := by
  induction n with
  | zero => simpa using ht.bot_lt
  | succ n hn =>
    specialize h_lt n
    rw [pullCount_add_one] at h_lt ⊢
    grind

lemma exists_pullCount_eq_of_le (hnm : t ≤ pullCount a (n + 1) h) (ht : t ≠ 0) :
    ∃ s, pullCount a (s + 1) h = t := by
  by_contra! h_contra
  refine lt_irrefl (pullCount a (n + 1) h) ?_
  refine lt_of_lt_of_le ?_ hnm
  exact pullCount_lt_of_forall_ne h_contra ht

section Measurability

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

lemma adapted_pullCount_add_one [MeasurableSingletonClass α] (a : α) :
    Adapted (Learning.filtration α R) (fun n ↦ pullCount a (n + 1)) := by
  refine fun n ↦ Measurable.stronglyMeasurable ?_
  simp only
  have : pullCount a (n + 1) = (fun h : Iic n → α × R ↦ pullCount' n h a) ∘ (hist n) := by
    ext
    exact pullCount_add_one_eq_pullCount'
  rw [Learning.filtration, Filtration.piLE_eq_comap_frestrictLe, ← hist_eq_frestrictLe, this]
  exact measurable_comp_comap (hist n) (measurable_pullCount' n a)

lemma isPredictable_pullCount [MeasurableSingletonClass α] (a : α) :
    IsPredictable (Learning.filtration α R) (pullCount a) := by
  rw [isPredictable_iff_measurable_add_one]
  refine ⟨?_, fun n ↦ (adapted_pullCount_add_one a n).measurable⟩
  simp only [pullCount_zero]
  fun_prop

end Measurability

end PullCount

section StepsUntil

-- TODO: replace this by leastGE, once leastGE is generalized
/-- Number of steps until action `a` was pulled exactly `m` times. -/
noncomputable
def stepsUntil (a : α) (m : ℕ) (h : ℕ → α × R) : ℕ∞ := sInf ((↑) '' {s | pullCount a (s + 1) h = m})

lemma stepsUntil_eq_top_iff : stepsUntil a m h = ⊤ ↔ ∀ s, pullCount a (s + 1) h ≠ m := by
  simp [stepsUntil, sInf_eq_top]

lemma stepsUntil_ne_top (h_exists : ∃ s, pullCount a (s + 1) h = m) : stepsUntil a m h ≠ ⊤ := by
  simpa [stepsUntil_eq_top_iff]

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

-- todo: this is in ℝ because of the limited def of leastGE
lemma stepsUntil_eq_leastGE (a : α) (hm : m ≠ 0) :
    stepsUntil a m = leastGE (fun n (h : ℕ → α × ℝ) ↦ pullCount a (n + 1) h) m := by
  classical
  ext h
  rw [stepsUntil_eq_dite]
  unfold leastGE hittingAfter
  simp only [zero_le, Set.mem_Ici, Nat.cast_le, true_and, ENat.some_eq_coe]
  have h_iff : (∃ s, pullCount a (s + 1) h = m) ↔ (∃ s, m ≤ pullCount a (s + 1) h) := by
    refine ⟨fun ⟨s, hs⟩ ↦ ⟨s, hs.ge⟩, fun ⟨s, hs⟩ ↦ ?_⟩
    exact exists_pullCount_eq_of_le hs hm
  by_cases h_exists : ∃ s, m ≤ pullCount a (s + 1) h
  swap; · simp_rw [h_iff]; simp [h_exists]
  rw [if_pos h_exists, dif_pos]
  swap; · rwa [h_iff]
  norm_cast
  rw [Nat.find_eq_iff]
  constructor
  · apply le_antisymm
    · by_contra! h_contra
      obtain ⟨s, hs⟩ : ∃ s, pullCount a (s + 1) h = m := exists_pullCount_eq_of_le h_contra.le hm
      rw [← hs] at h_contra
      refine h_contra.not_ge ?_
      gcongr
      exact csInf_le (by simp) (by simp)
    · exact Nat.sInf_mem (s := {j | m ≤ pullCount a (j + 1) h}) h_exists
  · intro n hn h_contra
    refine hn.not_ge ?_
    exact csInf_le (by simp) (by simp [h_contra])

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

section Measurability

lemma isStoppingTime_stepsUntil [MeasurableSingletonClass α] (a : α) (hm : m ≠ 0) :
    IsStoppingTime (Learning.filtration α ℝ) (stepsUntil a m) := by
  rw [stepsUntil_eq_leastGE _ hm]
  refine Adapted.isStoppingTime_leastGE _ fun n ↦ ?_
  suffices StronglyMeasurable[Learning.filtration α ℝ n] (pullCount a (n + 1)) by fun_prop
  exact adapted_pullCount_add_one a n

-- todo: get this from the stopping time property?
@[fun_prop]
lemma measurable_stepsUntil [MeasurableSingletonClass α] (a : α) (m : ℕ) :
    Measurable (fun h : ℕ → α × R ↦ stepsUntil a m h) := by
  classical
  have h_union : {h' : ℕ → α × R | ∃ s, pullCount a (s + 1) h' = m}
      = ⋃ s : ℕ, {h' | pullCount a (s + 1) h' = m} := by ext; simp
  have h_meas_set : MeasurableSet {h' : ℕ → α × R | ∃ s, pullCount a (s + 1) h' = m} := by
    rw [h_union]
    exact MeasurableSet.iUnion fun s ↦ (measurableSet_singleton _).preimage (by fun_prop)
  simp_rw [stepsUntil_eq_dite]
  suffices Measurable fun k ↦ if h : k ∈ {k' | ∃ s, pullCount a (s + 1) k' = m}
      then (Nat.find h : ℕ∞) else ⊤ by convert this
  refine Measurable.dite (s := {k' : ℕ → α × R | ∃ s, pullCount a (s + 1) k' = m})
    (f := fun x ↦ (Nat.find x.2 : ℕ∞)) (g := fun _ ↦ ⊤) ?_ (by fun_prop) h_meas_set
  refine Measurable.coe_nat_enat ?_
  refine measurable_find _ fun k ↦ ?_
  suffices MeasurableSet {x : ℕ → α × R | pullCount a (k + 1) x = m} by
    have : Subtype.val '' {x : {k' : ℕ → α × R |
          ∃ s, pullCount a (s + 1) k' = m} | pullCount a (k + 1) (x : ℕ → α × R) = m}
        = {x : ℕ → α × R | pullCount a (k + 1) x = m} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.coe_setOf, Set.mem_image, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
      exact fun h ↦ ⟨_, h⟩
    refine (MeasurableEmbedding.subtype_coe h_meas_set).measurableSet_image.mp ?_
    rw [this]
    exact (measurableSet_singleton _).preimage (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_stepsUntil' [MeasurableSingletonClass α] (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × R) × (ℕ → α → R) ↦ stepsUntil a m ω.1) :=
  (measurable_stepsUntil a m).comp measurable_fst

lemma measurable_comap_indicator_stepsUntil_eq [Nonempty R] [MeasurableSingletonClass α]
    (a : α) (m n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω : ℕ → α × R ↦ (hist (n-1) ω, action n ω)) inferInstance]
      ({ω | stepsUntil a m ω = ↑n}.indicator fun _ ↦ 1) := by
  let r₀ : R := Nonempty.some inferInstance
  let k : ((Iic (n - 1) → α × R) × α) → (ℕ → α × R) := fun x i ↦
    if hi : i ∈ Iic (n - 1) then (x.1 ⟨i, hi⟩) else if i = n then (x.2, r₀) else (a, r₀)
  have hk : Measurable k := by
    unfold k
    rw [measurable_pi_iff]
    intro i
    split_ifs <;> fun_prop
  let φ : ((Iic (n - 1) → α × R) × α) → ℕ := fun x ↦ if stepsUntil a m (k x) = ↑n then 1 else 0
  have hφ : Measurable φ :=
    Measurable.ite ((measurableSet_singleton _).preimage (by fun_prop)) (by fun_prop) (by fun_prop)
  suffices {ω | stepsUntil a m ω = ↑n}.indicator (fun x ↦ 1)
      = φ ∘ fun ω ↦ (hist (n - 1) ω, action n ω) from this ▸ measurable_comp_comap _ hφ
  ext ω
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, φ]
  congr 1
  rw [stepsUntil_eq_congr]
  intro i hin
  simp only [action, mem_Iic, hist, dite_eq_ite, k, action]
  grind

lemma measurable_indicator_stepsUntil_eq [Nonempty R] [MeasurableSingletonClass α]
    (a : α) (m n : ℕ) :
    Measurable ({ω : ℕ → α × R | stepsUntil a m ω = ↑n}.indicator fun _ ↦ 1) := by
  refine (measurable_comap_indicator_stepsUntil_eq (mR := mR) a m n).mono ?_ le_rfl
  refine Measurable.comap_le ?_
  fun_prop

lemma measurableSet_stepsUntil_eq_zero [Nonempty R] [MeasurableSingletonClass α] (a : α) (m : ℕ) :
    MeasurableSet[MeasurableSpace.comap (action 0) inferInstance]
      {ω : ℕ → α × R | stepsUntil a m ω = 0} := by
  simp only [stepsUntil_eq_zero_iff (a := a) (m := m), ne_eq]
  by_cases hm : m = 0
  · simp only [hm, true_and, zero_ne_one, false_and, or_false]
    refine (measurableSet_singleton _).compl.preimage ?_
    rw [measurable_iff_comap_le]
  by_cases hm1 : m = 1
  swap; · simp [hm, hm1]
  simp only [hm1, one_ne_zero, false_and, true_and, false_or]
  refine (measurableSet_singleton _).preimage ?_
  rw [measurable_iff_comap_le]

lemma measurableSet_stepsUntil_eq [Nonempty R] [MeasurableSingletonClass α] (a : α) (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω : ℕ → α × R ↦ (hist (n-1) ω, action n ω))
        inferInstance]
      {ω : ℕ → α × R | stepsUntil a m ω = ↑n} := by
  let mProd := MeasurableSpace.comap (fun ω : ℕ → α × R ↦ (hist (n-1) ω, action n ω)) inferInstance
  suffices Measurable[mProd] ({ω | stepsUntil a m ω = ↑n}.indicator fun x ↦ 1) by
    rwa [measurable_indicator_const_iff] at this
  exact measurable_comap_indicator_stepsUntil_eq a m n

/-- `stepsUntil a m` is a stopping time with respect to the filtration `filtrationAction`. -/
theorem isStoppingTime_stepsUntil_filtrationAction [Nonempty R] [MeasurableSingletonClass α]
    (a : α) (m : ℕ) :
    IsStoppingTime (filtrationAction α R) (stepsUntil a m) := by
  refine isStoppingTime_of_measurableSet_eq fun n ↦ ?_
  by_cases hn : n = 0
  · simp only [hn, filtrationAction_zero_eq_comap, WithTop.coe_zero]
    exact measurableSet_stepsUntil_eq_zero a m
  · rw [filtrationAction_eq_comap _ hn]
    exact measurableSet_stepsUntil_eq a m n

-- /-- Sigma-algebra generated by the stopping time `stepsUntil a m`. -/
-- def stepsUntilMeasurableSpace [Nonempty R] [MeasurableSingletonClass α] (a : α) (m : ℕ) :
--     MeasurableSpace (ℕ → α × R) :=
--   (isStoppingTime_stepsUntil_filtrationAction a m (mR := mR)).measurableSpace

end Measurability

end StepsUntil

section RewardByCount

/-- Reward obtained when pulling action `a` for the `m`-th time.
If it is never pulled `m` times, the reward is given by the second component of `ω`, which in
applications will be indepedent with same law. -/
noncomputable
def rewardByCount (a : α) (m : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) : R :=
  match (stepsUntil a m ω.1) with
  | ⊤ => ω.2 m a
  | (n : ℕ) => reward n ω.1

variable {ω : (ℕ → α × R) × (ℕ → α → R)}

lemma rewardByCount_eq_ite (a : α) (m : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) :
    rewardByCount a m ω =
      if (stepsUntil a m ω.1) = ⊤ then ω.2 m a else reward (stepsUntil a m ω.1).toNat ω.1 := by
  unfold rewardByCount
  cases stepsUntil a m ω.1 <;> simp

lemma rewardByCount_of_stepsUntil_eq_top (h : stepsUntil a m ω.1 = ⊤) :
    rewardByCount a m ω = ω.2 m a := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_of_stepsUntil_ne_top (h : stepsUntil a m ω.1 ≠ ⊤) :
    rewardByCount a m ω = reward (stepsUntil a m ω.1).toNat ω.1 := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_eq_stoppedValue (h : stepsUntil a m ω.1 ≠ ⊤) :
    rewardByCount a m ω = stoppedValue reward (stepsUntil a m) ω.1 := by
  rw [rewardByCount_of_stepsUntil_ne_top h, stoppedValue]
  lift stepsUntil a m ω.1 to ℕ using h with n
  simp

lemma rewardByCount_of_stepsUntil_eq_coe (h : stepsUntil a m ω.1 = n) :
    rewardByCount a m ω = reward n ω.1 := by simp [rewardByCount_eq_ite, h]

/-- The value at 0 does not matter (it would be the "zeroth" reward).
It should be considered a junk value. -/
@[simp]
lemma rewardByCount_zero (a : α) (ω : (ℕ → α × R) × (ℕ → α → R)) :
    rewardByCount a 0 ω = if action 0 ω.1 = a then ω.2 0 a else reward 0 ω.1 := by
  rw [rewardByCount_eq_ite]
  by_cases ha : action 0 ω.1 = a
  · simp [ha, stepsUntil_zero_of_eq]
  · simp [stepsUntil_zero_of_ne, ha]

lemma rewardByCount_pullCount_add_one_eq_reward (t : ℕ) (ω : (ℕ → α × R) × (ℕ → α → R)) :
    rewardByCount (action t ω.1) (pullCount (action t ω.1) t ω.1 + 1) ω = reward t ω.1 := by
  rw [rewardByCount, ← pullCount_action_eq_pullCount_add_one, stepsUntil_pullCount_eq]

@[fun_prop]
lemma measurable_rewardByCount [MeasurableSingletonClass α] (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × R) × (ℕ → α → R) ↦ rewardByCount a m ω) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' a m
  · fun_prop
  · change Measurable ((fun p : ℕ × (ℕ → α × R) ↦ reward p.1 p.2)
      ∘ (fun ω : (ℕ → α × R) × (ℕ → α → R) ↦ ((stepsUntil a m ω.1).toNat, ω.1)))
    have : Measurable fun ω : (ℕ → α × R) × (ℕ → α → R) ↦ ((stepsUntil a m ω.1).toNat, ω.1) :=
      (measurable_stepsUntil' a m).toNat.prodMk (by fun_prop)
    exact Measurable.comp (by fun_prop) this

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
lemma measurable_sumRewards [MeasurableSingletonClass α] (a : α) (t : ℕ) :
    Measurable (sumRewards a t) := by
  unfold sumRewards
  have h_meas s : Measurable (fun h : ℕ → α × ℝ ↦ if action s h = a then reward s h else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean [MeasurableSingletonClass α] (a : α) (n : ℕ) :
    Measurable (empMean a n) := by
  unfold empMean
  fun_prop

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
