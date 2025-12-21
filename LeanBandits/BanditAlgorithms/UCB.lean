/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.AlgorithmAndRandomVariables
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.RewardByCountMeasure

/-!
# UCB algorithm

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

-- not used
lemma predictatble_pullCount (a : Fin K) :
    Adapted (Bandits.filtration (Fin K) ℝ) (fun n ↦ pullCount a (n + 1)) := by
  refine fun n ↦ Measurable.stronglyMeasurable ?_
  simp only
  have : pullCount a (n + 1) = (fun h ↦ pullCount' n h a) ∘ (hist n) := by
    ext
    exact pullCount_add_one_eq_pullCount'
  rw [Bandits.filtration, Filtration.piLE_eq_comap_frestrictLe, ← hist_eq_frestrictLe, this]
  exact measurable_comp_comap (hist n) (measurable_pullCount' n a)

-- not used
lemma isStoppingTime_stepsUntil (a : Fin K) (m : ℕ) :
    IsStoppingTime (Bandits.filtration (Fin K) ℝ) (stepsUntil a m) := by
  rw [stepsUntil_eq_leastGE]
  refine Adapted.isStoppingTime_leastGE _ fun n ↦ ?_
  suffices StronglyMeasurable[Bandits.filtration (Fin K) ℝ n] (pullCount a (n + 1)) by fun_prop
  exact predictatble_pullCount a n

section Algorithm

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth' (c : ℝ) (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  √(c * log (n + 2) / pullCount' n h a)

open Classical in
/-- Arm pulled by the UCB algorithm at time `n + 1`. -/
noncomputable
def UCB.nextArm (hK : 0 < K) (c : ℝ) (n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if n < K - 1 then ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ else
  measurableArgmax (fun h a ↦ empMean' n h a + ucbWidth' c n h a) h

@[fun_prop]
lemma UCB.measurable_nextArm (hK : 0 < K) (c : ℝ) (n : ℕ) : Measurable (nextArm hK c n) := by
  refine Measurable.ite (by simp) (by fun_prop) ?_
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  refine measurable_measurableArgmax fun a ↦ ?_
  unfold ucbWidth'
  fun_prop

/-- The UCB algorithm. -/
noncomputable
def ucbAlgorithm (hK : 0 < K) (c : ℝ) : Algorithm (Fin K) ℝ :=
  detAlgorithm (UCB.nextArm hK c) (by fun_prop) ⟨0, hK⟩

end Algorithm

namespace UCB

variable {hK : 0 < K} {c : ℝ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν] {n : ℕ} {h : ℕ → Fin K × ℝ}

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth (c : ℝ) (a : Fin K) (n : ℕ) (h : ℕ → Fin K × ℝ) : ℝ :=
  √(c * log (n + 1) / pullCount a n h)

lemma ucbWidth_eq_ucbWidth' (c : ℝ) (a : Fin K) (n : ℕ) (h : ℕ → Fin K × ℝ) (hn : n ≠ 0) :
    ucbWidth c a n h = ucbWidth' c (n - 1) (fun i ↦ h i) a := by
  simp only [ucbWidth, pullCount_eq_pullCount' hn, Nat.cast_nonneg, sqrt_div', ucbWidth']
  congr 4
  norm_cast
  grind

local notation "𝔓t" => Bandit.trajMeasure (ucbAlgorithm hK c) ν
local notation "𝔓" => Bandit.measure (ucbAlgorithm hK c) ν

lemma arm_zero : arm 0 =ᵐ[𝔓t] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_zero_detAlgorithm

lemma arm_ae_eq_ucbNextArm (n : ℕ) :
    arm (n + 1) =ᵐ[𝔓t] fun h ↦ nextArm hK c n (fun i ↦ h i) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_detAlgorithm_ae_eq n

lemma ucbIndex_le_ucbIndex_arm (a : Fin K) (hn : K ≤ n) :
    ∀ᵐ h ∂𝔓t, empMean a n h + ucbWidth c a n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h := by
  filter_upwards [arm_ae_eq_ucbNextArm (n - 1)] with h h_arm
  have : n - 1 + 1 = n := by grind
  have h_not_lt : ¬ n - 1 < K - 1 := by grind
  simp only [this, nextArm, h_not_lt, ↓reduceIte] at h_arm
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  simp_rw [h_arm, empMean_eq_empMean' (by grind : n ≠ 0),
    ucbWidth_eq_ucbWidth' _ _ _ _ (by grind : n ≠ 0)]
  exact isMaxOn_measurableArgmax (fun h a ↦ empMean' (n - 1) h a + ucbWidth' c (n - 1) h a)
    (fun i ↦ h i) a

omit [IsMarkovKernel ν] in
lemma gap_arm_le_two_mul_ucbWidth [Nonempty (Fin K)]
    (h_best : (ν (bestArm ν))[id] ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h)
    (h_arm : empMean (arm n h) n h - ucbWidth c (arm n h) n h ≤ (ν (arm n h))[id])
    (h_le : empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h) :
    gap ν (arm n h) ≤ 2 * ucbWidth c (arm n h) n h := by
  rw [gap_eq_bestArm_sub, sub_le_iff_le_add']
  calc (ν (bestArm ν))[id]
  _ ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h := h_best
  _ ≤ empMean (arm n h) n h + ucbWidth c (arm n h) n h := h_le
  _ ≤ (ν (arm n h))[id] + 2 * ucbWidth c (arm n h) n h := by
    rw [two_mul, ← add_assoc]
    gcongr
    rwa [sub_le_iff_le_add] at h_arm

omit [IsMarkovKernel ν] in
lemma pullCount_arm_le [Nonempty (Fin K)] (hc : 0 ≤ c)
    (h_best : (ν (bestArm ν))[id] ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h)
    (h_arm : empMean (arm n h) n h - ucbWidth c (arm n h) n h ≤ (ν (arm n h))[id])
    (h_le : empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h)
    (h_gap_pos : 0 < gap ν (arm n h)) (h_pull_pos : 0 < pullCount (arm n h) n h) :
    pullCount (arm n h) n h ≤ 4 * c * log (n + 1) / gap ν (arm n h) ^ 2 := by
  have h_gap_le := gap_arm_le_two_mul_ucbWidth h_best h_arm h_le
  rw [ucbWidth] at h_gap_le
  have h2 : (gap ν (arm n h)) ^ 2 ≤ (2 * √(c * log (n + 1) / pullCount (arm n h) n h)) ^ 2 := by
    gcongr
  rw [mul_pow, sq_sqrt] at h2
  · have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this] at h2
    field_simp at h2 ⊢
    exact h2
  · have : 0 ≤ log (n + 1) := by simp [log_nonneg]
    positivity

lemma todo [Nonempty (Fin K)] (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n k : ℕ) (hk : k ≠ 0) :
    𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (n + 1) / k) < (ν a)[id]} ≤
      1 / (n + 1) ^ (c / 2) := by
  have h_meas : MeasurableSet {ω | ω / k + √(c * log (n + 1) / k) < (ν a)[id]} :=
    measurableSet_lt (by fun_prop) measurable_const
  calc
  𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (n + 1) / k) < (ν a)[id]}
  _ = ((𝔓).map (fun ω ↦ ∑ m ∈ Icc 1 k, rewardByCount a m ω))
      {ω | ω / k + √(c * log (n + 1) / k) < (ν a)[id]} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = ((𝔓).map (fun ω ↦ ∑ s ∈ range k, ω.2 s a))
      {ω | ω / k + √(c * log (n + 1) / k) < (ν a)[id]} := by
    rw [IdentDistrib.map_eq (identDistrib_sum_Icc_rewardByCount k a)]
  _ = 𝔓 {ω | (∑ s ∈ range k, ω.2 s a) / k + √(c * log (n + 1) / k) < (ν a)[id]} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = 𝔓 {ω | (∑ s ∈ range k, (ω.2 s a - (ν a)[id])) / k < - √(c * log (n + 1) / k)} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = 𝔓 {ω | (∑ s ∈ range k, (ω.2 s a - (ν a)[id])) < - √(c * k * log (n + 1))} := by
    congr with ω
    field_simp
    congr! 2
    sorry
  _ ≤ ENNReal.ofReal (exp (-(√(c * k * log (n + 1))) ^ 2 / (2 * k * 1))) := by
    rw [← ofReal_measureReal]
    gcongr
    sorry
  _ = 1 / (n + 1) ^ (c / 2) := by
    rw [sq_sqrt]
    swap; · exact mul_nonneg (by positivity) (log_nonneg (by simp))
    field_simp
    rw [div_eq_inv_mul, ← mul_assoc, ← Real.log_rpow (by positivity), ← Real.log_inv,
      Real.exp_log (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    congr 2
    · norm_cast
    · field

lemma prob_ucbIndex_lt [Nonempty (Fin K)]
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    𝔓t {h | empMean a n h + ucbWidth c a n h < (ν a)[id]} ≤ 1 / (n + 1) ^ (c / 2 - 1) := by
  -- extend the probability space
  suffices 𝔓 {ω | empMean a n ω.1 + ucbWidth c a n ω.1 < (ν a)[id]} ≤ 1 / (n + 1) ^ (c / 2 - 1) by
    sorry
  -- express with `rewardByCount` and `pullCount`
  unfold empMean ucbWidth
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  calc
  𝔓 {ω | (∑ m ∈ Icc 1 (pullCount a n ω.1), rewardByCount a m ω) / pullCount a n ω.1 +
          √(c * log (↑n + 1) / pullCount a n ω.1) < (ν a)[id]}
  -- list the possible values of `pullCount a n ω.1`
  _ ≤ 𝔓 {ω | ∃ k ≤ n, (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k +
        √(c * log (↑n + 1) / k) < (ν a)[id]} := by
    refine measure_mono fun ω hω ↦ ?_
    simp only [Nat.cast_nonneg, sqrt_div', id_eq, Set.mem_setOf_eq] at hω ⊢
    exact ⟨pullCount a n ω.1, pullCount_le _ _ _, hω⟩
  _ = 𝔓 (⋃ k ∈ range (n + 1), {ω |(∑ m ∈ Icc 1 k, rewardByCount a m ω) / k +
        √(c * log (↑n + 1) / k) < (ν a)[id]}) := by
    congr 1
    ext ω
    simp [Nat.lt_add_one_iff]
  -- Union bound over the possible values of `pullCount a n ω.1`
  _ ≤ ∑ k ∈ range (n + 1),
      𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (↑n + 1) / k) < (ν a)[id]} :=
    measure_biUnion_finset_le _ _
  _ ≤ ∑ k ∈ range (n + 1), (1 : ℝ≥0∞) / (n + 1) ^ (c / 2) := by
    gcongr with k
    by_cases hk : k = 0
    · sorry -- todo: false for now. Need to fix this.
    exact todo hν hc a n k hk
  _ = 1 / (n + 1) ^ (c / 2 - 1) := by
    simp only [one_div, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [ENNReal.rpow_sub _ _ (by simp) (by finiteness), ENNReal.rpow_one]
    sorry

lemma prob_ucbIndex_gt [Nonempty (Fin K)]
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    𝔓t {h | (ν a)[id] < empMean a n h - ucbWidth c a n h} ≤
      sorry := by
  sorry

lemma pullCount_le_add (a : Fin K) (n C : ℕ) (ω : ℕ → Fin K × ℝ) :
    pullCount a n ω ≤ C + ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s := by
  rw [pullCount_eq_sum]
  calc ∑ s ∈ range n, if arm s ω = a then 1 else 0
  _ ≤ ∑ s ∈ range n, ({s | arm s ω = a ∧ pullCount a s ω ≤ C}.indicator 1 s +
      {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s) := by
    gcongr with s hs
    simp [Set.indicator_apply]
    grind
  _ = ∑ s ∈ range n, {s | arm s ω = a ∧ pullCount a s ω ≤ C}.indicator 1 s +
      ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s := by
    rw [Finset.sum_add_distrib]
  _ ≤ C + ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s := by
    gcongr
    sorry

omit [IsMarkovKernel ν] in
lemma pullCount_le_add_three [Nonempty (Fin K)] (a : Fin K) (n C : ℕ) (ω : ℕ → Fin K × ℝ) :
    pullCount a n ω ≤ C +
      ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
        empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | (ν (arm s ω))[id] <
          empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω}.indicator 1 s := by
  refine (pullCount_le_add a n C ω).trans ?_
  simp_rw [add_assoc]
  gcongr
  simp_rw [← add_assoc]
  let A := {s | arm s ω = a ∧ C < pullCount a s ω}
  let B := {s | arm s ω = a ∧ C < pullCount a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
        empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}
  let C' := {s | empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}
  let D := {s | (ν (arm s ω))[id] <
          empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω}
  change ∑ s ∈ range n, A.indicator 1 s ≤
    ∑ s ∈ range n, B.indicator 1 s + ∑ s ∈ range n, C'.indicator 1 s +
      ∑ s ∈ range n, D.indicator 1 s
  have h_union : A ⊆ B ∪ C' ∪ D := by simp [A, B, C', D]; grind
  calc
    (∑ s ∈ range n, A.indicator 1 s)
    _ ≤ (∑ s ∈ range n, (B ∪ C' ∪ D).indicator (fun _ ↦ (1 : ℕ)) s) := by
      gcongr with n hn
      by_cases h : n ∈ A
      · have : n ∈ B ∪ C' ∪ D := h_union h
        simp [h, this]
      · simp [h]
    _ ≤ ∑ s ∈ range n, (B.indicator 1 s + C'.indicator 1 s + D.indicator 1 s) := by
      gcongr with s
      simp [Set.indicator_apply]
      grind
    _ = ∑ s ∈ range n, B.indicator 1 s + ∑ s ∈ range n, C'.indicator 1 s +
          ∑ s ∈ range n, D.indicator 1 s := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : Fin K) (n : ℕ) :
    𝔓t[fun ω ↦ (pullCount a n ω : ℝ)] ≤ log n / gap ν a ^ 2 + 1 := by
  sorry

/-- Regret bound for the UCB algorithm. -/
lemma regret_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (n : ℕ) :
    𝔓t[regret ν n] ≤ ∑ a, (log n / gap ν a + gap ν a) := by -- todo: fix that bound
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · exact fun i _ ↦ (integrable_pullCount i n).mul_const _
  gcongr with a
  rw [integral_mul_const]
  sorry

end UCB

end Bandits
