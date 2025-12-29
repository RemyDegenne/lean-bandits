/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.AlgorithmAndRandomVariables
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.RewardByCountMeasure
import LeanBandits.BanditAlgorithms.ETC

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

@[fun_prop]
lemma measurable_ucbWidth (c : ℝ) (a : Fin K) : Measurable (ucbWidth c a n) := by
  unfold ucbWidth
  fun_prop

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

lemma arm_ae_all_eq :
    ∀ᵐ h ∂𝔓t, arm 0 h = ⟨0, hK⟩ ∧ ∀ n, arm (n + 1) h = nextArm hK c n (fun i ↦ h i) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨arm_zero, arm_ae_eq_ucbNextArm⟩

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

lemma forall_arm_eq_mod_of_lt :
    ∀ᵐ h ∂𝔓t, ∀ n < K, arm n h = ⟨n % K, Nat.mod_lt _ hK⟩ := by
  simp_rw [ae_all_iff]
  intro n hn
  induction n with
  | zero => exact arm_zero
  | succ n _ =>
    filter_upwards [arm_ae_eq_ucbNextArm n] with h h_eq
    rw [h_eq, nextArm, if_pos]
    grind

lemma forall_ucbIndex_le_ucbIndex_arm (a : Fin K) :
    ∀ᵐ h ∂𝔓t, ∀ n, K ≤ n →
      empMean a n h + ucbWidth c a n h ≤ empMean (arm n h) n h + ucbWidth c (arm n h) n h := by
  simp_rw [ae_all_iff]
  exact fun _ ↦ ucbIndex_le_ucbIndex_arm a

lemma forall_arm_prop :
    ∀ᵐ h ∂𝔓t,
      (∀ n < K, arm n h = ⟨n % K, Nat.mod_lt _ hK⟩) ∧
      (∀ n, K ≤ n → ∀ a, empMean a n h + ucbWidth c a n h ≤
        empMean (arm n h) n h + ucbWidth c (arm n h) n h) := by
  simp only [eventually_and]
  constructor
  · exact forall_arm_eq_mod_of_lt
  · simp_rw [ae_all_iff]
    intro n hn a
    have h_ae := forall_ucbIndex_le_ucbIndex_arm (ν := ν) (c := c) (hK := hK) a
    simp_rw [ae_all_iff] at h_ae
    exact h_ae n hn

lemma pullCount_eq_of_time_eq (a : Fin K) :
    ∀ᵐ ω ∂𝔓t, pullCount a K ω = 1 := by
  filter_upwards [forall_arm_eq_mod_of_lt] with h h_eq
  rw [pullCount_eq_sum]
  conv_rhs => rw [← sum_mod_range hK a]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  congr
  exact h_eq s (by grind)

lemma time_gt_of_pullCount_gt_one (a : Fin K) :
    ∀ᵐ ω ∂𝔓t, ∀ n, 1 < pullCount a n ω → K < n := by
  filter_upwards [pullCount_eq_of_time_eq a] with h h_eq n hn
  rw [← h_eq] at hn
  by_contra! h_lt
  exact hn.not_ge (pullCount_mono _ h_lt _)

lemma pullCount_pos_of_time_ge :
    ∀ᵐ ω ∂𝔓t, ∀ n, K ≤ n → ∀ b : Fin K, 0 < pullCount b n ω := by
  have h_ae a := pullCount_eq_of_time_eq (ν := ν) (c := c) (hK := hK) a
  rw [← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω hω n hn a
  refine Nat.one_pos.trans_le ?_
  rw [← hω a]
  exact pullCount_mono _ hn _

lemma pullCount_pos_of_pullCount_gt_one (a : Fin K) :
    ∀ᵐ ω ∂𝔓t, ∀ n, 1 < pullCount a n ω → ∀ b : Fin K, 0 < pullCount b n ω := by
  filter_upwards [time_gt_of_pullCount_gt_one a, pullCount_pos_of_time_ge] with ω h1 h2 n h_gt a
  exact h2 n (h1 n h_gt).le a

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

lemma todo (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n k : ℕ) (hk : k ≠ 0) :
    𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (n + 1) / k) ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ (c / 2) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h_meas : MeasurableSet {ω | ω / k + √(c * log (n + 1) / k) ≤ (ν a)[id]} :=
    measurableSet_le (by fun_prop) measurable_const
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc
  𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (n + 1) / k) ≤ (ν a)[id]}
  _ = ((𝔓).map (fun ω ↦ ∑ m ∈ Icc 1 k, rewardByCount a m ω))
      {ω | ω / k + √(c * log (n + 1) / k) ≤ (ν a)[id]} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = ((𝔓).map (fun ω ↦ ∑ s ∈ range k, ω.2 s a))
      {ω | ω / k + √(c * log (n + 1) / k) ≤ (ν a)[id]} := by
    rw [IdentDistrib.map_eq (identDistrib_sum_Icc_rewardByCount k a)]
  _ = 𝔓 {ω | (∑ s ∈ range k, ω.2 s a) / k + √(c * log (n + 1) / k) ≤ (ν a)[id]} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = 𝔓 {ω | (∑ s ∈ range k, (ω.2 s a - (ν a)[id])) / k ≤ - √(c * log (n + 1) / k)} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = 𝔓 {ω | (∑ s ∈ range k, (ω.2 s a - (ν a)[id])) ≤ - √(c * k * log (n + 1))} := by
    congr with ω
    field_simp
    congr! 2
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_assoc (k : ℝ), sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ = Bandit.streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ - √(c * k * log (n + 1))} := by
    rw [← Bandit.snd_measure (ucbAlgorithm hK c), Measure.snd_apply]
    · rfl
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  _ ≤ ENNReal.ofReal (exp (-(√(c * k * log (n + 1))) ^ 2 / (2 * k * 1))) := by
    rw [← ofReal_measureReal]
    gcongr
    refine (HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun (c := 1) ?_ ?_ (by positivity))
    · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
        (fun _ ↦ by fun_prop)
    · intro i him
      refine (hν a).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
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

lemma todo' (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n k : ℕ) (hk : k ≠ 0) :
    𝔓 {ω | (ν a)[id] ≤ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k - √(c * log (n + 1) / k)} ≤
      1 / (n + 1) ^ (c / 2) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h_meas : MeasurableSet {ω |(ν a)[id] ≤ ω / k - √(c * log (n + 1) / k)} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc
  𝔓 {ω | (ν a)[id] ≤ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k - √(c * log (n + 1) / k)}
  _ = ((𝔓).map (fun ω ↦ ∑ m ∈ Icc 1 k, rewardByCount a m ω))
      {ω | (ν a)[id] ≤ ω / k - √(c * log (n + 1) / k)} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = ((𝔓).map (fun ω ↦ ∑ s ∈ range k, ω.2 s a))
      {ω | (ν a)[id] ≤ ω / k - √(c * log (n + 1) / k)} := by
    rw [IdentDistrib.map_eq (identDistrib_sum_Icc_rewardByCount k a)]
  _ = 𝔓 {ω | (ν a)[id] ≤ (∑ s ∈ range k, ω.2 s a) / k - √(c * log (n + 1) / k)} := by
    rw [Measure.map_apply (by fun_prop) h_meas]
    rfl
  _ = 𝔓 {ω | √(c * log (n + 1) / k) ≤ (∑ s ∈ range k, (ω.2 s a - (ν a)[id])) / k} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = 𝔓 {ω | √(c * k * log (n + 1)) ≤ (∑ s ∈ range k, (ω.2 s a - (ν a)[id]))} := by
    congr with ω
    field_simp
    congr! 1
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_comm _ (k : ℝ), sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ = Bandit.streamMeasure ν
      {ω | √(c * k * log (n + 1)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))} := by
    rw [← Bandit.snd_measure (ucbAlgorithm hK c), Measure.snd_apply]
    · rfl
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  _ ≤ ENNReal.ofReal (exp (-(√(c * k * log (n + 1))) ^ 2 / (2 * k * 1))) := by
    rw [← ofReal_measureReal]
    gcongr
    refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (c := 1) ?_ ?_ (by positivity))
    · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
        (fun _ ↦ by fun_prop)
    · intro i him
      refine (hν a).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
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

lemma prob_ucbIndex_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    𝔓t {h | 0 < pullCount a n h ∧ empMean a n h + ucbWidth c a n h ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ (c / 2 - 1) := by
  -- extend the probability space
  suffices 𝔓 {ω | 0 < pullCount a n ω.1 ∧
      empMean a n ω.1 + ucbWidth c a n ω.1 ≤ (ν a)[id]} ≤ 1 / (n + 1) ^ (c / 2 - 1) by
    rwa [← Bandit.fst_measure (ucbAlgorithm hK c) ν, Measure.fst_apply]
    change MeasurableSet ({h | 0 < pullCount a n h}
      ∩ {h | empMean a n h + ucbWidth c a n h ≤ ∫ (x : ℝ), id x ∂ν a})
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  -- express with `rewardByCount` and `pullCount`
  unfold empMean ucbWidth
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  calc
  𝔓 {ω | 0 < pullCount a n ω.1 ∧
    (∑ m ∈ Icc 1 (pullCount a n ω.1), rewardByCount a m ω) / pullCount a n ω.1 +
          √(c * log (↑n + 1) / pullCount a n ω.1) ≤ (ν a)[id]}
  -- list the possible values of `pullCount a n ω.1`
  _ ≤ 𝔓 {ω | ∃ k ≤ n, 0 < k ∧ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k +
        √(c * log (↑n + 1) / k) ≤ (ν a)[id]} := by
    refine measure_mono fun ω hω ↦ ?_
    simp only [Nat.cast_nonneg, sqrt_div', id_eq, Set.mem_setOf_eq] at hω ⊢
    exact ⟨pullCount a n ω.1, pullCount_le _ _ _, hω⟩
  _ = 𝔓 (⋃ k ∈ Icc 1 n, {ω |(∑ m ∈ Icc 1 k, rewardByCount a m ω) / k +
        √(c * log (↑n + 1) / k) ≤ (ν a)[id]}) := by
    congr 1
    ext ω
    simp
    grind
  -- Union bound over the possible values of `pullCount a n ω.1`
  _ ≤ ∑ k ∈ Icc 1 n,
      𝔓 {ω | (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k + √(c * log (↑n + 1) / k) ≤ (ν a)[id]} :=
    measure_biUnion_finset_le _ _
  _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ≥0∞) / (n + 1) ^ (c / 2) := by
    gcongr with k hk
    exact todo hν hc a n k (by grind)
  _ ≤ (n + 1) * (1 : ℝ≥0∞) / (n + 1) ^ (c / 2) := by
    simp only [one_div, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    rw [div_eq_mul_inv ((n : ℝ≥0∞) + 1)]
    gcongr
    exact le_self_add
  _ = 1 / (n + 1) ^ (c / 2 - 1) := by
    simp only [mul_one, one_div]
    rw [ENNReal.rpow_sub _ _ (by simp) (by finiteness), ENNReal.rpow_one, div_eq_mul_inv,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), inv_inv]

lemma prob_ucbIndex_ge (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    𝔓t {h | 0 < pullCount a n h ∧
      (ν a)[id] ≤ empMean a n h - ucbWidth c a n h} ≤ 1 / (n + 1) ^ (c / 2 - 1) := by
  -- extend the probability space
  suffices 𝔓 {ω | 0 < pullCount a n ω.1 ∧
      (ν a)[id] ≤ empMean a n ω.1 - ucbWidth c a n ω.1} ≤ 1 / (n + 1) ^ (c / 2 - 1) by
    rwa [← Bandit.fst_measure (ucbAlgorithm hK c) ν, Measure.fst_apply]
    change MeasurableSet ({h | 0 < pullCount a n h}
      ∩ {h | (ν a)[id] ≤ empMean a n h - ucbWidth c a n h})
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  -- express with `rewardByCount` and `pullCount`
  unfold empMean ucbWidth
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  calc
  𝔓 {ω | 0 < pullCount a n ω.1 ∧
    (ν a)[id] ≤ (∑ m ∈ Icc 1 (pullCount a n ω.1), rewardByCount a m ω) / pullCount a n ω.1 -
          √(c * log (↑n + 1) / pullCount a n ω.1)}
  -- list the possible values of `pullCount a n ω.1`
  _ ≤ 𝔓 {ω | ∃ k ≤ n, 0 < k ∧ (ν a)[id] ≤ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k -
        √(c * log (↑n + 1) / k)} := by
    refine measure_mono fun ω hω ↦ ?_
    simp only [Nat.cast_nonneg, sqrt_div', id_eq, Set.mem_setOf_eq] at hω ⊢
    exact ⟨pullCount a n ω.1, pullCount_le _ _ _, hω⟩
  _ = 𝔓 (⋃ k ∈ Icc 1 n, {ω | (ν a)[id] ≤ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k -
        √(c * log (↑n + 1) / k)}) := by
    congr 1
    ext ω
    simp
    grind
  -- Union bound over the possible values of `pullCount a n ω.1`
  _ ≤ ∑ k ∈ Icc 1 n,
      𝔓 {ω | (ν a)[id] ≤ (∑ m ∈ Icc 1 k, rewardByCount a m ω) / k - √(c * log (↑n + 1) / k)} :=
    measure_biUnion_finset_le _ _
  _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ≥0∞) / (n + 1) ^ (c / 2) := by
    gcongr with k hk
    exact todo' hν hc a n k (by grind)
  _ ≤ (n + 1) * (1 : ℝ≥0∞) / (n + 1) ^ (c / 2) := by
    simp only [one_div, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    rw [div_eq_mul_inv ((n : ℝ≥0∞) + 1)]
    gcongr
    exact le_self_add
  _ = 1 / (n + 1) ^ (c / 2 - 1) := by
    simp only [mul_one, one_div]
    rw [ENNReal.rpow_sub _ _ (by simp) (by finiteness), ENNReal.rpow_one, div_eq_mul_inv,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), inv_inv]

lemma probReal_ucbIndex_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    (𝔓t).real {h | 0 < pullCount a n h ∧ empMean a n h + ucbWidth c a n h ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ (c / 2 - 1) := by
  rw [measureReal_def]
  grw [prob_ucbIndex_le hν hc a n]
  swap; · finiteness
  simp only [one_div, ENNReal.toReal_inv]
  rw [← ENNReal.toReal_rpow]
  norm_cast

lemma probReal_ucbIndex_ge (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    (𝔓t).real {h | 0 < pullCount a n h ∧
      (ν a)[id] ≤ empMean a n h - ucbWidth c a n h} ≤ 1 / (n + 1) ^ (c / 2 - 1) := by
  rw [measureReal_def]
  grw [prob_ucbIndex_ge hν hc a n]
  swap; · finiteness
  simp only [one_div, ENNReal.toReal_inv]
  rw [← ENNReal.toReal_rpow]
  norm_cast

lemma pullCount_le_add (a : Fin K) (n C : ℕ) (ω : ℕ → Fin K × ℝ) :
    pullCount a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s := by
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
  _ ≤ C + 1 + ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω}.indicator 1 s := by
    gcongr
    have h_le n : ∑ s ∈ range n, {s | arm s ω = a ∧ pullCount a s ω ≤ C}.indicator 1 s ≤
        pullCount a n ω := by
      rw [pullCount_eq_sum]
      gcongr with s hs
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      grind
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_range_succ]
      rcases le_or_gt (pullCount a n ω) C with h_pc | h_pc
      · have hn' : ∑ s ∈ range n, {s | arm s ω = a ∧ pullCount a s ω ≤ C}.indicator 1 s ≤ C :=
          (h_le n).trans h_pc
        grw [hn']
        gcongr
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        grind
      · refine le_trans ?_ hn
        simp [h_pc]

omit [IsMarkovKernel ν] in
lemma pullCount_le_add_three [Nonempty (Fin K)] (a : Fin K) (n C : ℕ) (ω : ℕ → Fin K × ℝ) :
    pullCount a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
        empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | C < pullCount a s ω ∧ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | C < pullCount a s ω ∧ (ν a)[id] <
          empMean a s ω - ucbWidth c a s ω}.indicator 1 s := by
  refine (pullCount_le_add a n C ω).trans ?_
  simp_rw [add_assoc]
  gcongr
  simp_rw [← add_assoc]
  let A := {s | arm s ω = a ∧ C < pullCount a s ω}
  let B := {s | arm s ω = a ∧ C < pullCount a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
        empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}
  let C' := {s | C < pullCount a s ω ∧ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}
  let D := {s | C < pullCount a s ω ∧ (ν a)[id] <
          empMean a s ω - ucbWidth c a s ω}
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

lemma pullCount_le_add_three_ae [Nonempty (Fin K)] (a : Fin K) (n C : ℕ) (hC : C ≠ 0) :
    ∀ᵐ ω ∂𝔓t,
    pullCount a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
        empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount (bestArm ν) s ω ∧ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount a s ω ∧ (ν a)[id] <
          empMean a s ω - ucbWidth c a s ω}.indicator 1 s := by
  filter_upwards [pullCount_pos_of_pullCount_gt_one a] with ω hω
  refine (pullCount_le_add_three a n C ω (ν := ν) (c := c)).trans ?_
  gcongr 5 with k hk j k hk j
  · gcongr 1
    exact fun h_gt ↦ hω _ (lt_of_le_of_lt (by grind) h_gt) _
  · exact fun h_gt ↦ hω _ (lt_of_le_of_lt (by grind) h_gt) _

lemma some_sum_eq_zero [Nonempty (Fin K)] (hc : 0 ≤ c) (a : Fin K) (h_gap : 0 < gap ν a) (n C : ℕ)
    (hC : C ≠ 0) (hC' : 4 * c * log (n + 1) / gap ν a ^ 2 ≤ C) :
    ∀ᵐ ω ∂𝔓t,
    ∑ s ∈ range n, {s | arm s ω = a ∧ C < pullCount a s ω ∧
      (ν (bestArm ν))[id] ≤ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω ∧
      empMean (arm s ω) s ω - ucbWidth c (arm s ω) s ω ≤ (ν (arm s ω))[id]}.indicator 1 s = 0 := by
  have h_ae := forall_ucbIndex_le_ucbIndex_arm (bestArm ν) (ν := ν) (c := c) (hK := hK)
  have h_gt := time_gt_of_pullCount_gt_one a (ν := ν) (c := c) (hK := hK)
  filter_upwards [h_ae, h_gt] with ω h_le h_time_ge
  simp only [id_eq, tsub_le_iff_right, sum_eq_zero_iff, mem_range, Set.indicator_apply_eq_zero,
    Set.mem_setOf_eq, Pi.one_apply, one_ne_zero, imp_false, not_and, not_le]
  intro k hn h_arm hC_lt h_le_best
  by_contra! h_le_arm
  have h := pullCount_arm_le hc h_le_best (by simpa) ?_ ?_ ?_
  rotate_left
  · refine h_le _ ?_
    refine (h_time_ge _ ?_).le
    refine lt_of_le_of_lt ?_ hC_lt
    grind
  · rwa [h_arm]
  · rw [h_arm]
    exact zero_le'.trans_lt hC_lt
  refine lt_irrefl (4 * c * log (n + 1) / gap ν a ^ 2) ?_
  refine hC'.trans_lt (lt_of_lt_of_le ?_ (h.trans ?_))
  · rw [h_arm]
    exact mod_cast hC_lt
  · rw [h_arm]
    gcongr

lemma pullCount_ae_le_add_two [Nonempty (Fin K)] (hc : 0 ≤ c) (a : Fin K) (h_gap : 0 < gap ν a)
    (n C : ℕ) (hC : C ≠ 0) (hC' : 4 * c * log (n + 1) / gap ν a ^ 2 ≤ C) :
    ∀ᵐ ω ∂𝔓t,
    pullCount a n ω ≤ C + 1 +
      ∑ s ∈ range n,
        {s | 0 < pullCount (bestArm ν) s ω ∧ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount a s ω ∧ (ν a)[id] <
          empMean a s ω - ucbWidth c a s ω}.indicator 1 s := by
  filter_upwards [some_sum_eq_zero hc a h_gap n C hC hC',
    pullCount_le_add_three_ae a n C hC] with ω hω_zero hω_le
  refine (hω_le).trans_eq ?_
  rw [hω_zero]

/-- A sum that appears in the UCB regret upper bound. -/
noncomputable
def constSum (c : ℝ) (n : ℕ) : ℝ≥0∞ := ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c / 2 - 1)

lemma constSum_lt_top (c : ℝ) (n : ℕ) : constSum c n < ∞ := by
  rw [constSum, ENNReal.sum_lt_top]
  intro k hk
  simp only [one_div, ENNReal.inv_lt_top]
  positivity

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le' (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 < c) (a : Fin K) (h_gap : 0 < gap ν a) (n : ℕ) :
    ∫⁻ ω, pullCount a n ω ∂𝔓t ≤
      ENNReal.ofReal (4 * c * log (n + 1) / gap ν a ^ 2 + 1) + 1 + 2 * constSum c n := by
  by_cases hn_zero : n = 0
  · simp [hn_zero]
  let C a : ℕ := ⌈4 * c * log (n + 1) / gap ν a ^ 2⌉₊
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h_set_1 b : MeasurableSet {a_1 | 0 < pullCount a b a_1 ∧
      (ν a)[id] < empMean a b a_1 - ucbWidth c a b a_1} := by
    change MeasurableSet ({a_1 | 0 < pullCount a b a_1} ∩
      {a_1 | (ν a)[id] < empMean a b a_1 - ucbWidth c a b a_1})
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have h_set_2 b : MeasurableSet {a | 0 < pullCount (bestArm ν) b a ∧
      empMean (bestArm ν) b a + ucbWidth c (bestArm ν) b a < (ν (bestArm ν))[id]} := by
    change MeasurableSet ({a | 0 < pullCount (bestArm ν) b a} ∩
      {a | empMean (bestArm ν) b a + ucbWidth c (bestArm ν) b a < (ν (bestArm ν))[id]})
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have h_meas_1 b : Measurable fun h ↦ {s | 0 < pullCount a s h ∧ (ν a)[id] <
      empMean a s h - ucbWidth c a s h}.indicator (1 : ℕ → ℕ) b := by
    simp only [id_eq, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    exact Measurable.ite (h_set_1 _) (by fun_prop) (by fun_prop)
  have h_meas_2 b : Measurable fun h ↦ {s | 0 < pullCount (bestArm ν) s h ∧
      empMean (bestArm ν) s h + ucbWidth c (bestArm ν) s h <
          (ν (bestArm ν))[id]}.indicator (1 : ℕ → ℕ) b := by
    simp only [id_eq, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    exact Measurable.ite (h_set_2 _) (by fun_prop) (by fun_prop)
  calc ∫⁻ ω, pullCount a n ω ∂𝔓t
  _ ≤ ∫⁻ ω, C a + 1 +
      ∑ s ∈ range n,
        {s | 0 < pullCount (bestArm ν) s ω ∧ empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator (1 : ℕ → ℕ) s +
      ∑ s ∈ range n,
        {s | 0 < pullCount a s ω ∧ (ν a)[id] <
          empMean a s ω - ucbWidth c a s ω}.indicator (1 : ℕ → ℕ) s ∂𝔓t := by
    refine lintegral_mono_ae ?_
    have hCa : C a ≠ 0 := by
      simp only [ne_eq, Nat.ceil_eq_zero, not_le, C]
      have : 0 < log (n + 1) := log_pos (by simp; grind)
      positivity
    filter_upwards [pullCount_ae_le_add_two hc.le a h_gap n (C a) hCa (Nat.le_ceil _)] with ω hω
    simp only [id_eq, Nat.cast_sum]
    norm_cast
  _ ≤ (C a : ℝ≥0∞) + 1 +
      ∑ s ∈ range n,
        𝔓t {ω | 0 < pullCount (bestArm ν) s ω ∧
          empMean (bestArm ν) s ω + ucbWidth c (bestArm ν) s ω < (ν (bestArm ν))[id]} +
      ∑ s ∈ range n,
        𝔓t {ω | 0 < pullCount a s ω ∧ (ν a)[id] < empMean a s ω - ucbWidth c a s ω} := by
    simp only [id_eq, Nat.cast_sum]
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [lintegral_finset_sum _ (by fun_prop), lintegral_finset_sum _ (by fun_prop)]
    gcongr with k hk k hk
    · rw [← lintegral_indicator_one]
      swap; · exact h_set_2 _
      gcongr with h
      simp [Set.indicator_apply]
    · rw [← lintegral_indicator_one]
      swap; · exact h_set_1 _
      gcongr with h
      simp [Set.indicator_apply]
  _ ≤ (C a : ℝ≥0∞) + 1 +
      ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c / 2 - 1) +
      ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c / 2 - 1) := by
    gcongr with s hs s hs
    · refine (measure_mono ?_).trans (prob_ucbIndex_le hν hc.le (bestArm ν) s)
      grind
    · refine (measure_mono ?_).trans (prob_ucbIndex_ge hν hc.le a s)
      grind
  _ ≤ ENNReal.ofReal (4 * c * log (n + 1) / gap ν a ^ 2 + 1) + 1 + 2 * constSum c n := by
    rw [two_mul, add_assoc, constSum]
    gcongr
    simp only [C]
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (Nat.ceil_lt_add_one ?_).le
    have : 0 ≤ log (n + 1) := log_nonneg (by simp)
    positivity

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 < c) (a : Fin K) (h_gap : 0 < gap ν a) (n : ℕ) :
    𝔓t[fun ω ↦ (pullCount a n ω : ℝ)] ≤
      4 * c * log (n + 1) / gap ν a ^ 2 + 2 + 2 * (constSum c n).toReal := by
  have h := expectation_pullCount_le' hν hc a h_gap n (hK := hK)
  simp_rw [← ENNReal.ofReal_natCast] at h
  rw [← ofReal_integral_eq_lintegral_ofReal] at h
  rotate_left
  · exact integrable_pullCount _ _
  · exact ae_of_all _ fun _ ↦ by simp
  simp only
  have : 0 ≤ log (n + 1) := log_nonneg (by simp)
  rw [← ENNReal.ofReal_toReal (a := 2 * constSum c n), ← ENNReal.ofReal_one, ← ENNReal.ofReal_add,
    ← ENNReal.ofReal_add, ENNReal.ofReal_le_ofReal_iff] at h
  rotate_left
  · positivity
  · positivity
  · simp
  · have : constSum c n ≠ ∞ := (constSum_lt_top c n).ne
    finiteness
  · simp
  · have : constSum c n ≠ ∞ := (constSum_lt_top c n).ne
    finiteness
  refine h.trans_eq ?_
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, add_left_inj]
  ring

/-- Regret bound for the UCB algorithm. -/
lemma regret_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (hc : 0 < c) (n : ℕ) :
    𝔓t[regret ν n] ≤
      ∑ a, (4 * c * log (n + 1) / gap ν a + gap ν a * (2 + 2 * (constSum c n).toReal)) := by
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · exact fun i _ ↦ (integrable_pullCount i n).mul_const _
  gcongr with a
  rw [integral_mul_const]
  by_cases h_gap : gap ν a = 0
  · simp [h_gap]
  replace h_gap : 0 < gap ν a := lt_of_le_of_ne gap_nonneg (Ne.symm h_gap)
  grw [expectation_pullCount_le hν hc a h_gap n]
  refine le_of_eq ?_
  rw [mul_add]
  field

end UCB

end Bandits
