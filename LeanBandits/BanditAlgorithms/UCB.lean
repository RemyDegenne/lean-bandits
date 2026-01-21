/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit.SumRewards
import LeanBandits.BanditAlgorithms.AuxSums
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.SequentialLearning.Deterministic

/-!
# UCB algorithm

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

section Algorithm

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth' (c : ℝ) (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  √(2 * c * log (n + 2) / pullCount' n h a)

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

variable {hK : 0 < K} {c : ℝ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
   {n : ℕ} {ω : Ω}

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth (A : ℕ → Ω → Fin K) (c : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  √(2 * c * log (n + 1) / pullCount A a n ω)

@[fun_prop]
lemma measurable_ucbWidth (hA : ∀ n, Measurable (A n)) (c : ℝ) (a : Fin K) :
    Measurable (ucbWidth A c a n) := by
  unfold ucbWidth
  fun_prop

lemma ucbWidth_eq_ucbWidth' (c : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    ucbWidth A c a n ω = ucbWidth' c (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  simp only [ucbWidth, pullCount_eq_pullCount' (A := A) (R' := R) hn, Nat.cast_nonneg, sqrt_div',
    ucbWidth']
  congr 4
  norm_cast
  grind

lemma arm_zero [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) :
    A 0 =ᵐ[P] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_zero_detAlgorithm

lemma arm_ae_eq_ucbNextArm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (n : ℕ) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextArm hK c n (IsAlgEnvSeq.hist A R n ω) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_detAlgorithm_ae_eq n

lemma arm_ae_all_eq [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) :
    ∀ᵐ h ∂P, A 0 h = ⟨0, hK⟩ ∧ ∀ n, A (n + 1) h = nextArm hK c n (IsAlgEnvSeq.hist A R n h) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨arm_zero h, arm_ae_eq_ucbNextArm h⟩

lemma ucbIndex_le_ucbIndex_arm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (a : Fin K) (hn : K ≤ n) :
    ∀ᵐ h ∂P, empMean A R a n h + ucbWidth A c a n h ≤
      empMean A R (A n h) n h + ucbWidth A c (A n h) n h := by
  filter_upwards [arm_ae_eq_ucbNextArm h (n - 1)] with h h_arm
  have : n - 1 + 1 = n := by grind
  have h_not_lt : ¬ n - 1 < K - 1 := by grind
  simp only [this, nextArm, h_not_lt, ↓reduceIte] at h_arm
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  simp_rw [h_arm, empMean_eq_empMean' (by grind : n ≠ 0),
    ucbWidth_eq_ucbWidth' (A := A) (R := R) _ _ _ _ (by grind : n ≠ 0)]
  exact isMaxOn_measurableArgmax (fun h a ↦ empMean' (n - 1) h a + ucbWidth' c (n - 1) h a)
    (IsAlgEnvSeq.hist A R (n - 1) h) a

lemma forall_arm_eq_mod_of_lt [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) :
    ∀ᵐ h ∂P, ∀ n < K, A n h = ⟨n % K, Nat.mod_lt _ hK⟩ := by
  simp_rw [ae_all_iff]
  intro n hn
  induction n with
  | zero => exact arm_zero h
  | succ n _ =>
    filter_upwards [arm_ae_eq_ucbNextArm h n] with h h_eq
    rw [h_eq, nextArm, if_pos]
    grind

lemma forall_ucbIndex_le_ucbIndex_arm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (a : Fin K) :
    ∀ᵐ h ∂P, ∀ n, K ≤ n →
      empMean A R a n h + ucbWidth A c a n h ≤
        empMean A R (A n h) n h + ucbWidth A c (A n h) n h := by
  simp_rw [ae_all_iff]
  exact fun _ ↦ ucbIndex_le_ucbIndex_arm h a

lemma forall_arm_prop [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) :
    ∀ᵐ h ∂P,
      (∀ n < K, A n h = ⟨n % K, Nat.mod_lt _ hK⟩) ∧
      (∀ n, K ≤ n → ∀ a, empMean A R a n h + ucbWidth A c a n h ≤
        empMean A R (A n h) n h + ucbWidth A c (A n h) n h) := by
  simp only [eventually_and]
  constructor
  · exact forall_arm_eq_mod_of_lt h
  · simp_rw [ae_all_iff]
    intro n hn a
    have h_ae := forall_ucbIndex_le_ucbIndex_arm h a
    simp_rw [ae_all_iff] at h_ae
    exact h_ae n hn

lemma pullCount_eq_of_time_eq [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, pullCount A a K ω = 1 := by
  filter_upwards [forall_arm_eq_mod_of_lt h] with h h_eq
  rw [pullCount_eq_sum]
  conv_rhs => rw [← sum_mod_range hK a]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  congr
  exact h_eq s (by grind)

lemma time_gt_of_pullCount_gt_one [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → K < n := by
  filter_upwards [pullCount_eq_of_time_eq h a] with h h_eq n hn
  rw [← h_eq] at hn
  by_contra! h_lt
  exact hn.not_ge (pullCount_mono _ h_lt _)

lemma pullCount_pos_of_time_ge [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) :
    ∀ᵐ ω ∂P, ∀ n, K ≤ n → ∀ b : Fin K, 0 < pullCount A b n ω := by
  have h_ae a := pullCount_eq_of_time_eq h a
  rw [← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω hω n hn a
  refine Nat.one_pos.trans_le ?_
  rw [← hω a]
  exact pullCount_mono _ hn _

lemma pullCount_pos_of_pullCount_gt_one [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → ∀ b : Fin K, 0 < pullCount A b n ω := by
  filter_upwards [time_gt_of_pullCount_gt_one h a, pullCount_pos_of_time_ge h] with ω h1 h2 n h_gt a
  exact h2 n (h1 n h_gt).le a

omit [IsMarkovKernel ν] in
lemma gap_arm_le_two_mul_ucbWidth [Nonempty (Fin K)]
    (h_best : (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) n ω + ucbWidth A c (bestArm ν) n ω)
    (h_arm : empMean A R (A n ω) n ω - ucbWidth A c (A n ω) n ω ≤ (ν (A n ω))[id])
    (h_le : empMean A R (bestArm ν) n ω + ucbWidth A c (bestArm ν) n ω ≤
      empMean A R (A n ω) n ω + ucbWidth A c (A n ω) n ω) :
    gap ν (A n ω) ≤ 2 * ucbWidth A c (A n ω) n ω := by
  rw [gap_eq_bestArm_sub, sub_le_iff_le_add']
  calc (ν (bestArm ν))[id]
  _ ≤ empMean A R (bestArm ν) n ω + ucbWidth A c (bestArm ν) n ω := h_best
  _ ≤ empMean A R (A n ω) n ω + ucbWidth A c (A n ω) n ω := h_le
  _ ≤ (ν (A n ω))[id] + 2 * ucbWidth A c (A n ω) n ω := by
    rw [two_mul, ← add_assoc]
    gcongr
    rwa [sub_le_iff_le_add] at h_arm

omit [IsMarkovKernel ν] in
lemma pullCount_arm_le [Nonempty (Fin K)] (hc : 0 ≤ c)
    (h_best : (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) n ω + ucbWidth A c (bestArm ν) n ω)
    (h_arm : empMean A R (A n ω) n ω - ucbWidth A c (A n ω) n ω ≤ (ν (A n ω))[id])
    (h_le : empMean A R (bestArm ν) n ω + ucbWidth A c (bestArm ν) n ω ≤
      empMean A R (A n ω) n ω + ucbWidth A c (A n ω) n ω)
    (h_gap_pos : 0 < gap ν (A n ω)) (h_pull_pos : 0 < pullCount A (A n ω) n ω) :
    pullCount A (A n ω) n ω ≤ 8 * c * log (n + 1) / gap ν (A n ω) ^ 2 := by
  have h_gap_le := gap_arm_le_two_mul_ucbWidth h_best h_arm h_le
  rw [ucbWidth] at h_gap_le
  have h2 : (gap ν (A n ω)) ^ 2 ≤ (2 * √(2 * c * log (n + 1) / pullCount A (A n ω) n ω)) ^ 2 := by
    gcongr
  rw [mul_pow, sq_sqrt] at h2
  · have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this] at h2
    field_simp at h2 ⊢
    grind
  · have : 0 ≤ log (n + 1) := by simp [log_nonneg]
    positivity

lemma todo (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * c * log (n + 1) / k) ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ c := by
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * c * log (n + 1) / k) ≤ (ν a)[id]}
  _ = streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) / k ≤ - √(2 * c * log (n + 1) / k)} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ - √(2 * c * k * log (n + 1))} := by
    congr with ω
    field_simp
    congr! 2
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_assoc (k : ℝ), mul_assoc (k : ℝ), sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ ≤ 1 / (n + 1) ^ c := prob_sum_le_sqrt_log hν hc a k hk

lemma todo' (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν
        {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * c * log (n + 1) / k)} ≤
      1 / (n + 1) ^ c := by
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * c * log (n + 1) / k)}
  _ = streamMeasure ν
      {ω | √(2 * c * log (n + 1) / k) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id])) / k} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = streamMeasure ν
      {ω | √(2 * c * k * log (n + 1)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))} := by
    congr with ω
    field_simp
    congr! 1
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_comm _ (k : ℝ), sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ ≤ 1 / (n + 1) ^ c := prob_sum_ge_sqrt_log hν hc a k hk

lemma prob_ucbIndex_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    P {h | 0 < pullCount A a n h ∧ empMean A R a n h + ucbWidth A c a n h ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ (c - 1) := by
  let s : Set (ℕ × ℝ) := {(m, x) | 0 < m ∧ x / m + √(2 * c * log (↑n + 1) / m) ≤ (ν a)[id]}
  have hs : MeasurableSet s := by
    simp only [Nat.cast_nonneg, sqrt_div', id_eq, measurableSet_setOf, s]
    fun_prop
  classical
  calc P {h | 0 < pullCount A a n h ∧ empMean A R a n h + ucbWidth A c a n h ≤ (ν a)[id]}
  _ ≤ ∑ k ∈ range (n + 1) with k ∈ Prod.fst '' s,
      (streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} :=
    prob_pullCount_prod_sumRewards_mem_le h hs
  _ ≤ ∑ k ∈ Icc 1 n,
      (streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m ↦ ?_) fun _ _ _ ↦ by positivity
    simp [s]
    grind
  _ = ∑ k ∈ Icc 1 n,
      (streamMeasure ν) {ω | (∑ i ∈ range k, ω i a) / k + √(2 * c * log (↑n + 1) / k) ≤
        (ν a)[id]} := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    congr with ω
    have hk : 0 < k := by grind
    simp [s, hk]
  _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ≥0∞) / (n + 1) ^ c := by
    gcongr with k hk
    exact todo hν hc a n k (by grind)
  _ ≤ (n + 1) * (1 : ℝ≥0∞) / (n + 1) ^ c := by
    simp only [one_div, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    rw [div_eq_mul_inv ((n : ℝ≥0∞) + 1)]
    gcongr
    exact le_self_add
  _ = 1 / (n + 1) ^ (c - 1) := by
    simp only [mul_one, one_div]
    rw [ENNReal.rpow_sub _ _ (by simp) (by finiteness), ENNReal.rpow_one, div_eq_mul_inv,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), inv_inv]

lemma prob_ucbIndex_ge [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    P {h | 0 < pullCount A a n h ∧
      (ν a)[id] ≤ empMean A R a n h - ucbWidth A c a n h} ≤ 1 / (n + 1) ^ (c - 1) := by
  let s : Set (ℕ × ℝ) := {(m, x) | 0 < m ∧ (ν a)[id] ≤ x / m - √(2 * c * log (↑n + 1) / m)}
  have hs : MeasurableSet s := by
    simp only [Nat.cast_nonneg, sqrt_div', id_eq, measurableSet_setOf, s]
    fun_prop
  classical
  calc P {h | 0 < pullCount A a n h ∧ (ν a)[id] ≤ empMean A R a n h - ucbWidth A c a n h}
  _ ≤ ∑ k ∈ range (n + 1) with k ∈ Prod.fst '' s,
      (streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} :=
    prob_pullCount_prod_sumRewards_mem_le h hs
  _ ≤ ∑ k ∈ Icc 1 n,
      (streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m ↦ ?_) fun _ _ _ ↦ by positivity
    simp [s]
    grind
  _ = ∑ k ∈ Icc 1 n,
      (streamMeasure ν)
        {ω | (ν a)[id] ≤ (∑ i ∈ range k, ω i a) / k - √(2 * c * log (↑n + 1) / k)} := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    congr with ω
    have hk : 0 < k := by grind
    simp [s, hk]
  _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ≥0∞) / (n + 1) ^ c := by
    gcongr with k hk
    exact todo' hν hc a n k (by grind)
  _ ≤ (n + 1) * (1 : ℝ≥0∞) / (n + 1) ^ c := by
    simp only [one_div, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    rw [div_eq_mul_inv ((n : ℝ≥0∞) + 1)]
    gcongr
    exact le_self_add
  _ = 1 / (n + 1) ^ (c - 1) := by
    simp only [mul_one, one_div]
    rw [ENNReal.rpow_sub _ _ (by simp) (by finiteness), ENNReal.rpow_one, div_eq_mul_inv,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), inv_inv]

lemma probReal_ucbIndex_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    P.real {h | 0 < pullCount A a n h ∧ empMean A R a n h + ucbWidth A c a n h ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ (c - 1) := by
  rw [measureReal_def]
  grw [prob_ucbIndex_le h hν hc a n]
  swap; · finiteness
  simp only [one_div, ENNReal.toReal_inv]
  rw [← ENNReal.toReal_rpow]
  norm_cast

lemma probReal_ucbIndex_ge [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 ≤ c) (a : Fin K) (n : ℕ) :
    P.real {h | 0 < pullCount A a n h ∧
      (ν a)[id] ≤ empMean A R a n h - ucbWidth A c a n h} ≤ 1 / (n + 1) ^ (c - 1) := by
  rw [measureReal_def]
  grw [prob_ucbIndex_ge h hν hc a n]
  swap; · finiteness
  simp only [one_div, ENNReal.toReal_inv]
  rw [← ENNReal.toReal_rpow]
  norm_cast

omit [IsMarkovKernel ν] in
lemma pullCount_le_add_three [Nonempty (Fin K)] (a : Fin K) (n C : ℕ) (ω : Ω) :
    pullCount A a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω ∧
        empMean A R (A s ω) s ω - ucbWidth A c (A s ω) s ω ≤ (ν (A s ω))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | C < pullCount A a s ω ∧ empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω <
          (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | C < pullCount A a s ω ∧ (ν a)[id] <
          empMean A R a s ω - ucbWidth A c a s ω}.indicator 1 s := by
  refine (pullCount_le_add a n C ω).trans ?_
  simp_rw [add_assoc]
  gcongr
  simp_rw [← add_assoc]
  let A' := {s | A s ω = a ∧ C < pullCount A a s ω}
  let B := {s | A s ω = a ∧ C < pullCount A a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω ∧
        empMean A R (A s ω) s ω - ucbWidth A c (A s ω) s ω ≤ (ν (A s ω))[id]}
  let C' := {s | C < pullCount A a s ω ∧
    empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω < (ν (bestArm ν))[id]}
  let D := {s | C < pullCount A a s ω ∧ (ν a)[id] < empMean A R a s ω - ucbWidth A c a s ω}
  change ∑ s ∈ range n, A'.indicator 1 s ≤
    ∑ s ∈ range n, B.indicator 1 s + ∑ s ∈ range n, C'.indicator 1 s +
      ∑ s ∈ range n, D.indicator 1 s
  have h_union : A' ⊆ B ∪ C' ∪ D := by simp [A', B, C', D]; grind
  calc
    (∑ s ∈ range n, A'.indicator 1 s)
    _ ≤ (∑ s ∈ range n, (B ∪ C' ∪ D).indicator (fun _ ↦ (1 : ℕ)) s) := by
      gcongr with n hn
      by_cases h : n ∈ A'
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

lemma pullCount_le_add_three_ae [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (a : Fin K) (n C : ℕ) (hC : C ≠ 0) :
    ∀ᵐ ω ∂P,
    pullCount A a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω ∧
        (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω ∧
        empMean A R (A s ω) s ω - ucbWidth A c (A s ω) s ω ≤ (ν (A s ω))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount A (bestArm ν) s ω ∧
          empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω <
            (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount A a s ω ∧ (ν a)[id] <
          empMean A R a s ω - ucbWidth A c a s ω}.indicator 1 s := by
  filter_upwards [pullCount_pos_of_pullCount_gt_one h a] with ω hω
  refine (pullCount_le_add_three (R := R) a n C ω (ν := ν) (c := c)).trans ?_
  gcongr 5 with k hk j k hk j
  · gcongr 1
    exact fun h_gt ↦ hω _ (lt_of_le_of_lt (by grind) h_gt) _
  · exact fun h_gt ↦ hω _ (lt_of_le_of_lt (by grind) h_gt) _

lemma some_sum_eq_zero [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hc : 0 ≤ c) (a : Fin K) (h_gap : 0 < gap ν a) (n C : ℕ)
    (hC : C ≠ 0) (hC' : 8 * c * log (n + 1) / gap ν a ^ 2 ≤ C) :
    ∀ᵐ ω ∂P,
    ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω ∧
      (ν (bestArm ν))[id] ≤ empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω ∧
      empMean A R (A s ω) s ω - ucbWidth A c (A s ω) s ω ≤ (ν (A s ω))[id]}.indicator 1 s = 0 := by
  have h_ae := forall_ucbIndex_le_ucbIndex_arm h (bestArm ν) (ν := ν) (c := c) (hK := hK)
  have h_gt := time_gt_of_pullCount_gt_one h a (ν := ν) (c := c) (hK := hK)
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
  refine lt_irrefl (8 * c * log (n + 1) / gap ν a ^ 2) ?_
  refine hC'.trans_lt (lt_of_lt_of_le ?_ (h.trans ?_))
  · rw [h_arm]
    exact mod_cast hC_lt
  · rw [h_arm]
    gcongr

lemma pullCount_ae_le_add_two [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hc : 0 ≤ c) (a : Fin K) (h_gap : 0 < gap ν a)
    (n C : ℕ) (hC : C ≠ 0) (hC' : 8 * c * log (n + 1) / gap ν a ^ 2 ≤ C) :
    ∀ᵐ ω ∂P,
    pullCount A a n ω ≤ C + 1 +
      ∑ s ∈ range n,
        {s | 0 < pullCount A (bestArm ν) s ω ∧
          empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω <
            (ν (bestArm ν))[id]}.indicator 1 s +
      ∑ s ∈ range n,
        {s | 0 < pullCount A a s ω ∧ (ν a)[id] <
          empMean A R a s ω - ucbWidth A c a s ω}.indicator 1 s := by
  filter_upwards [some_sum_eq_zero h hc a h_gap n C hC hC',
    pullCount_le_add_three_ae h a n C hC] with ω hω_zero hω_le
  refine (hω_le).trans_eq ?_
  rw [hω_zero]

/-- A sum that appears in the UCB regret upper bound. -/
noncomputable
def constSum (c : ℝ) (n : ℕ) : ℝ≥0∞ := ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c - 1)

lemma constSum_lt_top (c : ℝ) (n : ℕ) : constSum c n < ∞ := by
  rw [constSum, ENNReal.sum_lt_top]
  intro k hk
  simp only [one_div, ENNReal.inv_lt_top]
  positivity

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le' [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 < c) (a : Fin K) (h_gap : 0 < gap ν a) (n : ℕ) :
    ∫⁻ ω, pullCount A a n ω ∂P ≤
      ENNReal.ofReal (8 * c * log (n + 1) / gap ν a ^ 2 + 1) + 1 + 2 * constSum c n := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  by_cases hn_zero : n = 0
  · simp [hn_zero]
  let C a : ℕ := ⌈8 * c * log (n + 1) / gap ν a ^ 2⌉₊
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h_set_1 b : MeasurableSet {a_1 | 0 < pullCount A a b a_1 ∧
      (ν a)[id] < empMean A R a b a_1 - ucbWidth A c a b a_1} := by
    change MeasurableSet ({a_1 | 0 < pullCount A a b a_1} ∩
      {a_1 | (ν a)[id] < empMean A R a b a_1 - ucbWidth A c a b a_1})
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have h_set_2 b : MeasurableSet {a | 0 < pullCount A (bestArm ν) b a ∧
      empMean A R (bestArm ν) b a + ucbWidth A c (bestArm ν) b a < (ν (bestArm ν))[id]} := by
    change MeasurableSet ({a | 0 < pullCount A (bestArm ν) b a} ∩
      {a | empMean A R (bestArm ν) b a + ucbWidth A c (bestArm ν) b a < (ν (bestArm ν))[id]})
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have h_meas_1 b : Measurable fun h ↦ {s | 0 < pullCount A a s h ∧ (ν a)[id] <
      empMean A R a s h - ucbWidth A c a s h}.indicator (1 : ℕ → ℕ) b := by
    simp only [id_eq, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    exact Measurable.ite (h_set_1 _) (by fun_prop) (by fun_prop)
  have h_meas_2 b : Measurable fun h ↦ {s | 0 < pullCount A (bestArm ν) s h ∧
      empMean A R (bestArm ν) s h + ucbWidth A c (bestArm ν) s h <
          (ν (bestArm ν))[id]}.indicator (1 : ℕ → ℕ) b := by
    simp only [id_eq, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    exact Measurable.ite (h_set_2 _) (by fun_prop) (by fun_prop)
  calc ∫⁻ ω, pullCount A a n ω ∂P
  _ ≤ ∫⁻ ω, C a + 1 +
      ∑ s ∈ range n,
        {s | 0 < pullCount A (bestArm ν) s ω ∧
          empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω <
            (ν (bestArm ν))[id]}.indicator (1 : ℕ → ℕ) s +
      ∑ s ∈ range n,
        {s | 0 < pullCount A a s ω ∧ (ν a)[id] <
          empMean A R a s ω - ucbWidth A c a s ω}.indicator (1 : ℕ → ℕ) s ∂P := by
    refine lintegral_mono_ae ?_
    have hCa : C a ≠ 0 := by
      simp only [ne_eq, Nat.ceil_eq_zero, not_le, C]
      have : 0 < log (n + 1) := log_pos (by simp; grind)
      positivity
    filter_upwards [pullCount_ae_le_add_two h hc.le a h_gap n (C a) hCa (Nat.le_ceil _)] with ω hω
    simp only [id_eq, Nat.cast_sum]
    norm_cast
  _ ≤ (C a : ℝ≥0∞) + 1 +
      ∑ s ∈ range n,
        P {ω | 0 < pullCount A (bestArm ν) s ω ∧
          empMean A R (bestArm ν) s ω + ucbWidth A c (bestArm ν) s ω < (ν (bestArm ν))[id]} +
      ∑ s ∈ range n,
        P {ω | 0 < pullCount A a s ω ∧ (ν a)[id] < empMean A R a s ω - ucbWidth A c a s ω} := by
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
      ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c - 1) +
      ∑ s ∈ range n, 1 / ((s : ℝ≥0∞) + 1) ^ (c - 1) := by
    gcongr with s hs s hs
    · refine (measure_mono ?_).trans (prob_ucbIndex_le h hν hc.le (bestArm ν) s)
      grind
    · refine (measure_mono ?_).trans (prob_ucbIndex_ge h hν hc.le a s)
      grind
  _ ≤ ENNReal.ofReal (8 * c * log (n + 1) / gap ν a ^ 2 + 1) + 1 + 2 * constSum c n := by
    rw [two_mul, add_assoc, constSum]
    gcongr
    simp only [C]
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (Nat.ceil_lt_add_one ?_).le
    have : 0 ≤ log (n + 1) := log_nonneg (by simp)
    positivity

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (hc : 0 < c) (a : Fin K) (h_gap : 0 < gap ν a) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      8 * c * log (n + 1) / gap ν a ^ 2 + 2 + 2 * (constSum c n).toReal := by
  have hA := h.measurable_A
  have h := expectation_pullCount_le' h hν hc a h_gap n (hK := hK)
  simp_rw [← ENNReal.ofReal_natCast] at h
  rw [← ofReal_integral_eq_lintegral_ofReal] at h
  rotate_left
  · exact integrable_pullCount hA _ _
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
lemma regret_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (ucbAlgorithm hK c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (hc : 0 < c) (n : ℕ) :
    P[regret ν A n] ≤
      ∑ a, (8 * c * log (n + 1) / gap ν a + gap ν a * (2 + 2 * (constSum c n).toReal)) := by
  have hA := h.measurable_A
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · exact fun i _ ↦ (integrable_pullCount hA i n).mul_const _
  gcongr with a
  rw [integral_mul_const]
  by_cases h_gap : gap ν a = 0
  · simp [h_gap]
  replace h_gap : 0 < gap ν a := lt_of_le_of_ne gap_nonneg (Ne.symm h_gap)
  grw [expectation_pullCount_le h hν hc a h_gap n]
  refine le_of_eq ?_
  rw [mul_add]
  field

end UCB

end Bandits
