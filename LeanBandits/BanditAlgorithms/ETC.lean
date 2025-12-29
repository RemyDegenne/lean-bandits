/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.RewardByCountMeasure

/-! # The Explore-Then-Commit Algorithm

-/

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

section Aux

lemma ae_eq_set_iff {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s t : Set α} :
    s =ᵐ[μ] t ↔ ∀ᵐ a ∂μ, a ∈ s ↔ a ∈ t := by
  rw [Filter.EventuallyEq]
  simp only [eq_iff_iff]
  congr!

--todo: generalize Icc
lemma measurable_sum_of_le {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ} {g : α → ℕ} {n : ℕ} (hg_le : ∀ a, g a ≤ n) (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a) := by
  have h_eq : (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a)
      = fun a ↦ ∑ i ∈ range (n + 1), if g a = i then ∑ j ∈ Icc 1 i, f j a else 0 := by
    ext ω
    rw [sum_ite_eq_of_mem]
    grind
  rw [h_eq]
  refine measurable_sum _ fun n hn ↦ ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

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

end Aux

namespace Bandits

variable {K : ℕ}

section AlgorithmDefinition

/-- Arm pulled by the ETC algorithm at time `n + 1`.
For `n < K * m - 1`, this is arm `n % K`.
For `n = K * m - 1`, this is the arm with the highest empirical mean after the exploration phase.
For `n ≥ K * m`, this is the same arm as at time `n`. -/
noncomputable
def ETC.nextArm (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if hn : n < K * m - 1 then
    ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ -- for `n = 0` we have pulled arm 0 already, and we pull arm 1
  else
    if hn_eq : n = K * m - 1 then measurableArgmax (empMean' n) h
    else (h ⟨n, by simp⟩).1

/-- The next arm pulled by ETC is chosen in a measurable way. -/
@[fun_prop]
lemma ETC.measurable_nextArm (hK : 0 < K) (m n : ℕ) : Measurable (nextArm hK m n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold nextArm
  simp only [dite_eq_ite]
  refine Measurable.ite (by simp) (by fun_prop) ?_
  refine Measurable.ite (by simp) ?_ (by fun_prop)
  exact measurable_measurableArgmax fun a ↦ by fun_prop

/-- The Explore-Then-Commit algorithm: deterministic algorithm that chooses the next arm according
to `ETC.nextArm`. -/
noncomputable
def etcAlgorithm (hK : 0 < K) (m : ℕ) : Algorithm (Fin K) ℝ :=
  detAlgorithm (ETC.nextArm hK m) (by fun_prop) ⟨0, hK⟩

end AlgorithmDefinition

namespace ETC

variable {hK : 0 < K} {m : ℕ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]

local notation "𝔓t" => Bandit.trajMeasure (etcAlgorithm hK m) ν
local notation "𝔓" => Bandit.measure (etcAlgorithm hK m) ν

lemma arm_zero : arm 0 =ᵐ[𝔓t] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_zero_detAlgorithm

lemma arm_ae_eq_etcNextArm (n : ℕ) :
    arm (n + 1) =ᵐ[𝔓t] fun h ↦ nextArm hK m n (fun i ↦ h i) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_detAlgorithm_ae_eq n

/-- For `n < K * m`, the arm pulled at time `n` is the arm `n % K`. -/
lemma arm_of_lt {n : ℕ} (hn : n < K * m) :
    arm n =ᵐ[𝔓t] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ := by
  cases n with
  | zero => exact arm_zero
  | succ n =>
    filter_upwards [arm_ae_eq_etcNextArm n] with h hn_eq
    rw [hn_eq, nextArm, dif_pos]
    grind

/-- The arm pulled at time `K * m` is the arm with the highest empirical mean after the exploration
phase. -/
lemma arm_mul (hm : m ≠ 0) :
    have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    arm (K * m) =ᵐ[𝔓t] fun h ↦ measurableArgmax (empMean' (K * m - 1)) (fun i ↦ h i) := by
  have : K * m = (K * m - 1) + 1 := by
    have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind
  rw [this]
  filter_upwards [arm_ae_eq_etcNextArm (K * m - 1)] with h hn_eq
  rw [hn_eq, nextArm, dif_neg (by simp), dif_pos rfl]
  exact this ▸ rfl

/-- For `n ≥ K * m`, the arm pulled at time `n + 1` is the same as the arm pulled at time `n`. -/
lemma arm_add_one_of_ge {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) :
    arm (n + 1) =ᵐ[𝔓t] fun ω ↦ arm n ω := by
  filter_upwards [arm_ae_eq_etcNextArm n] with ω hn_eq
  rw [hn_eq, nextArm, dif_neg (by grind), dif_neg]
  · rfl
  · have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind

/-- For `n ≥ K * m`, the arm pulled at time `n` is the same as the arm pulled at time `K * m`. -/
lemma arm_of_ge {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) :
    arm n =ᵐ[𝔓t] arm (K * m) := by
  have h_ae n : K * m ≤ n → arm (n + 1) =ᵐ[𝔓t] fun ω ↦ arm n ω := arm_add_one_of_ge hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω h_ae
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hmn h_ind => rw [h_ae n hmn, h_ind]

/-- At time `K * m`, the number of pulls of each arm is equal to `m`. -/
lemma pullCount_mul (a : Fin K) : pullCount a (K * m) =ᵐ[𝔓t] fun _ ↦ m := by
  rw [Filter.EventuallyEq]
  simp_rw [pullCount_eq_sum]
  have h_arm (n : range (K * m)) : arm n =ᵐ[𝔓t] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ :=
    arm_of_lt (mem_range.mp n.2)
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_arm
  filter_upwards [h_arm] with ω h_arm
  have h_arm' {i : ℕ} (hi : i ∈ range (K * m)) : arm i ω = ⟨i % K, Nat.mod_lt _ hK⟩ := h_arm ⟨i, hi⟩
  calc (∑ s ∈ range (K * m), if arm s ω = a then 1 else 0)
  _ = (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) :=
    sum_congr rfl fun s hs ↦ by rw [h_arm' hs]
  _ = m := sum_mod_range_mul hK m a

lemma pullCount_add_one_of_ge (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount a (n + 1)
      =ᵐ[𝔓t] fun ω ↦ pullCount a n ω + {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  simp_rw [Filter.EventuallyEq, pullCount_add_one]
  filter_upwards [arm_of_ge hm hn] with ω h_arm
  congr 3

/-- For `n ≥ K * m`, the number of pulls of each arm `a` at time `n` is equal to `m` plus
`n - K * m` if arm `a` is the best arm after the exploration phase. -/
lemma pullCount_of_ge (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount a n
      =ᵐ[𝔓t] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  have h_ae n : K * m ≤ n → pullCount a (n + 1)
      =ᵐ[𝔓t] fun ω ↦ pullCount a n ω + {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω :=
    pullCount_add_one_of_ge a hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  have h_ae_Km : pullCount a (K * m) =ᵐ[𝔓t] fun _ ↦ m := pullCount_mul a
  filter_upwards [h_ae_Km, h_ae] with ω h_Km h_ae
  induction n, hn using Nat.le_induction with
  | base => simp [h_Km]
  | succ n hmn h_ind =>
    rw [h_ae n hmn, h_ind, add_assoc, ← add_one_mul]
    congr
    grind

/-- If at time `K * m` the algorithm chooses arm `a`, then the total reward obtained by pulling
arm `a` is at least the total reward obtained by pulling the best arm. -/
lemma sumRewards_bestArm_le_of_arm_mul_eq (a : Fin K) (hm : m ≠ 0) :
    have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    ∀ᵐ h ∂𝔓t, arm (K * m) h = a → sumRewards (bestArm ν) (K * m) h ≤ sumRewards a (K * m) h := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  filter_upwards [arm_mul hm, pullCount_mul a, pullCount_mul (bestArm ν)] with h h_arm ha h_best
    h_eq
  have h_max := isMaxOn_measurableArgmax (empMean' (K * m - 1)) (fun i ↦ h i) (bestArm ν)
  rw [← h_arm, h_eq] at h_max
  rw [sumRewards_eq_pullCount_mul_empMean, sumRewards_eq_pullCount_mul_empMean, ha, h_best]
  · gcongr
    have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    rwa [empMean_eq_empMean' this.ne', empMean_eq_empMean' this.ne']
  · simp [ha, hm]
  · simp [h_best, hm]

lemma identDistrib_aux (m : ℕ) (a b : Fin K) :
    IdentDistrib
      (fun ω ↦ (∑ s ∈ Icc 1 m, rewardByCount a s ω, ∑ s ∈ Icc 1 m, rewardByCount b s ω))
      (fun ω ↦ (∑ s ∈ range m, ω.2 s a, ∑ s ∈ range m, ω.2 s b)) 𝔓 𝔓 := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h2 (a : Fin K) : IdentDistrib (fun ω ↦ ∑ s ∈ Icc 1 m, rewardByCount a s ω)
      (fun ω ↦ ∑ s ∈ range m, ω.2 s a) 𝔓 𝔓 := identDistrib_sum_Icc_rewardByCount m a
  by_cases hab : a = b
  · simp only [hab]
    exact (h2 b).comp (u := fun p ↦ (p, p)) (by fun_prop)
  refine (h2 a).prodMk (h2 b) ?_ ?_
  · suffices IndepFun (fun ω s ↦ rewardByCount a s ω) (fun ω s ↦ rewardByCount b s ω)
        𝔓 by
      exact this.comp (φ := fun p ↦ ∑ i ∈ Icc 1 m, p i) (ψ := fun p ↦ ∑ j ∈ Icc 1 m, p j)
        (by fun_prop) (by fun_prop)
    exact indepFun_rewardByCount_of_ne hab
  · suffices IndepFun (fun ω s ↦ ω.2 s a) (fun ω s ↦ ω.2 s b) 𝔓 by
      exact this.comp (φ := fun p ↦ ∑ i ∈ range m, p i) (ψ := fun p ↦ ∑ j ∈ range m, p j)
        (by fun_prop) (by fun_prop)
    exact indepFun_eval_snd_measure _ ν hab

/-- The probability that at time `K * m` the ETC algorithm chooses arm `a` is at most
`exp(- m * Δ_a^2 / 4)`. -/
lemma prob_arm_mul_eq_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (a : Fin K)
    (hm : m ≠ 0) :
    (𝔓t).real {ω | arm (K * m) ω = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h_pos : 0 < K * m := Nat.mul_pos hK hm.bot_lt
  have h_le : (𝔓t).real {ω | arm (K * m) ω = a}
      ≤ (𝔓t).real {ω | sumRewards (bestArm ν) (K * m) ω ≤ sumRewards a (K * m) ω} := by
    simp_rw [measureReal_def]
    gcongr 1
    · simp
    refine measure_mono_ae ?_
    exact sumRewards_bestArm_le_of_arm_mul_eq a hm
  refine h_le.trans ?_
  -- extend the probability space to include the stream of independent rewards
  suffices (𝔓).real {ω | sumRewards (bestArm ν) (K * m) ω.1 ≤ sumRewards a (K * m) ω.1}
      ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) by
    suffices (𝔓t).real {ω | sumRewards (bestArm ν) (K * m) ω ≤ sumRewards a (K * m) ω}
      = (𝔓).real {ω | sumRewards (bestArm ν) (K * m) ω.1 ≤ sumRewards a (K * m) ω.1} by rwa [this]
    calc (𝔓t).real {ω | sumRewards (bestArm ν) (K * m) ω ≤ sumRewards a (K * m) ω}
    _ = ((𝔓).fst).real {ω | sumRewards (bestArm ν) (K * m) ω ≤ sumRewards a (K * m) ω} := by simp
    _ = (𝔓).real {ω | sumRewards (bestArm ν) (K * m) ω.1 ≤ sumRewards a (K * m) ω.1} := by
      rw [Measure.fst, map_measureReal_apply (by fun_prop)]
      · rfl
      · exact measurableSet_le (by fun_prop) (by fun_prop)
  calc (𝔓).real {ω | sumRewards (bestArm ν) (K * m) ω.1 ≤ sumRewards a (K * m) ω.1}
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 (pullCount (bestArm ν) (K * m) ω.1), rewardByCount (bestArm ν) s ω
      ≤ ∑ s ∈ Icc 1 (pullCount a (K * m) ω.1), rewardByCount a s ω} := by
    congr with ω
    congr! 1 <;> rw [sum_rewardByCount_eq_sumRewards]
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 m, rewardByCount (bestArm ν) s ω
      ≤ ∑ s ∈ Icc 1 m, rewardByCount a s ω} := by
    simp_rw [measureReal_def]
    congr 1
    refine measure_congr ?_
    have ha := pullCount_mul a (hK := hK) (ν := ν) (m := m)
    have h_best := pullCount_mul (bestArm ν) (hK := hK) (ν := ν) (m := m)
    rw [ae_eq_set_iff]
    change ∀ᵐ ω ∂((𝔓t).prod _), _
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [ha, h_best] with ω ha h_best
      refine ae_of_all _ fun ω' ↦ ?_
      rw [ha, h_best]
    · simp only [Set.mem_setOf_eq]
      let f₁ := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦
        ∑ s ∈ Icc 1 (pullCount (bestArm ν) (K * m) ω.1), rewardByCount (bestArm ν) s ω
      let g₁ := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦
        ∑ s ∈ Icc 1 (pullCount a (K * m) ω.1), rewardByCount a s ω
      let f₂ := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦
        ∑ s ∈ Icc 1 m, rewardByCount (bestArm ν) s ω
      let g₂ := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦ ∑ s ∈ Icc 1 m, rewardByCount a s ω
      change MeasurableSet {x | f₁ x ≤ g₁ x ↔ f₂ x ≤ g₂ x}
      have hf₁ : Measurable f₁ := by
        refine measurable_sum_of_le (n := K * m + 1)
          (g := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦ pullCount (bestArm ν) (K * m) ω.1)
          (f := rewardByCount (bestArm ν)) (fun ω ↦ ?_)
          (by fun_prop) (by fun_prop)
        have h_le := pullCount_le (bestArm ν) (K * m) ω.1
        grind
      have hg₁ : Measurable g₁ := by
        refine measurable_sum_of_le (n := K * m + 1)
          (g := fun ω : (ℕ → Fin K × ℝ) × (ℕ → Fin K → ℝ) ↦ pullCount a (K * m) ω.1)
          (f := rewardByCount a) (fun ω ↦ ?_) (by fun_prop) (by fun_prop)
        have h_le := pullCount_le a (K * m) ω.1
        grind
      refine MeasurableSet.iff ?_ ?_
      · exact measurableSet_le (by fun_prop) (by fun_prop)
      · exact measurableSet_le (by fun_prop) (by fun_prop)
  _ = (𝔓).real {ω | ∑ s ∈ range m, ω.2 s (bestArm ν) ≤ ∑ s ∈ range m, ω.2 s a} := by
    simp_rw [measureReal_def]
    congr 1
    have : (𝔓).map (fun ω ↦ (∑ s ∈ Icc 1 m, rewardByCount (bestArm ν) s ω,
          ∑ s ∈ Icc 1 m, rewardByCount a s ω))
        = (𝔓).map (fun ω ↦ (∑ s ∈ range m, ω.2 s (bestArm ν), ∑ s ∈ range m, ω.2 s a)) :=
      (identDistrib_aux m (bestArm ν) a).map_eq
    rw [Measure.ext_iff] at this
    have h_meas : MeasurableSet {x : ℝ × ℝ | x.1 ≤ x.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    specialize this {x | x.1 ≤ x.2} h_meas
    rwa [Measure.map_apply (by fun_prop) h_meas, Measure.map_apply (by fun_prop) h_meas] at this
  _ = (Bandit.streamMeasure ν).real
      {ω | ∑ s ∈ range m, ω s (bestArm ν) ≤ ∑ s ∈ range m, ω s a} := by
    simp_rw [measureReal_def]
    congr 1
    rw [← Bandit.snd_measure (etcAlgorithm hK m), Measure.snd_apply]
    · rfl
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  _ ≤ Real.exp (-↑m * gap ν a ^ 2 / 4) := by
    by_cases ha : a = bestArm ν
    · simp [ha]
    -- Apply a sub-Gaussian concentration inequality
    refine (HasSubgaussianMGF.measure_sum_le_sum_le' (cX := fun _ ↦ 1) (cY := fun _ ↦ 1)
      ?_ ?_ ?_ ?_ ?_ ?_).trans_eq ?_
    · exact iIndepFun_eval_streamMeasure'' ν (bestArm ν)
    · exact iIndepFun_eval_streamMeasure'' ν a
    · intro i him
      simp_rw [integral_eval_streamMeasure]
      refine (hν (bestArm ν)).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
    · intro i him
      simp_rw [integral_eval_streamMeasure]
      refine (hν a).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
    · exact indepFun_eval_streamMeasure' ν (Ne.symm ha)
    · gcongr 1 with i him
      simp_rw [integral_eval_streamMeasure]
      exact le_bestArm a
    · congr 1
      simp_rw [integral_eval_streamMeasure]
      simp only [id_eq, sum_const, card_range, nsmul_eq_mul, mul_one, NNReal.coe_natCast,
        gap_eq_bestArm_sub, neg_mul]
      field_simp
      ring

/-- Bound on the expectation of the number of pulls of each arm by the ETC algorithm. -/
lemma expectation_pullCount_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    𝔓t[fun ω ↦ (pullCount a n ω : ℝ)]
      ≤ m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : (fun ω ↦ (pullCount a n ω : ℝ))
      =ᵐ[𝔓t] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
    filter_upwards [pullCount_of_ge a hm hn] with ω h
    simp only [h, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero, Nat.cast_add,
      Nat.cast_ite, CharP.cast_eq_zero, add_right_inj]
    norm_cast
  rw [integral_congr_ae this, integral_add (integrable_const _), integral_const_mul]
  swap
  · refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff]
    · exact integrableOn_const
    · exact (measurableSet_singleton _).preimage (by fun_prop)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, neg_mul, add_le_add_iff_left]
  gcongr
  · norm_cast
    simp
  rw [integral_indicator_const, smul_eq_mul, mul_one]
  · rw [← neg_mul]
    exact prob_arm_mul_eq_le hν a hm
  · exact (measurableSet_singleton _).preimage (by fun_prop)

/-- Regret bound for the ETC algorithm. -/
lemma regret_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (hm : m ≠ 0)
    (n : ℕ) (hn : K * m ≤ n) :
    𝔓t[regret ν n] ≤ ∑ a, gap ν a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4)) := by
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · exact fun i _ ↦ (integrable_pullCount i n).mul_const _
  gcongr with a
  rw [mul_comm (gap _ _), integral_mul_const]
  gcongr
  · exact gap_nonneg
  · exact expectation_pullCount_le hν a hm hn

end ETC

end Bandits
