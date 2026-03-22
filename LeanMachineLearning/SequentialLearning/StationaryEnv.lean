/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Stationary environments
-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

/-- A stationary environment, in which the distribution of the next reward depends only on the last
action. -/
@[simps]
-- ANCHOR: stationaryEnv
def stationaryEnv (ν : Kernel α R) [IsMarkovKernel ν] : Environment α R where
  feedback _ := ν.prodMkLeft _
  ν0 := ν
-- ANCHOR_END: stationaryEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

namespace IsAlgEnvSeq

/-- The conditional distribution of the reward at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_reward_stationaryEnv
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    condDistrib (R' n) (A n) P =ᵐ[P.map (A n)] ν := by
  have hA := h.measurable_A
  have hR' := h.measurable_R
  cases n with
  | zero =>
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
    change P.map (step A R' 0) = P.map (A 0) ⊗ₘ ν
    rw [(hasLaw_action_zero h).map_eq, (hasLaw_step_zero h).map_eq, stationaryEnv_ν0]
  | succ n =>
    have h_eq := (h.hasCondDistrib_reward n).condDistrib_eq
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_eq ⊢
    have : P.map (A (n + 1)) =
        (P.map (fun x ↦ (hist A R' n x, A (n + 1) x))).snd := by
      rw [Measure.snd_map_prodMk (by fun_prop)]
    simp only [stationaryEnv_feedback] at h_eq
    rw [this, ← Measure.snd_prodAssoc_compProd_prodMkLeft, ← h_eq,
      Measure.snd_map_prodMk (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_reward_hist_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_A _ ; P] hist A R' n := by
  have hA := h.measurable_A
  have hR' := h.measurable_R
  exact condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (by fun_prop) (by fun_prop) (by fun_prop) (h.hasCondDistrib_reward n).condDistrib_eq

lemma condIndepFun_reward_hist_action_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_A (n + 1); P]
      (fun ω ↦ (hist A R' n ω, A (n + 1) ω)) := by
  have h_indep : R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_A (n + 1); P] hist A R' n := by
    convert h.condIndepFun_reward_hist_action n
  have hA := h.measurable_A
  have hR' := h.measurable_R
  exact h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)

lemma condIndepFun_reward_hist_action_action' [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) (hn : n ≠ 0) :
    R' n ⟂ᵢ[A n, h.measurable_A n; P] (fun ω ↦ (hist A R' (n - 1) ω, A n ω)) := by
  have := h.condIndepFun_reward_hist_action_action (n - 1)
  grind

end IsAlgEnvSeq

namespace IT

local notation "𝔓" => trajMeasure alg (stationaryEnv ν)

/-- The conditional distribution of the reward at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_reward_stationaryEnv (n : ℕ) :
    condDistrib (IT.reward n) (IT.action n) 𝔓 =ᵐ[(𝔓).map (IT.action n)] ν :=
  IsAlgEnvSeq.condDistrib_reward_stationaryEnv
    (IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)) n

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_reward_hist_action (n : ℕ) :
    IT.reward (n + 1) ⟂ᵢ[IT.action (n + 1), IT.measurable_action _ ; 𝔓] IT.hist n :=
  IsAlgEnvSeq.condIndepFun_reward_hist_action
    (IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)) n

lemma condIndepFun_reward_hist_action_action
    {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν] (n : ℕ) :
    reward (n + 1) ⟂ᵢ[action (n + 1), measurable_action (n + 1); trajMeasure alg (stationaryEnv ν)]
      (fun ω ↦ (hist n ω, action (n + 1) ω)) :=
  IsAlgEnvSeq.condIndepFun_reward_hist_action_action
    (IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)) n

lemma condIndepFun_reward_hist_action_action'
    {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν] (n : ℕ) (hn : n ≠ 0) :
    reward n ⟂ᵢ[action n, measurable_action n; trajMeasure alg (stationaryEnv ν)]
      (fun ω ↦ (hist (n - 1) ω, action n ω)) :=
  IsAlgEnvSeq.condIndepFun_reward_hist_action_action'
    (IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν)) n hn

end IT

end Learning
