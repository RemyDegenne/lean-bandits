/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.Algorithm

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
def stationaryEnv (ν : Kernel α R) [IsMarkovKernel ν] : Environment α R where
  feedback _ := ν.prodMkLeft _
  ν0 := ν

variable {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]

local notation "𝔓" => trajMeasure alg (stationaryEnv ν)

/-- The conditional distribution of the reward at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_reward_stationaryEnv [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace R] [Nonempty R] (n : ℕ) :
    condDistrib (reward n) (action n) 𝔓 =ᵐ[(𝔓).map (action n)] ν := by
  cases n with
  | zero =>
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
    change (𝔓).map (step 0) = (𝔓).map (action 0) ⊗ₘ ν
    rw [(hasLaw_action_zero alg (stationaryEnv ν)).map_eq,
      (hasLaw_step_zero alg (stationaryEnv ν)).map_eq, stationaryEnv_ν0]
  | succ n =>
    have h_eq := condDistrib_reward alg (stationaryEnv ν) n
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_eq ⊢
    have : (𝔓).map (action (n + 1)) = ((𝔓).map (fun x ↦ (hist n x, action (n + 1) x))).snd := by
      rw [Measure.snd_map_prodMk (by fun_prop)]
    simp only [stationaryEnv_feedback] at h_eq
    rw [this, ← Measure.snd_prodAssoc_compProd_prodMkLeft, ← h_eq,
      Measure.snd_map_prodMk (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_reward_hist_action [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace R] [Nonempty R] (n : ℕ) :
    reward (n + 1) ⟂ᵢ[action (n + 1), measurable_action _ ; 𝔓] hist n :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (by fun_prop) (by fun_prop) (by fun_prop) (condDistrib_reward alg (stationaryEnv ν) n)

end Learning
