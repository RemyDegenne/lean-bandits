import Mathlib.Probability.Moments.SubGaussian
import LeanBandits.Bandit
import LeanBandits.Regret

/-! # The Explore-Then-Commit Algorithm

-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Bandits

def etcArm {K : ℕ} (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  if hn : n < K * m - 1 then
    ⟨n % K, Nat.mod_lt _ hK⟩
  else
    if hn_eq : n = K * m - 1 then
      let hatμ a := (∑ s : Iic n, if (h s).1 = a then (h s).2 else 0) / m
      ⟨0, hK⟩ -- TODO placeholder, replace by the argmax
    else
      have : 0 < n := by grind
      (h ⟨n - 1, by simp⟩).1

@[fun_prop]
lemma measurable_etcArm {K : ℕ} (hK : 0 < K) (m n : ℕ) : Measurable (etcArm hK m n) := by
  unfold etcArm
  simp only [dite_eq_ite]
  fun_prop

/-- The Explore-Then-Commit Kernel, which describes the arm pulled by the ETC algorithm. -/
noncomputable
def etcKernel {K : ℕ} (hK : 0 < K) (m n : ℕ) : Kernel (Iic n → Fin K × ℝ) (Fin K) :=
  Kernel.deterministic (etcArm hK m n) (by fun_prop)

end Bandits
