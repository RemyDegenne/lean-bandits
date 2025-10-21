import Mathlib

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {μ : Measure Ω}

lemma iIndepFun_nat_iff_forall_indepFun {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ) :
    iIndepFun X μ ↔ ∀ n, (X (n + 1)) ⟂ᵢ[μ] (fun ω (i : Iic n) ↦ X i ω) := by
  constructor
  · intro h n
    have h' := h.indepFun_finset₀ {n + 1} (Iic n) (by simp) hX
    sorry
  · intro h
    rw [iIndepFun_iff_finset]
    intro s
    sorry

end ProbabilityTheory
