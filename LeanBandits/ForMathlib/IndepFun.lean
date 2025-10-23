import Mathlib

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {μ : Measure Ω}

lemma iIndepFun_nat_iff_forall_indepFun {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ) :
    iIndepFun X μ ↔ ∀ n, (X (n + 1)) ⟂ᵢ[μ] (fun ω (i : Iic n) ↦ X i ω) := by
  constructor
  · intro h n
    have h' := h.indepFun_finset₀ {n + 1} (Iic n) (by simp) hX
    let f : (({n + 1} : Finset ℕ) → E) → E := fun x ↦ x ⟨n + 1, by simp⟩
    have hf : Measurable f := by unfold f; fun_prop
    have h_eq : X (n + 1) = f ∘ (fun ω (i : ({n + 1} : Finset ℕ)) ↦ X i ω) := rfl
    exact h'.comp (ψ := id) hf measurable_id
  · intro h
    suffices ∀ n, iIndepFun ((Iic n).restrict X) μ by
      rw [iIndepFun_iff_finset]
      intro s
      sorry
    intro n
    sorry

end ProbabilityTheory
