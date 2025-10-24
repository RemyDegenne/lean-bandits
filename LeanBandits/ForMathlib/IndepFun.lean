import Mathlib

open MeasureTheory Finset

namespace ProbabilityTheory

variable {α Ω Ω' E ι : Type*} [Countable ι] {mα : MeasurableSpace α}
  {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mE : MeasurableSpace E} {μ ν : Measure Ω}

lemma iIndepFun_nat_iff_forall_indepFun {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ) :
    iIndepFun X μ ↔ ∀ n, X (n + 1) ⟂ᵢ[μ] fun ω (i : Iic n) ↦ X i ω := by
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

-- todo: kernel version?
lemma IndepFun_map_iff [IsFiniteMeasure μ] {X : Ω' → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : AEMeasurable X (μ.map f)) (hY : AEMeasurable Y (μ.map f)) :
    X ⟂ᵢ[μ.map f] Y ↔ (X ∘ f) ⟂ᵢ[μ] (Y ∘ f) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY,
    indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable hY hf, AEMeasurable.map_map_of_aemeasurable hX hf,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma iIndepFun_map_iff [IsProbabilityMeasure μ] {X : ι → Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : ∀ n, AEMeasurable (X n) (μ.map f)) :
    iIndepFun X (μ.map f) ↔ iIndepFun (fun n ↦ X n ∘ f) μ := by
  have := Measure.isProbabilityMeasure_map hf (μ := μ)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hX,
    iIndepFun_iff_map_fun_eq_infinitePi_map₀' (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  congr! 3
  rw [AEMeasurable.map_map_of_aemeasurable (hX _) hf]

lemma identDistrib_map_right_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib X Y μ (ν.map f) ↔ IdentDistrib X (Y ∘ f) μ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable hY hf]

lemma identDistrib_comm (X : Ω → E) (Y : Ω' → E) {ν : Measure Ω'} :
    IdentDistrib X Y μ ν ↔ IdentDistrib Y X ν μ :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma identDistrib_map_left_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib Y X (ν.map f) μ ↔ IdentDistrib (Y ∘ f) X ν μ := by
  rw [identDistrib_comm Y, identDistrib_comm _ X]
  exact identDistrib_map_right_iff hf hX hY

end ProbabilityTheory
