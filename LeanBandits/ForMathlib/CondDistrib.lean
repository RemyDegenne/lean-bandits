/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Condexp


open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {α β γ Ω Ω' : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
  {X : α → β} {Y : α → Ω} {Z : α → Ω'} {T : α → γ}

@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

@[fun_prop]
lemma Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf

namespace MeasureTheory.Measure

lemma comp_congr {κ η : Kernel α β} (h : ∀ᵐ a ∂μ, κ a = η a) :
    κ ∘ₘ μ = η ∘ₘ μ :=
  bind_congr_right h

lemma copy_comp_map (hX : AEMeasurable X μ) :
    Kernel.copy β ∘ₘ (μ.map X) = μ.map (fun a ↦ (X a, X a)) := by
  rw [Kernel.copy, deterministic_comp_eq_map, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  congr

lemma compProd_deterministic [SFinite μ] (hX : Measurable X) :
    μ ⊗ₘ Kernel.deterministic X hX = μ.map (fun a ↦ (a, X a)) := by
  rw [compProd_eq_comp_prod, Kernel.id, Kernel.deterministic_prod_deterministic,
    deterministic_comp_eq_map]
  rfl

end MeasureTheory.Measure

namespace ProbabilityTheory

lemma condDistrib_comp_map [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hY, Measure.snd_map_prodMk₀ hX]

lemma condDistrib_congr [IsFiniteMeasure μ] {X' : α → β} {Y' : α → Ω}
    (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y' X' μ := by
  rw [condDistrib, condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

lemma condDistrib_congr_right [IsFiniteMeasure μ] {X' : α → β} (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y X' μ :=
  condDistrib_congr (by rfl) hX

lemma condDistrib_congr_left [IsFiniteMeasure μ] {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') :
    condDistrib Y X μ = condDistrib Y' X μ :=
  condDistrib_congr hY (by rfl)

lemma condDistrib_ae_eq_of_measure_eq_compProd₀ [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    ∀ᵐ x ∂μ.map X, κ x = condDistrib Y X μ x := by
  suffices ∀ᵐ x ∂μ.map (hX.mk X), κ x = condDistrib (hY.mk Y) (hX.mk X) μ x by
    rw [Measure.map_congr hX.ae_eq_mk]
    convert this using 3 with b
    rw [condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) hX.measurable_mk hY.measurable_mk κ
    ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

lemma condDistrib_comp [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) {f : β → Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ hX (by fun_prop) _ ?_
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  rfl

lemma condDistrib_const [IsFiniteMeasure μ]
    (hX : AEMeasurable X μ) (c : Ω) :
    condDistrib (fun _ ↦ c) X μ =ᵐ[μ.map X] Kernel.deterministic (fun _ ↦ c) (by fun_prop) := by
  have : (fun _ : α ↦ c) = (fun _ : β ↦ c) ∘ X := rfl
  conv_lhs => rw [this]
  filter_upwards [condDistrib_comp hX (by fun_prop : Measurable (fun _ ↦ c))] with b hb
  rw [hb]

lemma condDistrib_ae_eq_cond [Countable β] [MeasurableSingletonClass β]
    [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib Y X μ =ᵐ[μ.map X] fun b ↦ (μ[|X ⁻¹' {b}]).map Y := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro b hb
  ext s hs
  rw [condDistrib_apply_of_ne_zero hY,
    Measure.map_apply hX (measurableSet_singleton _), Measure.map_apply hY hs,
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs),
    cond_apply (hX (measurableSet_singleton _))]
  · congr
  · exact hb

lemma ae_cond_of_forall_mem {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ[|s], p x := Measure.ae_smul_measure (ae_restrict_of_forall_mem hs h) _

lemma condDistrib_of_indepFun [IsZeroOrProbabilityMeasure μ] (h : IndepFun X Y μ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) hX hY _ ?_
  simp only [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h

lemma indepFun_iff_condDistrib_eq_const [IsZeroOrProbabilityMeasure μ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine ⟨fun h ↦ condDistrib_of_indepFun h hX hY, fun h ↦ ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← compProd_map_condDistrib hY,
    Measure.compProd_congr h]
  simp

lemma cond_of_indepFun [IsZeroOrProbabilityMeasure μ] (h : IndepFun X T μ)
    (hX : Measurable X) (hT : Measurable T) {s : Set β} (hs : MeasurableSet s)
    (hμs : μ (X ⁻¹' s) ≠ 0) :
    (μ[|X ⁻¹' s]).map T = μ.map T := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht, Measure.map_apply (by fun_prop) ht, cond_apply (hX hs),
    IndepSet.measure_inter_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · exact hμs
  · simp
  · rw [indepFun_iff_indepSet_preimage hX hT] at h
    exact h s t hs ht

lemma condIndep_iff_condExpKernel_eq {α : Type*} {F G H mα : MeasurableSpace α}
    [StandardBorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hG : G ≤ mα) :
    CondIndep G F H hG μ
      ↔ condExpKernel μ (F ⊔ G) =ᵐ[@Measure.map  _ _ mα H id μ] condExpKernel μ G := by
  sorry

lemma condDistrib_of_condIndepFun
    [StandardBorelSpace α] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ) :
    condDistrib Y (fun ω ↦ (X ω, Z ω)) μ
      =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] fun p ↦ condDistrib Y Z μ p.2 := by
  sorry

lemma cond_of_condIndepFun [StandardBorelSpace α] [IsZeroOrProbabilityMeasure μ]
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ)
    (hX : Measurable X) (hY : Measurable Y) {s : Set β} (hs : MeasurableSet s) {t : Set Ω'}
    (ht : MeasurableSet t) (hμs : μ (Z ⁻¹' t) ≠ 0) :
    (μ[|X ⁻¹' s ∩ Z ⁻¹' t]).map Y = (μ[|Z ⁻¹' t]).map Y := by
  ext u hu
  rw [Measure.map_apply (by fun_prop) hu, Measure.map_apply (by fun_prop) hu, cond_apply,
    cond_apply]
  rotate_left
  · exact hZ ht
  · exact (hX hs).inter (hZ ht)
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hY hX] at h
  specialize h u s hu hs
  sorry

end ProbabilityTheory
