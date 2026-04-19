/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Independence.CondDistrib
public import Mathlib.Probability.HasLaw

/-!
# A predicate for having a specified conditional distribution
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] [Nonempty Ω']
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `μ`
is equal to the kernel `κ`. -/
structure HasCondDistrib (Y : α → Ω) (X : α → β) (κ : Kernel β Ω)
  (μ : Measure α) [IsFiniteMeasure μ] : Prop where
  aemeasurable_fst : AEMeasurable Y μ := by fun_prop
  aemeasurable_snd : AEMeasurable X μ := by fun_prop
  condDistrib_eq : condDistrib Y X μ =ᵐ[μ.map X] κ

attribute [fun_prop] HasCondDistrib.aemeasurable_fst HasCondDistrib.aemeasurable_snd

lemma hasCondDistrib_fst_prod {Y : α → Ω} {X : α → β}
    {κ : Kernel β Ω}
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure γ} [IsProbabilityMeasure ν]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) κ (μ.prod ν) where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have : ((μ.prod ν).map (fun ω ↦ X ω.1)) = μ.map X := by
      conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst]
      rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
      · rfl
      · have := h.aemeasurable_snd
        simpa
    rw [this]
    exact (condDistrib_fst_prod X h.aemeasurable_fst ν).trans h.condDistrib_eq

lemma HasCondDistrib.comp [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) {f : Ω → Ω'} (hf : Measurable f) :
    HasCondDistrib (fun ω ↦ f (Y ω)) X (κ.map f) μ where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have h_comp := condDistrib_comp X (Y := Y) (f := f) (mβ := mβ) h.aemeasurable_fst hf
    refine h_comp.trans ?_
    have h' := h.condDistrib_eq
    filter_upwards [h'] with ω hω
    rw [Kernel.map_apply _ hf, hω, Kernel.map_apply _ hf]

lemma HasCondDistrib.fst {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst μ := by
  rw [Kernel.fst_eq]
  exact HasCondDistrib.comp h measurable_fst

lemma HasCondDistrib.snd {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd μ := by
  rw [Kernel.snd_eq]
  exact HasCondDistrib.comp h measurable_snd

lemma HasCondDistrib.comp_right [IsFiniteMeasure μ] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    (f : β ≃ᵐ γ) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm (by fun_prop) : Kernel γ Ω) μ := by
  have hY := h.aemeasurable_fst
  have hX := h.aemeasurable_snd
  refine ⟨h.aemeasurable_fst, by fun_prop, ?_⟩
  have h_eq := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop) _] at h_eq ⊢
  calc μ.map (fun ω ↦ ((f ∘ X) ω, Y ω))
  _ = μ.map ((fun p ↦ (f p.1, p.2)) ∘ fun ω ↦ (X ω, Y ω)) := by congr
  _ = (μ.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (f p.1, p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  _ = (μ.map X ⊗ₘ κ).map (fun p ↦ (f p.1, p.2)) := by rw [h_eq]
  _ = μ.map (f ∘ X) ⊗ₘ (κ.comap f.symm (by fun_prop)) := by
    -- this is probably very inefficient.
    have hX_eq : X = f.symm ∘ (f ∘ X) := by ext; simp
    conv_lhs => rw [hX_eq]
    rw [← AEMeasurable.map_map_of_aemeasurable, Measure.compProd_eq_comp_prod,
      ← Measure.deterministic_comp_eq_map (f := f.symm), ← Measure.deterministic_comp_eq_map]
    rotate_left
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    rw [← Kernel.comp_deterministic_eq_comap, Measure.compProd_eq_comp_prod]
    simp_rw [Measure.comp_assoc]
    congr 1
    ext c : 1
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.prod_apply, Kernel.comp_apply]
    simp only [Kernel.deterministic_apply, Kernel.id_apply, Measure.dirac_bind κ.measurable,
      Measure.dirac_bind (Kernel.id ×ₖ κ).measurable, Kernel.prod_apply,
      Measure.deterministic_comp_eq_map]
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply, Measure.prod_apply,
      lintegral_dirac', lintegral_dirac']
    · congr
      ext
      simp
    · exact measurable_measure_prodMk_left hs
    · exact measurable_measure_prodMk_left (hs.preimage (by fun_prop))
    · exact hs
    · exact hs.preimage (by fun_prop)

lemma HasCondDistrib.prod_right [IsFiniteMeasure μ] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ := by
  have hY := h.aemeasurable_fst
  have hX := h.aemeasurable_snd
  refine ⟨h.aemeasurable_fst, by fun_prop, ?_⟩
  have h_eq := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop) _] at h_eq ⊢
  calc μ.map (fun x ↦ ((X x, f (X x)), Y x))
  _ = (μ.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ ((p.1, f p.1), p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = (μ.map X ⊗ₘ κ).map (fun p ↦ ((p.1, f p.1), p.2)) := by rw [h_eq]
  _ = (μ.map X).map (fun a ↦ (a, f a)) ⊗ₘ κ.prodMkRight γ := by
    rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod,
      ← Measure.deterministic_comp_eq_map (f := fun a ↦ (a, f a)),
      ← Measure.deterministic_comp_eq_map, Measure.comp_assoc, Measure.comp_assoc]
    swap; · fun_prop
    swap; · fun_prop
    congr 1
    ext b : 1
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.id_apply, Measure.dirac_bind (Kernel.measurable _), Kernel.prod_apply,
      Measure.deterministic_comp_eq_map, Kernel.prodMkRight_apply, Kernel.id_apply]
    change Measure.map (Prod.map (fun x ↦ (x, f x)) id) ((Measure.dirac b).prod (κ b)) =
      (Measure.dirac (b, f b)).prod (κ b)
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
      Measure.map_dirac' (by fun_prop)]
  _ = μ.map (fun a ↦ (X a, f (X a))) ⊗ₘ κ.prodMkRight γ := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr

lemma hasCondDistrib_prod_right_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] (X : α → β) (Y : α → Ω)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ ↔ HasCondDistrib Y X κ μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.prod_right hf⟩
  have hX : AEMeasurable X μ := by
    have := h.aemeasurable_snd
    have h_eq : X = (fun p ↦ p.1) ∘ (fun a ↦ (X a, f (X a))) := by ext; simp
    rw [h_eq]
    exact Measurable.comp_aemeasurable (by fun_prop) (by fun_prop)
  have hY := h.aemeasurable_fst
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_eq := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop) _] at h_eq ⊢
  calc μ.map (fun x ↦ (X x, Y x))
  _ = (μ.map (fun ω ↦ ((X ω, f (X ω)), Y ω))).map (fun p ↦ (p.1.1, p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = (μ.map (fun a ↦ (X a, f (X a))) ⊗ₘ κ.prodMkRight γ).map (fun p ↦ (p.1.1, p.2)) := by rw [h_eq]
  _ = ((μ.map X).map (fun a ↦ (a, f a)) ⊗ₘ κ.prodMkRight γ).map (fun p ↦ (p.1.1, p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = μ.map X ⊗ₘ κ := by
    simp_rw [Measure.compProd_eq_comp_prod,
      ← Measure.deterministic_comp_eq_map (f := fun a ↦ (a, f a)) (by fun_prop),
      ← Measure.deterministic_comp_eq_map (f := fun p : (β × γ) × Ω ↦ (p.1.1, p.2)) (by fun_prop),
      Measure.comp_assoc]
    congr 1
    ext b : 1
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
      Kernel.deterministic_apply, Measure.dirac_bind (Kernel.measurable _),
      Kernel.prod_apply, Measure.deterministic_comp_eq_map, Kernel.prodMkRight_apply,
      Kernel.id_apply]
    change Measure.map (Prod.map (fun x ↦ x.1) id) ((Measure.dirac (b, f b)).prod (κ b)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
      Measure.map_dirac' (by fun_prop)]

lemma HasLaw.prod_of_hasCondDistrib {P : Measure β} [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    (h1 : HasLaw X P μ) (h2 : HasCondDistrib Y X κ μ) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (P ⊗ₘ κ) μ := by
  have hX := h1.aemeasurable
  have hY := h2.aemeasurable_fst
  refine ⟨by fun_prop, ?_⟩
  rw [← compProd_map_condDistrib (by fun_prop), h1.map_eq]
  refine Measure.compProd_congr ?_
  rw [← h1.map_eq]
  exact h2.condDistrib_eq

lemma HasCondDistrib.prod [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {Z : α → Ω'} {η : Kernel (β × Ω) Ω'} [IsFiniteKernel η]
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  have hX := h1.aemeasurable_snd
  have hY := h1.aemeasurable_fst
  have hZ := h2.aemeasurable_fst
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_condDistrib_Y := h1.condDistrib_eq
  have h_condDistrib_Z := h2.condDistrib_eq
  have h_prod := condDistrib_prod_left hY hZ hX
  have h_prod' : 𝓛[fun ω ↦ (Y ω, Z ω) | X; μ] =ᵐ[μ.map X] (κ ⊗ₖ 𝓛[Z | fun ω ↦ (X ω, Y ω); μ]) := by
    filter_upwards [h_condDistrib_Y, h_prod] with ω hω₁ hω₂
    rw [hω₂]
    ext s hs
    rw [Kernel.compProd_apply hs, Kernel.compProd_apply hs]
    simp [hω₁]
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
    at h_condDistrib_Z h_condDistrib_Y ⊢
  rw [← Measure.compProd_assoc', ← h_condDistrib_Y, ← h_condDistrib_Z,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma hasLaw_of_hasCondDistrib_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const _ Q) μ) : HasLaw Y Q μ := by
  obtain ⟨hY, hX, h⟩ := h
  refine ⟨hY, ?_⟩
  have h_snd : (μ.map (fun ω => (X ω, Y ω))).snd = Q := by
    have h_map : μ.map (fun ω => (X ω, Y ω)) = (μ.map X) ⊗ₘ (Kernel.const _ Q) :=
      have h_map : μ.map (fun ω => (X ω, Y ω)) = (μ.map X) ⊗ₘ (condDistrib Y X μ) :=
      (compProd_map_condDistrib hY).symm
      h_map.trans (Measure.compProd_congr h)
    rw [h_map, MeasureTheory.Measure.snd_compProd]
    simp [MeasureTheory.Measure.map_apply_of_aemeasurable hX]
  rwa [Measure.snd_map_prodMk₀ hX] at h_snd

end ProbabilityTheory
