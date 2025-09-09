/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.CompProdEqIff
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

section CondDistrib

variable [IsFiniteMeasure μ]

lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hY, Measure.snd_map_prodMk₀ hX]

lemma condDistrib_congr {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y' X' μ := by
  rw [condDistrib, condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

lemma condDistrib_congr_right {X' : α → β} (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y X' μ :=
  condDistrib_congr (by rfl) hX

lemma condDistrib_congr_left {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') :
    condDistrib Y X μ = condDistrib Y' X μ :=
  condDistrib_congr hY (by rfl)

lemma condDistrib_ae_eq_of_measure_eq_compProd₀
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

lemma condDistrib_comp (hX : AEMeasurable X μ) {f : β → Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ hX (by fun_prop) _ ?_
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  rfl

lemma condDistrib_const (hX : AEMeasurable X μ) (c : Ω) :
    condDistrib (fun _ ↦ c) X μ =ᵐ[μ.map X] Kernel.deterministic (fun _ ↦ c) (by fun_prop) := by
  have : (fun _ : α ↦ c) = (fun _ : β ↦ c) ∘ X := rfl
  conv_lhs => rw [this]
  filter_upwards [condDistrib_comp hX (by fun_prop : Measurable (fun _ ↦ c))] with b hb
  rw [hb]

lemma condDistrib_of_indepFun (h : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) hX hY _ ?_
  simp only [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h

lemma indepFun_iff_condDistrib_eq_const (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine ⟨fun h ↦ condDistrib_of_indepFun h hX hY, fun h ↦ ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← compProd_map_condDistrib hY,
    Measure.compProd_congr h]
  simp

lemma Kernel.prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  rw [Kernel.prod_apply, Measure.prod_prod]

theorem Kernel.indepFun_iff_map_prod_eq_prod_map_map {Ω' α β γ : Type*}
    {mΩ' : MeasurableSpace Ω'} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {X : α → β} {T : α → γ}
    {μ : Measure Ω'} [IsFiniteMeasure μ]
    {κ : Kernel Ω' α} [IsFiniteKernel κ]
    -- TODO: relax this to CountableOrCountablyGenerated once it is fixed
    [StandardBorelSpace β] [StandardBorelSpace γ]
    (hf : Measurable X) (hg : Measurable T) :
    IndepFun X T κ μ ↔ κ.map (fun ω ↦ (X ω, T ω)) =ᵐ[μ] ((κ.map X) ×ₖ (κ.map T)) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Kernel.compProd_eq_iff]
    have : (μ ⊗ₘ κ.map fun ω ↦ (X ω, T ω)) = μ ⊗ₘ (κ.map X ×ₖ κ.map T)
        ↔ ∀ {u : Set Ω'} {s : Set β} {t : Set γ},
        MeasurableSet u → MeasurableSet s → MeasurableSet t →
        (μ ⊗ₘ κ.map (fun ω ↦ (X ω, T ω))) (u ×ˢ s ×ˢ t)
          = (μ ⊗ₘ (κ.map X ×ₖ κ.map T)) (u ×ˢ s ×ˢ t) := by
      refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
      sorry
    rw [this]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht)),
      Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω ∈ u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω ∈ u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [Kernel.map_apply _ (by fun_prop), Measure.map_apply (by fun_prop) (hs.prod ht)]
    rw [Set.mk_preimage_prod, hω, Kernel.prod_apply_prod, Kernel.map_apply' _ (by fun_prop),
        Kernel.map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    filter_upwards [h] with ω hω
    calc (κ ω) (X ⁻¹' s ∩ T ⁻¹' t)
    _ = (κ.map (fun ω ↦ (X ω, T ω))) ω (s ×ˢ t) := by
      rw [← Kernel.deterministic_comp_eq_map, ← deterministic_prod_deterministic hf hg,
        Kernel.comp_apply, Measure.bind_apply (hs.prod ht) (by fun_prop)]
      simp_rw [Kernel.prod_apply_prod, Kernel.deterministic_apply' hf _ hs,
        Kernel.deterministic_apply' hg _ ht]
      calc (κ ω) (X ⁻¹' s ∩ T ⁻¹' t)
      _ = ∫⁻ a, (X ⁻¹' s ∩ T ⁻¹' t).indicator (fun x ↦ 1) a ∂κ ω := by
        simp [lintegral_indicator ((hf hs).inter (hg ht))]
      _ = ∫⁻ a, (X ⁻¹' s).indicator (fun x ↦ 1) a * (T ⁻¹' t).indicator (fun x ↦ 1) a ∂κ ω := by
        congr with a
        simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, mul_ite, mul_one,
          mul_zero]
        by_cases has : X a ∈ s <;> simp [has]
      _ = ∫⁻ a, s.indicator (fun x ↦ 1) (X a) * t.indicator (fun x ↦ 1) (T a) ∂κ ω := rfl
    _ = ((κ.map X) ×ₖ (κ.map T)) ω (s ×ˢ t) := by rw [hω]
    _ = (κ ω) (X ⁻¹' s) * (κ ω) (T ⁻¹' t) := by
      rw [Kernel.prod_apply_prod, Kernel.map_apply' _ (by fun_prop),
        Kernel.map_apply' _ (by fun_prop)]
      exacts [ht, hs]

theorem Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map{Ω' α β γ : Type*}
    {mΩ' : MeasurableSpace Ω'} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {X : α → β} {T : α → γ}
    {μ : Measure Ω'} [IsFiniteMeasure μ]
    {κ : Kernel Ω' α} [IsFiniteKernel κ]
    -- TODO: relax this to CountableOrCountablyGenerated once it is fixed
    [StandardBorelSpace β] [StandardBorelSpace γ]
    (hf : Measurable X) (hg : Measurable T) :
    IndepFun X T κ μ ↔ (μ ⊗ₘ κ.map fun ω ↦ (X ω, T ω)) = μ ⊗ₘ (κ.map X ×ₖ κ.map T) := by
  rw [Kernel.indepFun_iff_map_prod_eq_prod_map_map hf hg, Kernel.compProd_eq_iff]

theorem condIndepFun_iff_map_prod_eq_prod_map_map {α : Type*} {m mα : MeasurableSpace α}
    [StandardBorelSpace α]
    {X : α → β} {T : α → γ}
    {hm : m ≤ mα} {μ : Measure α} [IsFiniteMeasure μ]
    -- TODO: relax this to CountableOrCountablyGenerated once it is fixed
    [StandardBorelSpace β] [StandardBorelSpace γ]
    (hX : Measurable X) (hT : Measurable T) :
    CondIndepFun m hm X T μ
     ↔ (condExpKernel μ m).map (fun ω ↦ (X ω, T ω))
       =ᵐ[μ.trim hm] (((condExpKernel μ m).map X) ×ₖ ((condExpKernel μ m).map T)) :=
  Kernel.indepFun_iff_map_prod_eq_prod_map_map hX hT

lemma condDistrib_of_condIndepFun [StandardBorelSpace α]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ) :
    condDistrib Y (fun ω ↦ (X ω, Z ω)) μ
      =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] Kernel.prodMkLeft _ (condDistrib Y Z μ) := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) (hX.prodMk hZ).aemeasurable
    hY.aemeasurable _ ?_
  sorry

end CondDistrib

lemma condIndep_iff_condExpKernel_eq {α : Type*} {F G H mα : MeasurableSpace α}
    [StandardBorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hG : G ≤ mα) :
    CondIndep G F H hG μ
      ↔ condExpKernel μ (F ⊔ G) =ᵐ[@Measure.map  _ _ mα H id μ] condExpKernel μ G := by
  sorry

section Cond

lemma ae_cond_of_forall_mem {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ[|s], p x := Measure.ae_smul_measure (ae_restrict_of_forall_mem hs h) _

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

end Cond

end ProbabilityTheory
