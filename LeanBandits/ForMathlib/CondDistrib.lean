/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.Lemmas
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

lemma trim_comap_apply (hX : Measurable X) {s : Set β} (hs : MeasurableSet s) :
    μ.trim hX.comap_le (X ⁻¹' s) = μ.map X s := by
  rw [trim_measurableSet_eq, Measure.map_apply (by fun_prop) hs]
  exact ⟨s, hs, rfl⟩

lemma ext_prod₃ {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ {s : Set α} {t : Set β} {u : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u), μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :
    μ = ν := by
  sorry

lemma ext_prod₃_iff {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
      μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :=
  ⟨fun h s t u hs ht hu ↦ by rw [h], Measure.ext_prod₃⟩

end MeasureTheory.Measure

namespace ProbabilityTheory

lemma Kernel.prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  rw [Kernel.prod_apply, Measure.prod_prod]

lemma CondIndepFun.prod_right
    {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {mδ : MeasurableSpace δ} [StandardBorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → γ} {Z : α → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : CondIndepFun (mδ.comap Z) hZ.comap_le X Y μ) :
    CondIndepFun (mδ.comap Z) hZ.comap_le X (fun ω ↦ (Y ω, Z ω)) μ := by
  sorry

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

-- todo: use this to refactor `indepFun_iff_map_prod_eq_prod_map_map`
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
      exact Measure.ext_prod₃ h
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

lemma Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map {Ω' α β γ : Type*}
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
    [StandardBorelSpace α] {X : α → β} {T : α → γ}
    {hm : m ≤ mα} {μ : Measure α} [IsFiniteMeasure μ]
    -- TODO: relax this to CountableOrCountablyGenerated once it is fixed
    [StandardBorelSpace β] [StandardBorelSpace γ]
    (hX : Measurable X) (hT : Measurable T) :
    CondIndepFun m hm X T μ
      ↔ (condExpKernel μ m).map (fun ω ↦ (X ω, T ω))
        =ᵐ[μ.trim hm] (((condExpKernel μ m).map X) ×ₖ ((condExpKernel μ m).map T)) :=
  Kernel.indepFun_iff_map_prod_eq_prod_map_map hX hT

lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
    {α : Type*} {m mα : MeasurableSpace α} [StandardBorelSpace α] {X : α → β} {T : α → γ}
    {hm : m ≤ mα} {μ : Measure α} [IsFiniteMeasure μ]
    -- TODO: relax this to CountableOrCountablyGenerated once it is fixed
    [StandardBorelSpace β] [StandardBorelSpace γ]
    (hX : Measurable X) (hT : Measurable T) :
    CondIndepFun m hm X T μ
      ↔ @Measure.map _ _ _ (m.prod _) (fun ω ↦ (ω, X ω, T ω)) μ
        = (Kernel.id ×ₖ ((condExpKernel μ m).map X ×ₖ (condExpKernel μ m).map T)) ∘ₘ μ.trim hm := by
  unfold CondIndepFun
  rw [Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hX hT]
  congr!
  · calc (μ.trim hm ⊗ₘ (condExpKernel μ m).map fun ω ↦ (X ω, T ω))
    _ = (Kernel.id ∥ₖ Kernel.deterministic (fun ω ↦ (X ω, T ω)) (by fun_prop))
        ∘ₘ (μ.trim hm ⊗ₘ (condExpKernel μ m)) := by
      rw [Measure.compProd_eq_parallelComp_comp_copy_comp, ← Kernel.deterministic_comp_eq_map,
        ← Kernel.parallelComp_id_left_comp_parallelComp, Measure.comp_assoc, Kernel.comp_assoc,
        Kernel.parallelComp_comp_copy, ← Measure.comp_assoc, Measure.compProd_eq_comp_prod]
    _ = (Kernel.id ∥ₖ Kernel.deterministic (fun ω ↦ (X ω, T ω)) (by fun_prop))
        ∘ₘ (@Measure.map _ _ mα (m.prod mα) (fun ω ↦ (ω, ω)) μ) := by
      congr
      exact compProd_trim_condExpKernel hm
    _ = _ := by
      rw [← Measure.deterministic_comp_eq_map, Measure.comp_assoc,
        ← Kernel.deterministic_prod_deterministic (g := fun ω ↦ ω),
        Kernel.parallelComp_comp_prod, Kernel.deterministic_comp_deterministic, Kernel.id_comp,
        Kernel.deterministic_prod_deterministic, Measure.deterministic_comp_eq_map]
      · rfl
      · exact Measurable.mono measurable_id le_rfl hm
      · fun_prop
  · rw [Measure.compProd_eq_comp_prod]

lemma condDistrib_apply_ae_eq_condExpKernel_map
    {α : Type*} {mα : MeasurableSpace α} [StandardBorelSpace α]
    [StandardBorelSpace β] [Nonempty β]
    {X : α → β} {T : α → γ} {μ : Measure α} [IsFiniteMeasure μ]
    (hX : Measurable X) (hT : Measurable T) {s : Set β} (hs : MeasurableSet s) :
    (fun a ↦ condDistrib X T μ (T a) s)
      =ᵐ[μ] fun a ↦ (condExpKernel μ (MeasurableSpace.comap T inferInstance)).map X a s := by
  have hT_meas {s : Set γ} (hs : MeasurableSet s) :
      MeasurableSet[MeasurableSpace.comap T inferInstance] (T ⁻¹' s) := by
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨s, hs, rfl⟩
  have h1 := condDistrib_ae_eq_condExp hT hX (μ := μ) hs
  simp_rw [Kernel.map_apply _ hX, Measure.map_apply hX hs]
  have h2 := condExpKernel_ae_eq_condExp hT.comap_le (μ := μ) (hX hs)
  filter_upwards [h1, h2] with a ha₁ ha₂
  rw [Measure.real] at ha₁ ha₂
  rw [← ENNReal.toReal_eq_toReal (by simp) (by simp), ha₁, ha₂]

omit [Nonempty Ω'] in
theorem condIndepFun_comap_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {α : Type*} {mα : MeasurableSpace α} [StandardBorelSpace α]
    {X : α → β} {T : α → γ} {Z : α → Ω'} {μ : Measure α} [IsFiniteMeasure μ]
    [StandardBorelSpace β] [StandardBorelSpace γ] [Nonempty β] [Nonempty γ]
    (hX : Measurable X) (hT : Measurable T) (hZ : Measurable Z) :
    CondIndepFun _ hZ.comap_le X T μ
      ↔ μ.map (fun ω ↦ (Z ω, X ω, T ω))
        = (Kernel.id ×ₖ (condDistrib X Z μ ×ₖ condDistrib T Z μ)) ∘ₘ μ.map Z := by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hX hT]
  simp_rw [Measure.ext_prod₃_iff]
  have hZ_meas {s : Set Ω'} (hs : MeasurableSet s) :
      MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' s) := by
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨s, hs, rfl⟩
  have h_left {s : Set Ω'} {t : Set β} {u : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      (μ.map (fun ω ↦ (Z ω, X ω, T ω))) (s ×ˢ t ×ˢ u)
        = (@Measure.map _ _ _ ((MeasurableSpace.comap Z inferInstance).prod inferInstance)
          (fun ω ↦ (ω, X ω, T ω)) μ) ((Z ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.map_apply (by fun_prop) (hs.prod (ht.prod hu)),
      Measure.map_apply _ ((hZ_meas hs).prod (ht.prod hu))]
    · simp [Set.mk_preimage_prod]
    · refine Measurable.prodMk ?_ (by fun_prop)
      exact Measurable.mono measurable_id le_rfl hZ.comap_le
  have h_right {s : Set Ω'} {t : Set β} {u : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (condDistrib X Z μ ×ₖ condDistrib T Z μ)) ∘ₘ μ.map Z) (s ×ˢ t ×ˢ u)
      = ((Kernel.id ×ₖ
        ((condExpKernel μ (MeasurableSpace.comap Z inferInstance)).map X ×ₖ
          (condExpKernel μ (MeasurableSpace.comap Z inferInstance)).map T)) ∘ₘ
        μ.trim hZ.comap_le) ((Z ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.bind_apply ((hZ_meas hs).prod (ht.prod hu)) (by fun_prop),
      Measure.bind_apply (hs.prod (ht.prod hu)) (by fun_prop), lintegral_map ?_ (by fun_prop),
      lintegral_trim]
    rotate_left
    · exact Kernel.measurable_coe _ ((hZ_meas hs).prod (ht.prod hu))
    · exact Kernel.measurable_coe _ (hs.prod (ht.prod hu))
    refine lintegral_congr_ae ?_
    filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hX hZ ht,
      condDistrib_apply_ae_eq_condExpKernel_map hT hZ hu] with a haX haT
    simp_rw [Kernel.prod_apply_prod]
    simp only [Kernel.id_apply, Measure.dirac_apply]
    rw [@Measure.dirac_apply' _ (MeasurableSpace.comap Z inferInstance) _ _ (hZ_meas hs)]
    congr
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro s t u hs ht hu
    specialize h (s := Z ⁻¹' s) (hZ_meas hs) ht hu
    convert h
    · exact h_left hs ht hu
    · exact h_right hs ht hu
  · rintro _ t u ⟨s, hs, rfl⟩ ht hu
    specialize h hs ht hu
    convert h
    · exact (h_left hs ht hu).symm
    · exact (h_right hs ht hu).symm

-- todo: should be an iff
lemma condDistrib_prod_of_condIndepFun [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ) :
    condDistrib Y (fun ω ↦ (X ω, Z ω)) μ
      =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] Kernel.prodMkLeft _ (condDistrib Y Z μ) := by
  symm
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) (hX.prodMk hZ).aemeasurable
    hY.aemeasurable _ ?_
  rw [condIndepFun_comap_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hY hX hZ] at h
  rw [Measure.compProd_eq_comp_prod]
  calc μ.map (fun x ↦ ((X x, Z x), Y x))
  _ = ((condDistrib X Z μ ×ₖ Kernel.id) ×ₖ condDistrib Y Z μ) ∘ₘ μ.map Z := by
    -- up to shuffling, this is the previous lemma
    sorry
  _ = (Kernel.id ×ₖ Kernel.prodMkLeft β (condDistrib Y Z μ)) ∘ₘ Kernel.swap _ _
      ∘ₘ (μ.map Z ⊗ₘ condDistrib X Z μ) := by
    rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc, Measure.comp_assoc]
    congr
    rw [Kernel.comp_assoc, Kernel.swap_prod]
    ext ω : 1
    simp_rw [Kernel.prod_apply]
    rw [Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply, ← Measure.compProd_eq_comp_prod]
    ext s hs
    rw [Measure.compProd_apply hs, Measure.prod_apply hs]
    simp only [Kernel.prodMkLeft_apply]
    rw [lintegral_prod, lintegral_prod]
    · simp_rw [lintegral_dirac]
    · refine Measurable.aemeasurable ?_
      have : Measurable fun a ↦ (Kernel.prodMkLeft _ (condDistrib Y Z μ) a) (Prod.mk a ⁻¹' s) :=
        Kernel.measurable_kernel_prodMk_left hs
      exact this
    · refine Measurable.aemeasurable ?_
      have : Measurable fun x ↦ (Kernel.const _ ((condDistrib Y Z μ) ω) x) (Prod.mk x ⁻¹' s) :=
        Kernel.measurable_kernel_prodMk_left hs
      exact this
  _ = (Kernel.id ×ₖ Kernel.prodMkLeft β (condDistrib Y Z μ)) ∘ₘ μ.map (fun a ↦ (X a, Z a)) := by
    congr
    rw [compProd_map_condDistrib hX.aemeasurable, Measure.swap_comp,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

lemma condDistrib_fst_prod (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) hX hY _ ?_
  have hX_map : (μ.prod ν).map (fun ω ↦ X ω.1) = μ.map X := by
    calc (μ.prod ν).map (fun ω ↦ X ω.1)
    _ = ((μ.prod ν).map Prod.fst).map X := by
      rw [AEMeasurable.map_map_of_aemeasurable ?_ (by fun_prop)]
      · rfl
      · rw [Measure.map_fst_prod]
        exact hX.smul_measure _
    _ = μ.map X := by simp [Measure.map_fst_prod]
  rw [← hX_map, compProd_map_condDistrib]
  · calc μ.map (fun x ↦ (X x, Y x))
    _ = ((μ.prod ν).map Prod.fst).map (fun a ↦ (X a, Y a)) := by simp [Measure.map_fst_prod]
    _ = (μ.prod ν).map (fun a ↦ (X a.1, Y a.1)) := by
      rw [AEMeasurable.map_map_of_aemeasurable ?_ (by fun_prop)]
      · rfl
      · simp only [Measure.map_fst_prod, measure_univ, one_smul]
        fun_prop
  · fun_prop

end CondDistrib

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

lemma cond_of_condIndepFun [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β] [Countable β]
    [Countable Ω']
    [IsZeroOrProbabilityMeasure μ]
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ)
    (hX : Measurable X) (hY : Measurable Y) {b : β} {ω : Ω'}
    (hμ : μ (X ⁻¹' {b} ∩ Z ⁻¹' {ω}) ≠ 0) :
    (μ[|X ⁻¹' {b} ∩ Z ⁻¹' {ω}]).map Y = (μ[|Z ⁻¹' {ω}]).map Y := by
  have h := condDistrib_prod_of_condIndepFun hX hY hZ h
  have h_left := condDistrib_ae_eq_cond (hX.prodMk hZ) hY (μ := μ)
  have h_right := condDistrib_ae_eq_cond hZ hY (μ := μ)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h h_left h_right
  specialize h (b, ω)
  specialize h_left (b, ω)
  specialize h_right ω
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h h_left h_right
  rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod] at h h_left
  have hZ_ne : μ (Z ⁻¹' {ω}) ≠ 0 := fun h ↦ hμ (measure_mono_null Set.inter_subset_right h)
  rw [← h_right hZ_ne, ← h_left hμ, h hμ]
  simp

end Cond

end ProbabilityTheory
