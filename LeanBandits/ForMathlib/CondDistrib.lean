/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.Lemmas
import LeanBandits.ForMathlib.KernelCompositionParallelComp
import LeanBandits.ForMathlib.KernelSub

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {α β γ δ Ω Ω' : Type*}
  {m mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
  {X : α → β} {Y : α → Ω} {Z : α → Ω'} {T : α → γ}

lemma MeasurableSpace.comap_prodMk (X : α → β) (Y : α → γ) :
    MeasurableSpace.comap (fun ω ↦ (X ω, Y ω)) inferInstance = mβ.comap X ⊔ mγ.comap Y := by
  rw [← generateFrom_prod, MeasurableSpace.comap_generateFrom,
    MeasurableSpace.comap_eq_generateFrom, MeasurableSpace.comap_eq_generateFrom,
    MeasurableSpace.generateFrom_sup_generateFrom]
  have : (Set.preimage fun ω ↦ (X ω, Y ω)) ''
        Set.image2 (fun x1 x2 ↦ x1 ×ˢ x2) {s | MeasurableSet s} {t | MeasurableSet t}
      = {x | ∃ a, MeasurableSet a ∧ ∃ b, MeasurableSet b ∧ X ⁻¹' a ∩ Y ⁻¹' b = x} := by
    ext
    simp [Set.mk_preimage_prod]
  rw [this]
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSpace.measurableSet_generateFrom <| .inl ⟨a, ha, rfl⟩
    · exact MeasurableSpace.measurableSet_generateFrom <| .inr ⟨b, hb, rfl⟩
  · refine fun t ht ↦ MeasurableSpace.measurableSet_generateFrom ?_
    cases ht with
    | inl h =>
      obtain ⟨s, hs, rfl⟩ := h
      exact ⟨s, hs, .univ, .univ, by simp⟩
    | inr h =>
      obtain ⟨t, ht, rfl⟩ := h
      exact ⟨.univ, .univ, t, ht, by simp⟩

lemma map_trim_comap {f : α → β} (hf : Measurable f) :
    @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply _ hs, trim_measurableSet_eq]
  · exact ⟨s, hs, rfl⟩
  · exact Measurable.of_comap_le le_rfl

lemma ae_map_iff_ae_trim {f : α → β} (hf : Measurable f) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) :
    (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂(μ.trim hf.comap_le), p (f x) := by
  rw [← map_trim_comap hf, ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]

@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

@[fun_prop]
lemma Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf

namespace MeasureTheory.Measure

lemma trim_eq_map {hm : m ≤ mα} : μ.trim hm = @Measure.map _ _ mα m id μ := by
  refine @Measure.ext _ m _ _ fun s hs ↦ ?_
  rw [trim_measurableSet_eq _ hs, Measure.map_apply _ hs]
  · simp
  · intro t ht
    simp only [Set.preimage_id_eq, id_eq]
    exact hm _ ht

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

lemma ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ {s : Set α} {t : Set β} (_ : MeasurableSet s) (_ : MeasurableSet t),
      μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  ext s hs
  have h_univ : μ .univ = ν .univ := by
    rw [← Set.univ_prod_univ]
    exact h .univ .univ
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · intro t ht
    simp only [Set.mem_image2, Set.mem_setOf_eq] at ht
    obtain ⟨s, hs, t, ht, rfl⟩ := ht
    exact h hs ht
  · intro t ht
    simp_rw [measure_compl ht (measure_ne_top _ _)]
    intro h
    rw [h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

lemma ext_prod_iff {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔ ∀ {s : Set α} {t : Set β} (_ : MeasurableSet s) (_ : MeasurableSet t),
      μ (s ×ˢ t) = ν (s ×ˢ t) :=
  ⟨fun h s t hs ht ↦ by rw [h], Measure.ext_prod⟩

lemma ext_prod₃ {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ {s : Set α} {t : Set β} {u : Set γ} (_ : MeasurableSet s) (_ : MeasurableSet t)
      (_ : MeasurableSet u), μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :
    μ = ν := by
  ext s hs
  have h_univ : μ .univ = ν .univ := by
    simp_rw [← Set.univ_prod_univ]
    exact h .univ .univ .univ
  let C₂ := Set.image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := Set.image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } C₂
  refine MeasurableSpace.induction_on_inter (s := C) ?_ ?_ (by simp) ?_ ?_ ?_ s hs
  · refine (generateFrom_eq_prod (C := { s : Set α | MeasurableSet s }) (D := C₂) (by simp)
      generateFrom_prod isCountablySpanning_measurableSet ?_).symm
    exact isCountablySpanning_measurableSet.prod isCountablySpanning_measurableSet
  · exact MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_prod
  · intro t ht
    simp only [Set.mem_image2, Set.mem_setOf_eq, exists_exists_and_exists_and_eq_and, C, C₂] at ht
    obtain ⟨s, hs, t, ht, u, hu, rfl⟩ := ht
    exact h hs ht hu
  · intro t ht
    simp_rw [measure_compl ht (measure_ne_top _ _)]
    intro h
    rw [h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

lemma ext_prod₃_iff {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
      μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :=
  ⟨fun h s t u hs ht hu ↦ by rw [h], Measure.ext_prod₃⟩

lemma ext_prod₃_iff' {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure ((α × β) × γ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
      μ ((s ×ˢ t) ×ˢ u) = ν ((s ×ˢ t) ×ˢ u)) := by
  have : μ = ν ↔ μ.map MeasurableEquiv.prodAssoc = ν.map MeasurableEquiv.prodAssoc := by
    refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
    have h_map_map (μ : Measure ((α × β) × γ)) :
        μ = (μ.map MeasurableEquiv.prodAssoc).map MeasurableEquiv.prodAssoc.symm := by
      simp
    rw [h_map_map μ, h_map_map ν, h]
  rw [this, ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      ν.map MeasurableEquiv.prodAssoc (s ×ˢ (t ×ˢ u)) = ν ((s ×ˢ t) ×ˢ u) := by
    rw [map_apply (by fun_prop) (hs.prod (ht.prod hu))]
    congr 1
    ext x
    simp [MeasurableEquiv.prodAssoc]
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h s t u hs ht hu ↦ ?_⟩
    <;> specialize h hs ht hu
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu] at h
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu]

alias ⟨_, ext_prod₃'⟩ := ext_prod₃_iff'

end MeasureTheory.Measure

namespace ProbabilityTheory

lemma Kernel.prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  rw [Kernel.prod_apply, Measure.prod_prod]

lemma Kernel.compProd_assoc {κ : Kernel α β} {η : Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ξ] :
    (κ ⊗ₖ η) ⊗ₖ ξ
      = (κ ⊗ₖ (η ⊗ₖ (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map
        MeasurableEquiv.prodAssoc.symm := by
  ext a s hs
  rw [compProd_apply hs, map_apply' _ (by fun_prop) _ hs,
    compProd_apply (hs.preimage (by fun_prop)), lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  swap; · exact hs.preimage (by fun_prop)
  congr

lemma _root_.MeasureTheory.Measure.compProd_assoc
    {μ : Measure α} {κ : Kernel α β} {η : Kernel (α × β) γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ κ) ⊗ₘ η = (μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.lintegral_compProd]
  swap; · exact Kernel.measurable_kernel_prodMk_left hs
  congr with a
  rw [Kernel.compProd_apply]
  swap; · exact hs.preimage (by fun_prop)
  congr

lemma _root_.MeasureTheory.Measure.compProd_assoc'
    {μ : Measure α} {κ : Kernel α β} {η : Kernel (α × β) γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ (κ ⊗ₖ η) = ((μ ⊗ₘ κ) ⊗ₘ η).map MeasurableEquiv.prodAssoc := by
  simp [Measure.compProd_assoc]

section IndepFun

-- fix the lemma in mathlib to allow different types for the functions
theorem CondIndepFun.symm'
    [StandardBorelSpace α] {hm : m ≤ mα} [IsFiniteMeasure μ] {f : α → β} {g : α → γ}
    (hfg : CondIndepFun m hm f g μ) :
    CondIndepFun m hm g f μ :=
  Kernel.IndepFun.symm hfg

lemma Kernel.indepFun_const_left {κ : Kernel α β} [IsZeroOrMarkovKernel κ] (c : δ) (X : β → γ) :
    IndepFun (fun _ ↦ c) X κ μ := by
  rw [IndepFun, MeasurableSpace.comap_const]
  exact indep_bot_left _

lemma Kernel.indepFun_const_right {κ : Kernel α β} [IsZeroOrMarkovKernel κ] (X : β → γ) (c : δ) :
    IndepFun X (fun _ ↦ c) κ μ :=
  (Kernel.indepFun_const_left c X).symm

lemma condIndepFun_const_left [StandardBorelSpace α] {hm : m ≤ mα} [IsFiniteMeasure μ]
    (c : γ) (X : α → β) :
    CondIndepFun m hm (fun _ ↦ c) X μ :=
  Kernel.indepFun_const_left c X

lemma condIndepFun_const_right [StandardBorelSpace α] {hm : m ≤ mα}
    [IsFiniteMeasure μ] (X : α → β) (c : γ) :
    CondIndepFun m hm X (fun _ ↦ c) μ :=
  Kernel.indepFun_const_right X c

lemma condIndepFun_of_measurable_left [StandardBorelSpace α] {hm : m ≤ mα} [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} (hX : Measurable[m] X) (hY : Measurable Y) :
    CondIndepFun m hm X Y μ := by
  rw [condIndepFun_iff _ hm _ _ (hX.mono hm le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have h_ind_eq ω : (X ⁻¹' s ∩ Y ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) ω
      = (X ⁻¹' s).indicator (fun _ ↦ (1 : ℝ)) ω * (Y ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) ω := by
    simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, mul_ite, mul_one, mul_zero]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · exfalso
      rw [Set.mem_inter_iff] at h1
      refine h3 h1.1
    · exfalso
      rw [Set.mem_inter_iff] at h1
      exact h2 h1.2
    · exfalso
      rw [Set.mem_inter_iff] at h1
      exact h1 ⟨h5, h4⟩
    · rfl
    · rfl
  calc μ[(X ⁻¹' s ∩ Y ⁻¹' t).indicator fun ω ↦ (1 : ℝ)|m]
  _ = μ[fun ω ↦ (X ⁻¹' s).indicator (fun _ ↦ 1) ω * (Y ⁻¹' t).indicator (fun _ ↦ 1) ω|m] := by
      simp_rw [← h_ind_eq]
  _ =ᵐ[μ] fun ω ↦ (X ⁻¹' s).indicator (fun _ ↦ 1) ω * μ[(Y ⁻¹' t).indicator (fun _ ↦ 1)|m] ω := by
    refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
    · exact (Measurable.indicator (by fun_prop) (hX hs)).stronglyMeasurable
    · have : ((X ⁻¹' s).indicator fun x ↦ (1 : ℝ)) * (Y ⁻¹' t).indicator (fun x ↦ 1)
          = (X ⁻¹' s ∩ Y ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) := by ext; simp [h_ind_eq]
      rw [this]
      rw [integrable_indicator_iff]
      · exact (integrable_const (1 : ℝ)).integrableOn
      · exact (hm _ (hX hs)).inter (hY ht)
    · rw [integrable_indicator_iff]
      · exact (integrable_const (1 : ℝ)).integrableOn
      · exact hY ht
  _ =ᵐ[μ] μ[(X ⁻¹' s).indicator fun ω ↦ 1|m] * μ[(Y ⁻¹' t).indicator fun ω ↦ 1|m] := by
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · rfl
    · exact (Measurable.indicator (by fun_prop) (hX hs)).stronglyMeasurable
    · rw [integrable_indicator_iff]
      · exact (integrable_const (1 : ℝ)).integrableOn
      · exact hm _ (hX hs)

lemma condIndepFun_of_measurable_right [StandardBorelSpace α] {hm : m ≤ mα} [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} (hX : Measurable X) (hY : Measurable[m] Y) :
    CondIndepFun m hm X Y μ := by
  refine CondIndepFun.symm' ?_
  exact condIndepFun_of_measurable_left hY hX

@[inherit_doc CondIndepFun]
notation3 X " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y =>
  CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ) X Y μ

lemma condIndepFun_self_left [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Z : α → δ} (hX : Measurable X) (hZ : Measurable Z) :
    Z ⟂ᵢ[Z, hZ; μ] X := by -- CondIndepFun (mδ.comap Z) hZ.comap_le Z X μ := by
  refine condIndepFun_of_measurable_left ?_ hX
  rw [measurable_iff_comap_le]

lemma condIndepFun_self_right [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Z : α → δ} (hX : Measurable X) (hZ : Measurable Z) :
    X ⟂ᵢ[Z, hZ; μ] Z := by -- CondIndepFun (mδ.comap Z) hZ.comap_le X Z μ := by
  refine condIndepFun_of_measurable_right hX ?_
  rw [measurable_iff_comap_le]

lemma Kernel.IndepFun.of_prod_right {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun X (fun ω ↦ (Y ω, T ω)) κ μ) :
    IndepFun X Y κ μ := by
  rw [Kernel.indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  specialize h s (t ×ˢ .univ) hs (ht.prod .univ)
  simpa [Set.mk_preimage_prod] using h

lemma Kernel.IndepFun.of_prod_left {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun (fun ω ↦ (X ω, T ω)) Y κ μ) :
    IndepFun X Y κ μ := h.symm.of_prod_right.symm

lemma CondIndepFun.of_prod_right {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, T ω))) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_right h

lemma CondIndepFun.of_prod_left {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : (fun ω ↦ (X ω, T ω)) ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_left h

lemma CondIndepFun.prod_right [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] Y) :-- CondIndepFun (mδ.comap Z) hZ.comap_le X Y μ) :
    X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, Z ω)) := by
    -- CondIndepFun (mδ.comap Z) hZ.comap_le X (fun ω ↦ (Y ω, Z ω)) μ := by
  sorry

end IndepFun

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
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  suffices ∀ᵐ x ∂μ.map (hX.mk X), κ x = condDistrib (hY.mk Y) (hX.mk X) μ x by
    symm
    rw [Measure.map_congr hX.ae_eq_mk]
    convert this using 3 with b
    rw [condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) hX.measurable_mk hY.measurable_mk κ
    ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

lemma condDistrib_ae_eq_iff_measure_eq_compProd₀
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] :
  (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ := by
  refine ⟨fun h ↦ ?_, condDistrib_ae_eq_of_measure_eq_compProd₀ hX hY κ⟩
  rw [Measure.compProd_congr h.symm, compProd_map_condDistrib hY]

lemma condDistrib_comp' (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {f : Ω → Ω'} (hf : Measurable f) :
    condDistrib (f ∘ Y) X μ =ᵐ[μ.map X] (condDistrib Y X μ).map f := by
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ hX (by fun_prop) _ ?_
  calc μ.map (fun x ↦ (X x, (f ∘ Y) x))
  _ = (μ.map (fun x ↦ (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    rfl
  _ = (μ.map X ⊗ₘ condDistrib Y X μ).map (Prod.map id f) := by
    rw [compProd_map_condDistrib hY]
  _ = μ.map X ⊗ₘ (condDistrib Y X μ).map f := by
    rw [Measure.compProd_eq_comp_prod, ← Measure.deterministic_comp_eq_map (by fun_prop),
      Measure.compProd_eq_comp_prod, Measure.comp_assoc]
    congr
    rw [← Kernel.deterministic_comp_eq_map hf, ← Kernel.parallelComp_comp_copy,
      ← Kernel.parallelComp_comp_copy, ← Kernel.parallelComp_id_left_comp_parallelComp,
      ← Kernel.deterministic_parallelComp_deterministic (by fun_prop), Kernel.comp_assoc,
      ← Kernel.id]

lemma condDistrib_comp (hX : AEMeasurable X μ) {f : β → Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ hX (by fun_prop) _ ?_
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  rfl

lemma condDistrib_const (hX : AEMeasurable X μ) (c : Ω) :
    condDistrib (fun _ ↦ c) X μ =ᵐ[μ.map X] Kernel.deterministic (fun _ ↦ c) (by fun_prop) := by
  have : (fun _ : α ↦ c) = (fun _ : β ↦ c) ∘ X := rfl
  conv_lhs => rw [this]
  filter_upwards [condDistrib_comp hX (by fun_prop : Measurable (fun _ ↦ c))] with b hb
  rw [hb]

lemma condDistrib_fst_prod (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ := by
  symm
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

lemma condDistrib_prod_left [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) T μ
      =ᵐ[μ.map T] condDistrib X T μ ⊗ₖ condDistrib Y (fun ω ↦ (T ω, X ω)) μ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd₀ (μ := μ) hT (by fun_prop)
    (condDistrib X T μ ⊗ₖ condDistrib Y (fun ω ↦ (T ω, X ω)) μ) ?_
  rw [Measure.compProd_assoc', compProd_map_condDistrib hX, compProd_map_condDistrib hY,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma fst_condDistrib_prod [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    (condDistrib (fun ω ↦ (X ω, Y ω)) T μ).fst =ᵐ[μ.map T] condDistrib X T μ := by
  filter_upwards [condDistrib_prod_left hX hY hT] with c hc
  rw [Kernel.fst_apply, hc, ← Kernel.fst_apply, Kernel.fst_compProd]

lemma condDistrib_of_indepFun (h : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
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
    IndepFun X T κ μ ↔ κ.map (fun ω ↦ (X ω, T ω)) =ᵐ[μ] κ.map X ×ₖ κ.map T := by
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
    (X ⟂ᵢ[Z, hZ; μ] T) -- CondIndepFun _ hZ.comap_le X T μ
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

omit [Nonempty Ω'] in
lemma condIndepFun_iff_condDistrib_prod_ae_eq_prodMkLeft
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    (Y ⟂ᵢ[Z, hZ; μ] X)-- CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ
      ↔ condDistrib Y (fun ω ↦ (X ω, Z ω)) μ
          =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] Kernel.prodMkLeft _ (condDistrib Y Z μ) := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd₀ (μ := μ) (hX.prodMk hZ).aemeasurable
    hY.aemeasurable, condIndepFun_comap_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hY hX hZ,
    Measure.compProd_eq_comp_prod]
  let e : Ω' × Ω × β ≃ᵐ (β × Ω') × Ω := {
    toFun := fun p ↦ ((p.2.2, p.1), p.2.1)
    invFun := fun p ↦ (p.1.2, p.2, p.1.1)
    left_inv p := by simp
    right_inv p := by simp
    measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
    measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop }
  have h_eq : ((condDistrib X Z μ ×ₖ Kernel.id) ×ₖ condDistrib Y Z μ) ∘ₘ μ.map Z
      = (Kernel.id ×ₖ Kernel.prodMkLeft β (condDistrib Y Z μ)) ∘ₘ μ.map (fun a ↦ (X a, Z a)) := by
    calc ((condDistrib X Z μ ×ₖ Kernel.id) ×ₖ condDistrib Y Z μ) ∘ₘ μ.map Z
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
  rw [← h_eq]
  have h1 : μ.map (fun x ↦ ((X x, Z x), Y x)) = (μ.map (fun a ↦ (Z a , Y a, X a))).map e := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr
  have h1_symm : μ.map (fun a ↦ (Z a , Y a, X a))
      = (μ.map (fun x ↦ ((X x, Z x), Y x))).map e.symm := by
    rw [h1, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  have h2 : (condDistrib X Z μ ×ₖ Kernel.id ×ₖ condDistrib Y Z μ) ∘ₘ μ.map Z
      = ((Kernel.id ×ₖ (condDistrib Y Z μ ×ₖ condDistrib X Z μ)) ∘ₘ μ.map Z).map e := by
    rw [← Measure.deterministic_comp_eq_map e.measurable, Measure.comp_assoc]
    congr
    ext ω : 1
    rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.comp_apply,
      Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Measure.deterministic_comp_eq_map]
    rw [Measure.ext_prod₃_iff']
    intro s t u hs ht hu
    rw [Measure.prod_prod, Measure.prod_prod,
      Measure.map_apply (by fun_prop) ((hs.prod ht).prod hu)]
    have : e ⁻¹' ((s ×ˢ t) ×ˢ u) = t ×ˢ u ×ˢ s := by
      ext x
      simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_prod, e]
      tauto
    rw [this]
    simp_rw [Measure.prod_prod]
    ring
  have h2_symm : (Kernel.id ×ₖ (condDistrib Y Z μ ×ₖ condDistrib X Z μ)) ∘ₘ μ.map Z
      = ((condDistrib X Z μ ×ₖ Kernel.id ×ₖ condDistrib Y Z μ) ∘ₘ μ.map Z).map e.symm := by
    rw [h2, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  rw [h1, h2]
  exact ⟨fun h ↦ by rw [h], fun h ↦ by rw [h1_symm, h1, h2_symm, h2, h]⟩

lemma Measure.snd_compProd_prodMkLeft {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkLeft α)).snd = κ ∘ₘ μ.snd := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.bind_apply hs (by fun_prop), Measure.snd,
    lintegral_map (κ.measurable_coe hs) (by fun_prop)]
  simp only [Kernel.prodMkLeft_apply]
  congr

lemma Measure.snd_prodAssoc_compProd_prodMkLeft {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    (((μ ⊗ₘ (κ.prodMkLeft α))).map MeasurableEquiv.prodAssoc).snd = μ.snd ⊗ₘ κ := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop)),
    Measure.compProd_apply, Measure.compProd_apply hs, Measure.snd, lintegral_map _ (by fun_prop)]
  · simp only [Kernel.prodMkLeft_apply]
    congr
  · exact Kernel.measurable_kernel_prodMk_left hs
  · exact hs.preimage (by fun_prop)

lemma ProbabilityMeasure.ext_iff_coe {α : Type*} {mα : MeasurableSpace α}
    {μ ν : ProbabilityMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

lemma FiniteMeasure.ext_iff_coe {α : Type*} {mα : MeasurableSpace α} {μ ν : FiniteMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

instance : PartialOrder (FiniteMeasure α) :=
  PartialOrder.lift _ FiniteMeasure.toMeasure_injective

lemma FiniteMeasure.le_iff_coe {μ ν : FiniteMeasure α} :
    μ ≤ ν ↔ (μ : Measure α) ≤ (ν : Measure α) := Iff.rfl

noncomputable
instance : Sub (FiniteMeasure α) :=
  ⟨fun μ ν ↦ ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩⟩

lemma FiniteMeasure.sub_def (μ ν : FiniteMeasure α) :
    μ - ν = ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩ :=
  rfl

@[simp, norm_cast]
theorem FiniteMeasure.toMeasure_sub (μ ν : FiniteMeasure α) : ↑(μ - ν) = (↑μ - ↑ν : Measure α) :=
  rfl

instance : CanonicallyOrderedAdd (FiniteMeasure α) where
  exists_add_of_le {μ ν} hμν := by
    refine ⟨ν - μ, ?_⟩
    rw [FiniteMeasure.ext_iff_coe]
    simp only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_sub]
    rw [add_comm, Measure.sub_add_cancel_of_le hμν]
  le_self_add μ ν := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_add]
    exact Measure.le_add_right le_rfl

instance : OrderedSub (FiniteMeasure α) where
  tsub_le_iff_right μ ν ξ := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_sub, FiniteMeasure.toMeasure_add]
    exact Measure.sub_le_iff_add

lemma Kernel.prodMkLeft_ae_eq_iff [MeasurableSpace.CountableOrCountablyGenerated α β]
    {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure (γ × α)} :
    κ.prodMkLeft γ =ᵐ[μ] η.prodMkLeft γ ↔ κ =ᵐ[μ.snd] η := by
  rw [Measure.snd, Filter.EventuallyEq, Filter.EventuallyEq, ae_map_iff (by fun_prop)]
  · simp
  · classical
    exact Kernel.measurableSet_eq κ η

omit [Nonempty Ω'] in
lemma condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) {η : Kernel Ω' Ω}
    [IsMarkovKernel η]
    (h : condDistrib Y (fun ω ↦ (X ω, Z ω)) μ =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] η.prodMkLeft _) :
    Y ⟂ᵢ[Z, hZ; μ] X := by
  have hη_eq : condDistrib Y Z μ =ᵐ[μ.map Z] η := by
    rw [condDistrib_ae_eq_iff_measure_eq_compProd₀ (by fun_prop) (by fun_prop)] at h ⊢
    have h_snd : μ.map Z = (μ.map (fun ω ↦ (X ω, Z ω))).snd := by
      rw [Measure.snd_map_prodMk hX]
    rw [h_snd, ← Measure.snd_prodAssoc_compProd_prodMkLeft, ← h,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.snd_map_prodMk (by fun_prop)]
    congr
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkLeft hX hY hZ]
  refine h.trans ?_
  rw [Kernel.prodMkLeft_ae_eq_iff, Measure.snd_map_prodMk (by fun_prop)]
  exact hη_eq.symm

/-- Law of `Y` conditioned on `X`. -/
notation "𝓛[" Y " | " X "; " μ "]" => condDistrib Y X μ

-- generalize to map instead of fst
omit [Nonempty Ω'] in
lemma condIndepFun_fst_prod [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (ν : Measure γ) [IsProbabilityMeasure ν]
    (h_indep : CondIndepFun (mΩ'.comap Z) hZ.comap_le Y X μ) :
    CondIndepFun (mΩ'.comap (fun ω ↦ Z ω.1)) (hZ.comp measurable_fst).comap_le
      (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) := by
  rw [condIndepFun_comap_iff_map_prod_eq_prod_condDistrib_prod_condDistrib (by fun_prop)
    (by fun_prop) (by fun_prop)] at h_indep ⊢
  have h1 : 𝓛[fun ω ↦ Y ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[Y | Z; μ] :=
    condDistrib_fst_prod (Y := Y) (X := Z) (ν := ν) (μ := μ) (by fun_prop) (by fun_prop)
  have h2 : 𝓛[fun ω ↦ X ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[X | Z; μ] :=
    condDistrib_fst_prod (Y := X) (X := Z) (ν := ν) (μ := μ) (by fun_prop) (by fun_prop)
  have h_fst1 : (μ.prod ν).map (fun ω ↦ Z ω.1) = μ.map Z := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h_fst2 : (μ.prod ν).map (fun ω ↦ (Z ω.1, Y ω.1, X ω.1))
      = μ.map (fun ω ↦ (Z ω, Y ω, X ω)) := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h_fst1, h_fst2, h_indep]
  refine Measure.bind_congr_right ?_
  filter_upwards [h1, h2] with x hx1 hx2
  simp_rw [Kernel.prod_apply]
  rw [hx1, ← hx2]

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

omit [Nonempty Ω'] in
lemma cond_of_condIndepFun [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β] [Countable β]
    [Countable Ω']
    [IsZeroOrProbabilityMeasure μ]
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ)
    (hX : Measurable X) (hY : Measurable Y) {b : β} {ω : Ω'}
    (hμ : μ (X ⁻¹' {b} ∩ Z ⁻¹' {ω}) ≠ 0) :
    (μ[|X ⁻¹' {b} ∩ Z ⁻¹' {ω}]).map Y = (μ[|Z ⁻¹' {ω}]).map Y := by
  have h := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkLeft hX hY hZ).mp h
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
