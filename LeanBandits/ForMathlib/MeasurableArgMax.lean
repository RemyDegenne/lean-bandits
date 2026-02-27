/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurable argmax function

-/

open MeasureTheory Finset
open scoped ENNReal NNReal

section MeasurableArgmax -- copied from PR #27579 (and changed from argmin to argmax)

lemma measurable_encode {α : Type*} {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    Measurable (Encodable.encode (α := α)) := by
  refine measurable_to_nat fun a ↦ ?_
  have : Encodable.encode ⁻¹' {Encodable.encode a} = {a} := by ext; simp
  rw [this]
  exact measurableSet_singleton _

lemma measurableEmbedding_encode (α : Type*) {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    MeasurableEmbedding (Encodable.encode (α := α)) where
  injective := Encodable.encode_injective
  measurable := measurable_encode
  measurableSet_image' _ _ := .of_discrete

section Finite

variable {𝓧 𝓨 α : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {mα : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
  [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]

lemma measurableSet_isMax [Countable 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y)) (y : 𝓨) :
    MeasurableSet {x | ∀ z, f x z ≤ f x y} := by
  rw [show {x | ∀ y', f x y' ≤ f x y} = ⋂ y', {x | f x y' ≤ f x y} by ext; simp]
  exact MeasurableSet.iInter fun z ↦ measurableSet_le (by fun_prop) (by fun_prop)

lemma exists_isMaxOn' {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    ∃ n : ℕ, ∃ y, n = Encodable.encode y ∧ ∀ z, f x z ≤ f x y := by
  obtain ⟨y, h⟩ := Finite.exists_max (f x)
  exact ⟨Encodable.encode y, y, rfl, h⟩

/-- A measurable argmax function. -/
noncomputable
def measurableArgmax [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y]
    (x : 𝓧) :
    𝓨 :=
  (measurableEmbedding_encode 𝓨).invFun (Nat.find (exists_isMaxOn' f x))

lemma measurable_measurableArgmax [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    {f : 𝓧 → 𝓨 → α}
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y]
    (hf : ∀ y, Measurable (fun x ↦ f x y)) :
    Measurable (measurableArgmax f) := by
  refine (MeasurableEmbedding.measurable_invFun (measurableEmbedding_encode 𝓨)).comp ?_
  refine measurable_find _ fun n ↦ ?_
  have : {x | ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y}
      = ⋃ y, ({x | n = Encodable.encode y} ∩ {x | ∀ z, f x z ≤ f x y}) := by ext; simp
  rw [this]
  refine MeasurableSet.iUnion fun y ↦ (MeasurableSet.inter (by simp) ?_)
  exact measurableSet_isMax (by fun_prop) y

lemma isMaxOn_measurableArgmax {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y]
    (x : 𝓧) (z : 𝓨) :
    f x z ≤ f x (measurableArgmax f x) := by
  obtain ⟨y, h_eq, h_le⟩ := Nat.find_spec (exists_isMaxOn' f x)
  refine le_trans (h_le z) (le_of_eq ?_)
  rw [measurableArgmax, h_eq,
    MeasurableEmbedding.leftInverse_invFun (measurableEmbedding_encode 𝓨) y]

/-- Congruence lemma: measurableArgmax only depends on the function values at the point. -/
lemma measurableArgmax_congr {𝓧₁ 𝓧₂ : Type*} {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f₁ : 𝓧₁ → 𝓨 → α) (f₂ : 𝓧₂ → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f₁ x z ≤ f₁ x y]
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f₂ x z ≤ f₂ x y]
    (x₁ : 𝓧₁) (x₂ : 𝓧₂) (h : f₁ x₁ = f₂ x₂) :
    measurableArgmax f₁ x₁ = measurableArgmax f₂ x₂ := by
  simp only [measurableArgmax]; congr 1
  exact Nat.find_congr' fun {_} =>
    ⟨fun ⟨y, hn, hy⟩ => ⟨y, hn, h ▸ hy⟩, fun ⟨y, hn, hy⟩ => ⟨y, hn, h.symm ▸ hy⟩⟩

/-- measurableArgmax is independent of the DecidablePred instance used.
    This follows from Nat.find_congr' which handles different decidability instances. -/
lemma measurableArgmax_eq_of_eq {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f : 𝓧 → 𝓨 → α)
    (d1 : ∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y)
    (d2 : ∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x z ≤ f x y)
    (x : 𝓧) :
    @measurableArgmax 𝓧 𝓨 α _ _ _ _ _ _ f d1 x = @measurableArgmax 𝓧 𝓨 α _ _ _ _ _ _ f d2 x := by
  simp only [measurableArgmax]; congr 1
  exact @Nat.find_congr' _ _ (d1 x) (d2 x) _ _ (fun {_} ↦ Iff.rfl)

end Finite
end MeasurableArgmax
