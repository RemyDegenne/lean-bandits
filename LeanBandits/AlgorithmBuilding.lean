/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit

/-! # Tools to build bandit algorithms

-/

open MeasureTheory ProbabilityTheory Finset
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

end Finite
end MeasurableArgmax

namespace Bandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

/-- Number of pulls of arm `a` up to (and including) time `n`. -/
noncomputable
def pullCount' (n : ℕ) (h : Iic n → α × ℝ) (a : α) := #{s | (h s).1 = a}

/-- Sum of rewards of arm `a` up to (and including) time `n`. -/
noncomputable
def sumRewards' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  ∑ s, if (h s).1 = a then (h s).2 else 0

/-- Empirical mean of arm `a` at time `n`. -/
noncomputable
def empMean' (n : ℕ) (h : Iic n → α × ℝ) (a : α) :=
  (sumRewards' n h a) / (pullCount' n h a)

omit [MeasurableSpace α] in
lemma pullCount'_eq_sum (n : ℕ) (h : Iic n → α × ℝ) (a : α) :
    pullCount' n h a = ∑ s : Iic n, if (h s).1 = a then 1 else 0 := by simp [pullCount']

@[fun_prop]
lemma measurable_pullCount' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_sumRewards' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ sumRewards' n h a) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable (fun (h : Iic n → α × ℝ) ↦ if (h s).1 = a then (h s).2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean' [MeasurableSingletonClass α] (n : ℕ) (a : α) :
    Measurable (fun h ↦ empMean' n h a) := by
  unfold empMean'
  fun_prop

end Bandits
