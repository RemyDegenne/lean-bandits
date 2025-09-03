/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian
import LeanBandits.Bandit
import LeanBandits.Regret

/-! # The Explore-Then-Commit Algorithm

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

variable {K : ℕ}

-- TODO: when defining the kernel of an algorithm, we use `Iic n → α × ℝ` as the history type.
-- But for all the defs in the regret file, we use `ℕ → α × ℝ` as the history type.
-- Should we unify this?

/-- The empirical mean of arm `a` at time `n` but weighted by `m`.
We will use it only for `n = K * m - 1`, time for which there is indeed `m` samples for each arm,
but for reasons that have to do with type equalities we define it for arbitrary `n`. -/
noncomputable
def empMeanETC (m n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) :=
  (∑ s : Iic n, if (h s).1 = a then (h s).2 else 0) / m

@[fun_prop]
lemma measurable_empMeanETC (m n : ℕ) (a : Fin K) :
    Measurable (fun h ↦ empMeanETC m n h a) := by
  unfold empMeanETC
  have h_meas s :
      Measurable (fun (h : Iic n → Fin K × ℝ) ↦ if (h s).1 = a then (h s).2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

/-- Arm pulled by the ETC algorithm. -/
noncomputable
def etcArm (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if hn : n < K * m - 1 then
    ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ -- for `n = 0` we have pulled arm 0 already, and we pull arm 1
  else
    if hn_eq : n = K * m - 1 then measurableArgmax (empMeanETC m n) h
    else (h ⟨n - 1, by simp⟩).1

@[fun_prop]
lemma measurable_etcArm (hK : 0 < K) (m n : ℕ) : Measurable (etcArm hK m n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold etcArm
  simp only [dite_eq_ite]
  refine Measurable.ite (by simp) (by fun_prop) ?_
  refine Measurable.ite (by simp) ?_ (by fun_prop)
  exact measurable_measurableArgmax fun a ↦ by fun_prop

/-- The Explore-Then-Commit Kernel, which describes the arm pulled by the ETC algorithm. -/
noncomputable
def etcKernel (hK : 0 < K) (m n : ℕ) : Kernel (Iic n → Fin K × ℝ) (Fin K) :=
  Kernel.deterministic (etcArm hK m n) (by fun_prop)

instance (hK : 0 < K) (m n : ℕ) : IsMarkovKernel (etcKernel hK m n) := by
  unfold etcKernel
  infer_instance

/-- The measure describing the first pull of the ETC algorithm. -/
noncomputable
def etcP0 (hK : 0 < K) : Measure (Fin K) := Measure.dirac ⟨0, hK⟩

instance (hK : 0 < K) : IsProbabilityMeasure (etcP0 hK) := by
  unfold etcP0
  infer_instance

/-- A bandit interaction between the ETC algorithm and an environment given by reward
distributions. -/
noncomputable
def ETCBandit (hK : 0 < K) (m : ℕ) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] : Bandit (Fin K) where
  ν := ν
  policy := etcKernel hK m
  p0 := etcP0 hK

end Bandits
