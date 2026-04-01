/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.Algorithm
import LeanBandits.OptimizationAlgorithms.Utils.Tuple
import LeanBandits.SequentialLearning.EvaluationEnv

open MeasureTheory ProbabilityTheory Learning

/-!
# PRS: Pure Random Search
Implementation of the _Pure Random Search_ algorithm, which samples from the uniform
distribution on the input space at each iteration.
-/

variable {α β : Type*} [MeasureSpace α] [IsFiniteMeasure (ℙ : Measure α)]
  [NeZero (ℙ : Measure α)] [MeasurableSpace β]

open Set in
noncomputable
def PRS : Algorithm α β where
  policy _ := Kernel.const _ ((ℙ (univ : Set α))⁻¹ • ℙ)
  p0 := (ℙ (univ : Set α))⁻¹ • ℙ
  h_policy _ := ⟨fun _ ↦ by simp [isProbabilityMeasure_iff]⟩
  hp0 := by simp [isProbabilityMeasure_iff]

open Finset

variable {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) (hfc : ∀ x, f x ≤ f c)
  (A : ℕ → ℝ → ℝ) (R : ℕ → ℝ → ℝ)

noncomputable abbrev IsAlgEnvSeq.argmax (A : ℕ → ℝ → ℝ) (R : ℕ → ℝ → ℝ) (n : ℕ) (ω : ℝ) : ℝ :=
  A (Tuple.argmax (fun (i : Iic n) ↦ R i ω)) ω

noncomputable abbrev IsAlgEnvSeq.max (R : ℕ → ℝ → ℝ) (n : ℕ) (ω : ℝ) : ℝ :=
  R (Tuple.argmax (fun (i : Iic n) ↦ R i ω)) ω

open Filter Topology ENNReal in
lemma ENNReal.tendsto_zero_le {α : Type*} {f g : α → ℝ≥0∞} {ι : Filter α}
    (hg : Tendsto g ι (𝓝 0)) (h : f ≤ g) : Tendsto f ι (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ 0) tendsto_const_nhds hg ?_ h
  intro
  simp

variable [IsFiniteMeasure (ℙ : Measure ℝ)] -- False, but assumed now for simplicity

open Filter Topology ENNReal in
example (h' : IsAlgEnvSeq A R PRS (evalEnv hf.measurable) ((ℙ (Set.univ : Set ℝ))⁻¹ • ℙ)) :
    TendstoInMeasure ((ℙ (Set.univ : Set α))⁻¹ • ℙ) (IsAlgEnvSeq.max R) atTop (fun _ ↦ f c) := by
  set μ := ((ℙ (Set.univ : Set α))⁻¹ • (ℙ : Measure ℝ))
  rw [tendstoInMeasure_iff_dist]
  intro ε₁ hε₁
  rw [Metric.continuous_iff] at hf
  specialize hf c ε₁ hε₁
  obtain ⟨δ, hδ, hf⟩ := hf
  let h : ℕ → ℝ≥0∞ := fun n ↦ μ {x | δ ≤ dist (IsAlgEnvSeq.argmax A R n x) c}
  refine tendsto_zero_le (g := h) ?_ ?_
  · sorry
  · intro n
    simp only [h]
    refine measure_mono ?_
    simp only [Set.setOf_subset_setOf]
    intro a
    by_contra! h''
    specialize hf (IsAlgEnvSeq.argmax A R n a) h''.2
    have := h''.1
    suffices IsAlgEnvSeq.max R n a = f (IsAlgEnvSeq.argmax A R n a) by
      rw [← this] at hf
      linarith

    sorry
