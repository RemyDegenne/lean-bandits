/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import Mathlib

/-!
# Online gradient descent

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {E Ω : Type*} {mE : MeasurableSpace E} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [MeasurableSub₂ E] [SecondCountableTopology E]
  {f : ℕ → E → ℝ} {hf : ∀ n, Measurable (∇ (f n))} {x x₀ : E}
  {g : ℕ → E → E} {hg : ∀ n, Measurable (g n)}
  {env : Environment E E}
  {X G : ℕ → Ω → E} {γ : ℕ → ℝ}

-- todo: write a process version? with `X : ℕ → Ω → E`, as a `ℕ → Ω → F`
def onlineRegret {E F : Type*} [AddCommGroup F] (ℓ : ℕ → E → F) (y : E) (x : ℕ → E) (n : ℕ) : F :=
  ∑ i ∈ Finset.range n, (ℓ i (x i) - ℓ i y)

noncomputable def linearizedLoss (f : ℕ → E → ℝ) (x : ℕ → E) : ℕ → E → ℝ :=
  fun n y ↦ ⟪y, ∇ (f n) (x n)⟫

/-- Online gradient descent with step sizes `γ : ℕ → ℝ` and initial point `x₀ : E`,
without projection.

It is an algorithm that chooses actions in `E` and gets feedback in `E` (gradient of the function at
the queried point). -/
noncomputable
def gradientDescent (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  detAlgorithm (fun n hist ↦ (hist ⟨n, by grind⟩).1 - γ n • (hist ⟨n, by grind⟩).2) (by fun_prop) x₀

lemma action_gradientDescent_ae_eq (h_seq : IsAlgEnvSeq X G (gradientDescent γ x₀) env P) (n : ℕ) :
    X (n + 1) =ᵐ[P] X n - γ n • G n := h_seq.action_detAlgorithm_ae_eq n

lemma action_gradientDescent_ae_all_eq (h_seq : IsAlgEnvSeq X G (gradientDescent γ x₀) env P) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ ∧ ∀ n, X (n + 1) ω = X n ω - γ n • G n ω :=
  h_seq.action_detAlgorithm_ae_all_eq

lemma action_ae_eq_sub_sum (h_seq : IsAlgEnvSeq X G (gradientDescent γ x₀) env P) (n : ℕ) :
    X n =ᵐ[P] fun ω ↦ x₀ - ∑ i ∈ Finset.range n, γ i • G i ω := by
  filter_upwards [h_seq.action_detAlgorithm_ae_all_eq] with ω ⟨hω0, hω⟩
  induction n with
  | zero => simpa
  | succ n ih => rw [hω n, Finset.sum_range_succ, ← sub_sub]; congr

section Convex

lemma todo' {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (x y : E) :
    f x - f y ≤ ⟪x - y, ∇ f x⟫ := by
  sorry

lemma todo'2 {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (x : ℕ → E) (y : E) (n : ℕ) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := sorry
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by gcongr; exact todo' hf (x _) y

lemma todo'' (x y g : E) (η : ℝ) :
    ⟪x - y, g⟫ = (2 * η)⁻¹ * (‖x - y‖ ^ 2 - ‖(x - η • g) - y‖ ^ 2) + (η / 2) * ‖g‖ ^ 2 := by
  sorry

lemma todo (x y g : ℕ → E) (η : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y i, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * η i)⁻¹ * (‖x i - y i‖ ^ 2 - ‖(x i - η i • g i) - y i‖ ^ 2) +
          (η i / 2) * ‖g i‖ ^ 2) := by
  gcongr with i hi
  rw [todo'' (x i) (y i) (g i) (η i)]

lemma todo''' (x g : ℕ → E) (y : E)
    (η : ℝ) (hη : 0 ≤ η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * (‖x 0 - y‖ ^ 2 - ‖x n - y‖ ^ 2) + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [todo x (fun _ ↦ y) g (fun _ ↦ η) n]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  gcongr
  refine le_of_eq ?_
  simp_rw [← hx]
  sorry

lemma lem14dot1 (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 ≤ η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [todo''' x g y η hη hx n]
  gcongr
  exact sub_le_self _ (sq_nonneg _)

end Convex

section Stochastic

variable {gradKernel : ℕ → Kernel E E} [∀ n, IsMarkovKernel (gradKernel n)]

-- use `obliviousEnv gradKernel` as the environment for stochastic gradient descent
example (gradKernel : ℕ → Kernel E E) [∀ n, IsMarkovKernel (gradKernel n)] :
    Environment E E := obliviousEnv gradKernel

-- use the deterministic equality wrt any sequence
lemma todo1 {η : ℝ} (hη : 0 ≤ η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    ∀ᵐ ω ∂P, ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫ ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖G i ω‖ ^ 2 := by
  filter_upwards [action_gradientDescent_ae_all_eq h] with ω hω
  refine (lem14dot1 _ _ y η hη hω.2 n).trans_eq ?_
  congr
  exact hω.1

lemma sfdsf {η : ℝ} (hη : 0 ≤ η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ⟪X n ω - y, G n ω⟫] = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by
  sorry

lemma qfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n))
    {η : ℝ} (hη : 0 ≤ η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (y : E) (n : ℕ) :
    P[fun ω ↦ f n (X n ω) - f n y] ≤ P[fun ω ↦ ⟪X n ω - y, G n ω⟫] := by
  rw [sfdsf hη h h_unbiased y n]
  gcongr
  · refine Integrable.sub ?_ (integrable_const _)
    sorry
  · simp only [inner_sub_left]
    refine Integrable.sub ?_ ?_
    · sorry
    · sorry
  · exact fun ω ↦ todo' (hf n) (X n ω) y

lemma qsfqqfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n))
    {η : ℝ} (hη : 0 ≤ η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, f n (X n ω) - f n y] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  sorry

lemma qsfqgzr {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    {η : ℝ} (hη : 0 ≤ η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    (y : E) (n : ℕ) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X n ω) - f y] ≤
      (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  sorry

end Stochastic

end Learning
