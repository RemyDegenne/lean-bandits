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
  {X G : ℕ → Ω → E} {γ : ℕ → ℝ} {η : ℝ}

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

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma _root_.ConvexOn.fderiv_sub_le_sub {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have h_convex t (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      f (x + t • (y - x)) ≤ t * f y + (1 - t) * f x := by
    have h1 : x + t • (y - x) = (1 - t) • x + t • y := by module
    have h2 : f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y :=
      hf.2 (Set.mem_univ x) (Set.mem_univ y) (by grind) (by grind) (by simp)
    simp only [smul_eq_mul] at h2
    grind
  have h_path_deriv : HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
      (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
      simpa using hfx.hasFDerivAt
    exact h2.comp_hasDerivAt _ h1
  refine le_of_tendsto h_path_deriv.tendsto_slope_zero_right (Filter.eventually_of_mem
    (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩) fun t ht ↦ ?_)
  simp [inv_mul_le_iff₀ ht.1]
  grind

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma _root_.ConvexOn.add_fderiv_le {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  suffices fderiv ℝ f x (y - x) ≤ f y - f x by grind
  exact hf.fderiv_sub_le_sub hfx y

omit [SecondCountableTopology E] in
lemma _root_.ConvexOn.add_inner_gradient_le {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + ⟪y - x, ∇ f x⟫ ≤ f y := by
  have hfderiv : (fderiv ℝ f x) (y - x) = ⟪y - x, ∇ f x⟫ := by
    simp [gradient, ← InnerProductSpace.toDual_symm_apply, real_inner_comm]
  rw [← hfderiv]
  exact hf.add_fderiv_le hfx y

omit [SecondCountableTopology E] in
lemma _root_.ConvexOn.le_add_inner_gradient {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x ≤ f y + ⟪x - y, ∇ f x⟫ := by
  have h_add_le := hf.add_inner_gradient_le hfx y
  have h_neg : ⟪x - y, ∇ f x⟫ = -⟪y - x, ∇ f x⟫ := by
    rw [show x - y = -(y - x) by abel, inner_neg_left]
  grind

omit [SecondCountableTopology E] in
lemma _root_.ConvexOn.sub_le_inner_gradient {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x - f y ≤ ⟪x - y, ∇ f x⟫ := by
  simp only [tsub_le_iff_right]
  rw [add_comm]
  exact hf.le_add_inner_gradient hfx y

omit [SecondCountableTopology E] in
lemma todo'2 {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (x i) - f y := by
    simp_rw [smul_sum]
    grw [hf.map_sum_le (fun _ _ ↦ by positivity) (by simp; field) (by simp)]
  _ = (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := by
    simp_rw [smul_eq_mul, mul_sum, mul_sub, sum_sub_distrib]
    rw [← sum_mul]
    simp
    field
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
    gcongr
    exact hf.sub_le_inner_gradient hdf.differentiableAt y

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma todo'' (x y g : E) (hη : 0 < η) :
    ⟪x - y, g⟫ = (2 * η)⁻¹ * (‖x - y‖ ^ 2 - ‖(x - η • g) - y‖ ^ 2) + (η / 2) * ‖g‖ ^ 2 := by
  have hsub : (x - η • g) - y = (x - y) - η • g := by abel
  rw [hsub, norm_sub_sq_real (x - y) (η • g)]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  field

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma todo (x y g : ℕ → E) (hη : ∀ n, 0 < γ n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y i, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * γ i)⁻¹ * (‖x i - y i‖ ^ 2 - ‖(x i - γ i • g i) - y i‖ ^ 2) +
          (γ i / 2) * ‖g i‖ ^ 2) := by
  gcongr with i hi
  rw [todo'' (x i) (y i) (g i) (hη i)]

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma todo''' (x g : ℕ → E) (y : E)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * (‖x 0 - y‖ ^ 2 - ‖x n - y‖ ^ 2) + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [todo x (fun _ ↦ y) g (fun _ ↦ hη) n]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  gcongr
  refine le_of_eq ?_
  simp_rw [← hx]
  exact Finset.sum_range_sub' (fun i ↦ ‖x i - y‖ ^ 2) n

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma lem14dot1 (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [todo''' x g y hη hx n]
  gcongr
  exact sub_le_self _ (sq_nonneg _)

end Convex

section Stochastic

variable {gradKernel : ℕ → Kernel E E} [∀ n, IsMarkovKernel (gradKernel n)]

-- use the deterministic equality wrt any sequence
lemma todo1 (hη : 0 < η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    ∀ᵐ ω ∂P, ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫ ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖G i ω‖ ^ 2 := by
  filter_upwards [action_gradientDescent_ae_all_eq h] with ω hω
  refine (lem14dot1 _ _ y η hη hω.2 n).trans_eq ?_
  congr
  exact hω.1

lemma sfdsf (hη : 0 < η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ⟪X n ω - y, G n ω⟫] = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by
  let M n := MeasurableSpace.comap (IsAlgEnvSeq.hist X G n) inferInstance
  calc P[fun ω ↦ ⟪X n ω - y, G n ω⟫]
  _ = P[fun ω ↦ P[fun ω' ↦ ⟪X n ω' - y, G n ω'⟫ | M n] ω] := by
    sorry
  _ = P[fun ω ↦ ⟪X n ω - y, P[G n | M n] ω⟫] := by
    sorry
  _ = P[fun ω ↦ ⟪X n ω - y, P[G n | MeasurableSpace.comap (X n) inferInstance] ω⟫] := by
    sorry
  _ = P[fun ω ↦ ⟪X n ω - y, (gradKernel n (X n ω))[id]⟫] := by
    refine integral_congr_ae ?_
    sorry
  _ = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by simp_rw [h_unbiased n]

lemma sfdsf' (hη : 0 < η)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (y : E) (n : ℕ) :
    ∫⁻ ω, ‖∇ (f n) (X n ω)‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, ‖G n ω‖ₑ ^ 2 ∂P := by
  simp_rw [← h_unbiased]
  sorry

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] in
theorem _root_.MeasureTheory.MemLp.eLpNorm_rpow_norm_lt_top {f : Ω → E} {p : ℝ≥0∞}
    (hf : MemLp f p P) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (fun x ↦ ‖f x‖ ^ p.toReal) 1 P < ∞ := by
  simpa [eLpNorm_one_eq_lintegral_enorm, enorm_rpow_of_nonneg] using
    (hf.integrable_enorm_rpow hp_zero hp_top).hasFiniteIntegral

omit [IsProbabilityMeasure P] [CompleteSpace E] [SecondCountableTopology E] in
lemma _root_.MeasureTheory.MemLp.integrable_inner {f g : Ω → E}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω ↦ ⟪f ω, g ω⟫) P := by
  rw [← memLp_one_iff_integrable]
  constructor
  · exact hf.aestronglyMeasurable.inner hg.aestronglyMeasurable
  have h x : ‖⟪f x, g x⟫‖ ≤ ‖‖f x‖ ^ (2 : ℝ) + ‖g x‖ ^ (2 : ℝ)‖ := by
    norm_cast
    calc ‖⟪f x, g x⟫‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) one_le_two
      _ ≤ ‖‖f x‖ ^ 2 + ‖g x‖ ^ 2‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
  refine (eLpNorm_mono h).trans_lt ((eLpNorm_add_le ?_ ?_ le_rfl).trans_lt ?_)
  · exact (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact (hg.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨hf.eLpNorm_rpow_norm_lt_top (by simp) (by simp),
    hg.eLpNorm_rpow_norm_lt_top (by simp) (by simp)⟩

lemma qfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n))
    (hdf : ∀ n, Differentiable ℝ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ f n (X n ω) - f n y] ≤ P[fun ω ↦ ⟪X n ω - y, G n ω⟫] := by
  rw [sfdsf hη h h_unbiased y n]
  gcongr
  · refine Integrable.sub ?_ (integrable_const _)
    sorry
  · refine MemLp.integrable_inner ?_ ?_
    · sorry
    · sorry
  · exact fun ω ↦ (hf n).sub_le_inner_gradient (hdf n).differentiableAt y

lemma qsfqqfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, f n (X n ω) - f n y] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  sorry

lemma qsfqgzr {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientDescent (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X n ω) - f y] ≤
      (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  sorry

end Stochastic

end Learning
