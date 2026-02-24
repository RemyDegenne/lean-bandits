/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.BanditAlgorithms.UCB
import LeanBandits.SequentialLearning.BayesStationaryEnv
import LeanBandits.SequentialLearning.HistoryDensity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The Thompson Sampling Algorithm -/

open MeasureTheory ProbabilityTheory Finset Learning

open scoped ENNReal NNReal

namespace Bandits

namespace TS

variable {K : ℕ} (hK : 0 < K)
variable {𝓔 : Type*} [mE : MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ) [IsMarkovKernel κ]

/-- The distribution over actions for every given history for TS. -/
noncomputable
def policy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (IT.bayesTrajMeasurePosterior Q κ (uniformAlgorithm hK) n).map
    (IsBayesAlgEnvSeq.bestAction κ id)

instance (n : ℕ) : IsMarkovKernel (policy hK Q κ n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold policy
  exact Kernel.IsMarkovKernel.map _
    (IsBayesAlgEnvSeq.measurable_bestAction measurable_id)

/-- The initial distribution over actions for TS. -/
noncomputable
def initialPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (IsBayesAlgEnvSeq.bestAction κ id)

instance : IsProbabilityMeasure (initialPolicy hK Q κ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact Measure.isProbabilityMeasure_map
    (IsBayesAlgEnvSeq.measurable_bestAction (by fun_prop)).aemeasurable

end TS

variable {K : ℕ}

section Algorithm

variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]

/-- The Thompson Sampling (TS) algorithm: actions are chosen according to the probability that they
are optimal given prior knowledge represented by a prior distribution `Q` and a data generation
model represented by a kernel `κ`. -/
noncomputable
def tsAlgorithm (hK : 0 < K) (Q : Measure 𝓔) [IsProbabilityMeasure Q]
    (κ : Kernel (𝓔 × Fin K) ℝ) [IsMarkovKernel κ] : Algorithm (Fin K) ℝ where
  policy := TS.policy hK Q κ
  p0 := TS.initialPolicy hK Q κ

end Algorithm

section Regret

variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable (hK : 0 < K)
variable {Ω : Type*} [MeasurableSpace Ω]
variable (E' : Ω → E) (A : ℕ → Ω → (Fin K)) (R' : ℕ → Ω → ℝ)
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (E × Fin K) ℝ) [IsMarkovKernel κ]
variable (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable
def ucbIndex (A : ℕ → Ω → Fin K) (R' : ℕ → Ω → ℝ) (σ2 lo hi δ : ℝ)
    (a : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  if pullCount A a t ω = 0 then hi
  else max lo (min hi
    (empMean A R' a t ω
      + √(2 * σ2 * Real.log (1 / δ) / (pullCount A a t ω : ℝ))))

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma lo_le_ucbIndex (σ2 lo hi δ : ℝ) (hlo : lo ≤ hi) (a : Fin K) (t : ℕ) (ω : Ω) :
    lo ≤ ucbIndex A R' σ2 lo hi δ a t ω := by
  unfold ucbIndex; split_ifs <;> [exact hlo; exact le_max_left lo _]

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma ucbIndex_le_hi (σ2 lo hi δ : ℝ) (hlo : lo ≤ hi) (a : Fin K) (t : ℕ) (ω : Ω) :
    ucbIndex A R' σ2 lo hi δ a t ω ≤ hi := by
  unfold ucbIndex; split_ifs <;> [exact le_refl _; exact max_le hlo (min_le_left hi _)]

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma ucbIndex_mem_Icc (σ2 lo hi δ : ℝ) (hlo : lo ≤ hi) (a : Fin K) (t : ℕ) (ω : Ω) :
    ucbIndex A R' σ2 lo hi δ a t ω ∈ Set.Icc lo hi :=
  ⟨lo_le_ucbIndex A R' σ2 lo hi δ hlo a t ω, ucbIndex_le_hi A R' σ2 lo hi δ hlo a t ω⟩

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma abs_ucbIndex_le (σ2 lo hi δ : ℝ) (hlo : lo ≤ hi) (a : Fin K) (t : ℕ) (ω : Ω) :
    |ucbIndex A R' σ2 lo hi δ a t ω| ≤ max |lo| |hi| := by
  have hmem := ucbIndex_mem_Icc A R' σ2 lo hi δ hlo a t ω
  exact abs_le_max_abs_abs hmem.1 hmem.2

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma norm_ucbIndex_le (σ2 lo hi δ : ℝ) (hlo : lo ≤ hi) (a : Fin K) (t : ℕ) (ω : Ω) :
    ‖ucbIndex A R' σ2 lo hi δ a t ω‖ ≤ max |lo| |hi| := by
  rw [Real.norm_eq_abs]; exact abs_ucbIndex_le A R' σ2 lo hi δ hlo a t ω

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma abs_sub_le_of_mem_Icc {lo hi x y : ℝ} (hx : x ∈ Set.Icc lo hi)
    (hy : y ∈ Set.Icc lo hi) :
    |x - y| ≤ hi - lo := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∑ i ∈ s, √(c i) ≤ √(#s * ∑ i ∈ s, c i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s hc (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, sum_const, nsmul_eq_mul] at h
  calc ∑ i ∈ s, √(c i) ≤ √(∑ i ∈ s, c i) * √↑(#s) := h
    _ = _ := by rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hc i)), mul_comm]

omit [StandardBorelSpace E] [Nonempty E] in
lemma sum_inv_sqrt_max_one_le (N : ℕ) :
    ∑ j ∈ range N, (1 / √(↑(max 1 j) : ℝ)) ≤ 2 * √↑N := by
  suffices h : ∀ M : ℕ, 0 < M →
      ∑ j ∈ range M, (1 / √(↑(max 1 j) : ℝ)) + 1 / √↑M ≤ 2 * √↑M by
    cases N with
    | zero => simp
    | succ n =>
      have := h (n + 1) (Nat.succ_pos n)
      linarith [div_nonneg zero_le_one (Real.sqrt_nonneg (↑(n + 1) : ℝ))]
  intro M hM
  induction M with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn : n = 0
    · subst hn; simp; norm_num
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hmax : (↑(max 1 n) : ℝ) = ↑n := by
        simp [Nat.max_eq_right (by omega : 1 ≤ n)]
      rw [hmax]
      have h_ih := ih hn_pos
      suffices h_key : 1 / √(↑(n + 1) : ℝ) ≤ 2 * (√↑(n + 1) - √↑n) by linarith
      have hns : (0 : ℝ) < ↑(n + 1) := by positivity
      have hnn : (0 : ℝ) ≤ ↑n := by positivity
      set a := √(↑(n + 1) : ℝ)
      set b := √(↑n : ℝ)
      have hsn : a * a = ↑(n + 1) := Real.mul_self_sqrt (le_of_lt hns)
      have hs : b * b = ↑n := Real.mul_self_sqrt hnn
      have hab : 2 * (a * b) ≤ ↑(n + 1) + ↑n := by
        nlinarith [mul_self_nonneg (a - b)]
      rw [div_le_iff₀ (by positivity : 0 < a)]
      have h_expand : 2 * (a - b) * a = 2 * (a * a) - 2 * (a * b) := by ring
      rw [h_expand, hsn]
      have : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
      linarith

@[fun_prop]
lemma measurable_ucbIndex [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    (σ2 lo hi δ : ℝ) (a : Fin K) (t : ℕ) :
    Measurable (ucbIndex A R' σ2 lo hi δ a t) := by
  unfold ucbIndex
  have hpc : Measurable (fun ω ↦ (pullCount A a t ω : ℝ)) :=
    measurable_from_top.comp (measurable_pullCount (fun n ↦ h.measurable_A n) a t)
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurable_pullCount (fun n ↦ h.measurable_A n) a t) (measurableSet_singleton 0)
  · exact (Measurable.max measurable_const (Measurable.min measurable_const
      (Measurable.add (measurable_empMean (fun n ↦ h.measurable_A n)
        (fun n ↦ h.measurable_R n) a t)
      (measurable_const.div hpc).sqrt)))

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma armMean_le_ucbIndex {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ (Set.Icc lo hi))
    (σ2 δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω)
    (hconc : pullCount A a t ω ≠ 0 →
      |empMean A R' a t ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|
        < √(2 * σ2 * Real.log (1 / δ) / (pullCount A a t ω : ℝ))) :
    IsBayesAlgEnvSeq.actionMean κ E' a ω ≤ ucbIndex A R' σ2 lo hi δ a t ω := by
  unfold ucbIndex
  have hmean := hm a (E' ω)
  simp only [IsBayesAlgEnvSeq.actionMean] at hmean hconc ⊢
  split_ifs with h0
  · exact hmean.2
  · have habs := abs_sub_lt_iff.mp (hconc h0)
    refine le_max_of_le_right (le_min hmean.2 ?_)
    linarith [habs.2]

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma ucbIndex_sub_armMean_le {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ (Set.Icc lo hi))
    (σ2 δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω) (hpc : pullCount A a t ω ≠ 0)
    (hconc :
      |empMean A R' a t ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|
        < √(2 * σ2 * Real.log (1 / δ) / (pullCount A a t ω : ℝ))) :
    ucbIndex A R' σ2 lo hi δ a t ω - IsBayesAlgEnvSeq.actionMean κ E' a ω
      ≤ 2 * √(2 * σ2 * Real.log (1 / δ) / (pullCount A a t ω : ℝ)) := by
  unfold ucbIndex
  simp only [IsBayesAlgEnvSeq.actionMean] at hconc ⊢
  rw [if_neg hpc]
  set w := √(2 * σ2 * Real.log (1 / δ) / ↑(pullCount A a t ω))
  set emp := empMean A R' a t ω
  have habs := abs_sub_lt_iff.mp hconc
  have hmean := hm a (E' ω)
  have h1 : max lo (min hi (emp + w)) ≤ emp + w :=
    max_le_iff.mpr ⟨by linarith [hmean.1, habs.2], min_le_right _ _⟩
  linarith [habs.2]

lemma ts_identity [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P) (t : ℕ) :
    condDistrib (A (t + 1)) (IsAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
    condDistrib (IsBayesAlgEnvSeq.bestAction κ E') (IsAlgEnvSeq.hist A R' t) P :=
  by
  have h_ba_comp : IsBayesAlgEnvSeq.bestAction κ E'
      = IsBayesAlgEnvSeq.bestAction κ id ∘ E' := rfl
  rw [h_ba_comp]
  have hm := IsBayesAlgEnvSeq.measurable_bestAction (κ := κ) measurable_id
  have h_comp := condDistrib_comp (mβ := MeasurableSpace.pi) (μ := P)
    (IsAlgEnvSeq.hist A R' t) h.measurable_E.aemeasurable hm
  have h_map : (condDistrib E' (IsAlgEnvSeq.hist A R' t) P).map
      (IsBayesAlgEnvSeq.bestAction κ id) =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
      (IT.bayesTrajMeasurePosterior Q κ (uniformAlgorithm hK) t).map
        (IsBayesAlgEnvSeq.bestAction κ id) := by
    filter_upwards [posterior_eq_ref Q κ h (Bandits.uniformAlgorithm_hasFullSupport hK) t] with x hx
    simp only [Kernel.map_apply _ hm, hx]
  exact (h.hasCondDistrib_action' t).condDistrib_eq.trans (h_comp.trans h_map).symm

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma le_armMean_bestArm [Nonempty (Fin K)] (ω : Ω) (i : Fin K) :
    IsBayesAlgEnvSeq.actionMean κ E' i ω ≤
    IsBayesAlgEnvSeq.actionMean κ E' (IsBayesAlgEnvSeq.bestAction κ E' ω) ω := by
  have := isMaxOn_measurableArgmax (fun ω a ↦ IsBayesAlgEnvSeq.actionMean κ E' a ω) ω i
  simp only [IsBayesAlgEnvSeq.bestAction]; convert this

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma iSup_armMean_eq_bestArm [Nonempty (Fin K)] {lo hi : ℝ}
    (hm : ∀ a e, (κ (e, a))[id] ∈ Set.Icc lo hi)
    (ω : Ω) : ⨆ i, IsBayesAlgEnvSeq.actionMean κ E' i ω =
    IsBayesAlgEnvSeq.actionMean κ E' (IsBayesAlgEnvSeq.bestAction κ E' ω) ω :=
  le_antisymm (ciSup_le (le_armMean_bestArm E' κ ω))
    (le_ciSup (f := fun i ↦ IsBayesAlgEnvSeq.actionMean κ E' i ω)
      ⟨hi, by rintro _ ⟨i, rfl⟩; exact (hm i _).2⟩ _)

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma gap_eq_armMean_sub [Nonempty (Fin K)] {lo hi : ℝ}
    (hm : ∀ a e, (κ (e, a))[id] ∈ Set.Icc lo hi)
    (s : ℕ) (ω : Ω) : gap (κ.sectR (E' ω)) (A s ω) =
    IsBayesAlgEnvSeq.actionMean κ E' (IsBayesAlgEnvSeq.bestAction κ E' ω) ω -
    IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω := by
  simp only [gap, Kernel.sectR_apply]
  exact congr_arg (· - _) (iSup_armMean_eq_bestArm E' κ hm ω)

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure Q] [IsMarkovKernel κ] in
lemma bayesRegret_eq_sum_integral_gap [Nonempty (Fin K)]
    {alg : Algorithm (Fin K) ℝ}
    (h : IsBayesAlgEnvSeq Q κ alg E' A R' P)
    {C : ℝ} (hm : ∀ a e, |(κ (e, a))[id]| ≤ C) (t : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E' A t] =
    ∑ s ∈ range t, P[fun ω ↦ gap (κ.sectR (E' ω))
      (A s ω)] := by
  simp only [IsBayesAlgEnvSeq.regret, regret_eq_sum_gap]
  refine integral_finset_sum _ (fun s _ => ?_)
  have hmeas : Measurable (fun ω ↦ gap (κ.sectR (E' ω))
      (A s ω)) :=
    (Measurable.iSup (fun a ↦ IsBayesAlgEnvSeq.measurable_actionMean
      (a := a) h.measurable_E)).sub
      (stronglyMeasurable_id.integral_kernel.measurable.comp
        (h.measurable_E.prodMk (h.measurable_A s)))
  refine ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 2 * C)
    (Filter.Eventually.of_forall fun ω => ?_)⟩
  simp only [Real.norm_eq_abs, gap, Kernel.sectR_apply]
  have hbdd : BddAbove (Set.range fun i => (κ (E' ω, i))[id]) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; exact le_of_abs_le (hm i _)⟩
  rw [abs_of_nonneg (sub_nonneg.mpr (le_ciSup hbdd _))]
  linarith [ciSup_le fun i => le_of_abs_le (hm i (E' ω)),
    neg_le_of_abs_le (hm (A s ω) (E' ω))]

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsProbabilityMeasure Q]
    [IsMarkovKernel κ] [IsProbabilityMeasure P] in
lemma sum_comp_pullCount (f : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    ∑ s ∈ range n, f (pullCount A (A s ω) s ω) =
    ∑ a : Fin K, ∑ j ∈ range (pullCount A a n ω), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    suffices ∑ a, ∑ j ∈ range (pullCount A a (n + 1) ω), f j =
        (∑ a, ∑ j ∈ range (pullCount A a n ω), f j) +
        f (pullCount A (A n ω) n ω) by linarith
    have h_eq : ∀ a, ∑ j ∈ range (pullCount A a (n + 1) ω), f j =
        ∑ j ∈ range (pullCount A a n ω), f j +
        if A n ω = a then f (pullCount A a n ω) else 0 := by
      intro a
      rw [pullCount_add_one]
      split_ifs with h
      · rw [sum_range_succ]
      · simp
    simp_rw [h_eq, sum_add_distrib]
    congr 1
    simp

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsProbabilityMeasure Q]
    [IsMarkovKernel κ] [IsProbabilityMeasure P] in
lemma sum_ucbIndex_sub_armMean_le {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ (Set.Icc lo hi))
    (hlo : lo ≤ hi) (σ2 δ : ℝ) (n : ℕ) (ω : Ω)
    (hconc : ∀ s < n, ∀ a, pullCount A a s ω ≠ 0 →
      |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|
        < √(2 * σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ))) :
    ∑ s ∈ range n, (ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
        IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω)
      ≤ (hi - lo) * ↑K + 2 * √(8 * σ2 * Real.log (1 / δ)) * √(↑K * ↑n) := by
  -- Split range n into first-pull (pc=0) and non-first-pull (pc≠0) sets
  set S0 := (range n).filter (fun s => pullCount A (A s ω) s ω = 0)
  set S1 := (range n).filter (fun s => pullCount A (A s ω) s ω ≠ 0)
  have hpart : range n = S0 ∪ S1 := (Finset.filter_union_filter_not_eq _ _).symm
  have hdisj : Disjoint S0 S1 := Finset.disjoint_filter_filter_not _ _ _
  conv_lhs => rw [hpart]
  rw [Finset.sum_union hdisj]
  -- We bound ∑_{S0} and ∑_{S1} separately, then combine
  suffices h_S0 : ∑ s ∈ S0, (ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
        IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω) ≤ (hi - lo) * ↑K by
    suffices h_S1 : ∑ s ∈ S1, (ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
        IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω)
          ≤ 2 * √(8 * σ2 * Real.log (1 / δ)) * √(↑K * ↑n) by
      have := Finset.sum_union hdisj (f := fun s =>
        ucbIndex A R' σ2 lo hi δ (A s ω) s ω - IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω)
      rw [← hpart] at this; linarith
    -- Bound ∑_{S1}: each term ≤ 2√(2σ2c/pc) = 2√(2σ2c/max(1,pc)), so ≤ full sum
    calc ∑ s ∈ S1, (ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
            IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω)
        ≤ ∑ s ∈ S1,
            2 * √(2 * σ2 * Real.log (1 / δ) / (max 1 (pullCount A (A s ω) s ω) : ℝ)) :=
          sum_le_sum fun s hs => by
            have hpc : pullCount A (A s ω) s ω ≠ 0 := (Finset.mem_filter.mp hs).2
            have hpc_eq : (max 1 (pullCount A (A s ω) s ω) : ℝ) =
                (pullCount A (A s ω) s ω : ℝ) := by
              simp [Nat.one_le_iff_ne_zero.mpr hpc]
            rw [hpc_eq]
            exact ucbIndex_sub_armMean_le E' A R' κ hm σ2 δ (A s ω) s ω hpc
              (hconc s (mem_range.mp (Finset.mem_filter.mp hs).1) _ hpc)
      _ ≤ ∑ s ∈ range n,
            2 * √(2 * σ2 * Real.log (1 / δ) / (max 1 (pullCount A (A s ω) s ω) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun s _ _ => by positivity
      _ ≤ 2 * √(8 * σ2 * Real.log (1 / δ)) * √(↑K * ↑n) := by
          set c := Real.log (1 / δ)
          by_cases hc : 0 ≤ 2 * σ2 * c
          · open Real in
            calc ∑ s ∈ range n, 2 * √(2 * σ2 * c / max 1 ↑(pullCount A (A s ω) s ω))
                = ∑ s ∈ range n, √(8 * σ2 * c) *
                    (1 / √(↑(max 1 (pullCount A (A s ω) s ω)) : ℝ)) :=
                  sum_congr rfl fun s _ => by
                    rw [show (8 : ℝ) * σ2 * c = (2 : ℝ) ^ 2 * (2 * σ2 * c) from by ring]
                    rw [sqrt_mul (by positivity : (0:ℝ) ≤ 2 ^ 2),
                        sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
                    rw [sqrt_div (by linarith : 0 ≤ 2 * σ2 * c)]; push_cast; ring
              _ = √(8 * σ2 * c) * ∑ s ∈ range n,
                    (1 / √(↑(max 1 (pullCount A (A s ω) s ω)) : ℝ)) := by
                  rw [mul_sum]
              _ = √(8 * σ2 * c) * ∑ a : Fin K, ∑ j ∈ range (pullCount A a n ω),
                    (1 / √(↑(max 1 j) : ℝ)) := by
                  congr 1; exact sum_comp_pullCount A (fun j => 1 / √(↑(max 1 j) : ℝ)) n ω
              _ ≤ √(8 * σ2 * c) * ∑ a : Fin K, (2 * √↑(pullCount A a n ω)) := by
                  gcongr with a; exact sum_inv_sqrt_max_one_le _
              _ = √(8 * σ2 * c) * (2 * ∑ a : Fin K, √↑(pullCount A a n ω)) := by
                simp only [mul_sum]
              _ ≤ √(8 * σ2 * c) * (2 * √(↑K * ↑n)) := by
                  gcongr
                  calc ∑ a : Fin K, √↑(pullCount A a n ω)
                      ≤ √(↑(Finset.univ.card) * ∑ a, ↑(pullCount A a n ω)) :=
                        sum_sqrt_le Finset.univ _ fun a => by positivity
                    _ = √(↑K * ↑n) := by
                        congr 1; rw [Finset.card_fin]; congr 1
                        have h := sum_pullCount (A := A) (t := n) (ω := ω)
                        exact_mod_cast h
              _ = 2 * √(8 * σ2 * c) * √(↑K * ↑n) := by ring
          · have h0 : ∀ s ∈ range n,
                2 * √(2 * σ2 * c / max 1 ↑(pullCount A (A s ω) s ω)) = 0 :=
              fun s _ => by
                open Real in
                have : 2 * σ2 * c / max 1 ↑(pullCount A (A s ω) s ω) ≤ 0 :=
                  div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
                simp [sqrt_eq_zero'.mpr this]
            rw [sum_congr rfl h0]; simp only [sum_const_zero]; positivity
  -- Bound ∑_{S0}: each term = hi - armMean ≤ hi - lo, and #S0 ≤ K
  have hterm_S0 : ∀ s ∈ S0, ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
      IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω ≤ hi - lo := fun s hs => by
    have hpc : pullCount A (A s ω) s ω = 0 := (Finset.mem_filter.mp hs).2
    simp only [ucbIndex, hpc, ↓reduceIte, IsBayesAlgEnvSeq.actionMean]
    linarith [(hm (A s ω) (E' ω)).1]
  have h_card_S0 : #S0 ≤ K := by
    calc #S0 ≤ #(Finset.univ : Finset (Fin K)) :=
          Finset.card_le_card_of_injOn (fun s => A s ω)
            (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (by
              intro s₁ hs₁ s₂ hs₂ heq
              have hpc₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hs₁)).2
              have hpc₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hs₂)).2
              by_contra h_ne
              rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
              · have : s₁ ∈ (range s₂).filter (fun i => A i ω = A s₂ ω) := by
                  simp [mem_range.mpr h_lt, heq]
                exact absurd hpc₂ (show pullCount A (A s₂ ω) s₂ ω ≠ 0 from
                  Finset.card_ne_zero_of_mem this)
              · have : s₂ ∈ (range s₁).filter (fun i => A i ω = A s₁ ω) := by
                  simp [mem_range.mpr h_lt, ← heq]
                exact absurd hpc₁ (show pullCount A (A s₁ ω) s₁ ω ≠ 0 from
                  Finset.card_ne_zero_of_mem this))
      _ = K := Finset.card_fin K
  calc ∑ s ∈ S0, (ucbIndex A R' σ2 lo hi δ (A s ω) s ω -
          IsBayesAlgEnvSeq.actionMean κ E' (A s ω) ω)
      ≤ ∑ _s ∈ S0, (hi - lo) := sum_le_sum hterm_S0
    _ = #S0 * (hi - lo) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ↑K * (hi - lo) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast h_card_S0
    _ = (hi - lo) * ↑K := by ring

lemma streamMeasure_concentration_le_delta {α : Type*} [MeasurableSpace α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (a : α) (k : ℕ) (hk : k ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k +
        √(2 * ↑σ2 * Real.log (1 / δ) / k) ≤ (ν a)[id]} ≤
      ENNReal.ofReal δ := by
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hδ |>.mpr hδ1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hσ2_pos : (0 : ℝ) < ↑σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ2)
  calc
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k +
        √(2 * ↑σ2 * Real.log (1 / δ) / k) ≤ (ν a)[id]}
  _ = streamMeasure ν
        {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) / k ≤
          -√(2 * ↑σ2 * Real.log (1 / δ) / k)} := by
      congr with ω
      field_simp
      rw [Finset.sum_sub_distrib]
      simp
      grind
  _ = streamMeasure ν
        {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤
          -√(2 * k * ↑σ2 * Real.log (1 / δ))} := by
      congr with ω
      field_simp
      congr! 2
      rw [Real.sqrt_div (by positivity : 0 ≤ 2 * ↑σ2 * Real.log (1 / δ)),
        show ↑k * 2 * ↑σ2 * Real.log (1 / δ) = ↑k * (2 * ↑σ2 * Real.log (1 / δ)) from by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ↑k), ← mul_div_assoc,
        mul_div_right_comm, Real.div_sqrt]
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * k * ↑σ2 * Real.log (1 / δ)))^2 /
        (2 * k * ↑σ2))) := by
      rw [← ofReal_measureReal]
      gcongr
      refine HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun (c := σ2) ?_ ?_
        (by positivity)
      · exact (iIndepFun_eval_streamMeasure'' ν a).comp
          (fun i ω ↦ ω - (ν a)[id]) (fun _ ↦ by fun_prop)
      · intro i _; exact (hν a).congr_identDistrib
          ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)
  _ = ENNReal.ofReal δ := by
      rw [Real.sq_sqrt (by positivity)]
      simp only [neg_div, Real.exp_neg]
      rw [show 2 * (k : ℝ) * ↑σ2 * Real.log (1 / δ) / (2 * k * ↑σ2) =
        Real.log (1 / δ) from by field_simp [ne_of_gt hσ2_pos, ne_of_gt hk_pos]]
      rw [Real.exp_log (by positivity : (0 : ℝ) < 1 / δ), one_div, inv_inv]

lemma streamMeasure_concentration_ge_delta {α : Type*} [MeasurableSpace α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (a : α) (k : ℕ) (hk : k ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k -
        √(2 * ↑σ2 * Real.log (1 / δ) / k)} ≤
      ENNReal.ofReal δ := by
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hδ |>.mpr hδ1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hσ2_pos : (0 : ℝ) < ↑σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ2)
  calc
    streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k -
        √(2 * ↑σ2 * Real.log (1 / δ) / k)}
  _ = streamMeasure ν
        {ω | √(2 * ↑σ2 * Real.log (1 / δ) / k) ≤
          (∑ s ∈ range k, (ω s a - (ν a)[id])) / k} := by
      congr with ω
      field_simp
      rw [Finset.sum_sub_distrib]
      simp
      grind
  _ = streamMeasure ν
        {ω | √(2 * k * ↑σ2 * Real.log (1 / δ)) ≤
          (∑ s ∈ range k, (ω s a - (ν a)[id]))} := by
      congr with ω
      field_simp
      congr! 1
      rw [Real.sqrt_div (by positivity : 0 ≤ 2 * ↑σ2 * Real.log (1 / δ)),
        show 2 * ↑σ2 * Real.log (1 / δ) * ↑k = ↑k * (2 * ↑σ2 * Real.log (1 / δ)) from by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ↑k), ← mul_div_assoc,
        mul_div_right_comm, Real.div_sqrt]
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * k * ↑σ2 * Real.log (1 / δ)))^2 /
        (2 * k * ↑σ2))) := by
      rw [← ofReal_measureReal]
      gcongr
      refine HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (c := σ2) ?_ ?_
        (by positivity)
      · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
          (fun _ ↦ by fun_prop)
      · intro i _; exact (hν a).congr_identDistrib
          ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)
  _ = ENNReal.ofReal δ := by
      rw [Real.sq_sqrt (by positivity)]
      simp only [neg_div, Real.exp_neg]
      rw [show 2 * (k : ℝ) * ↑σ2 * Real.log (1 / δ) / (2 * k * ↑σ2) =
        Real.log (1 / δ) from by field_simp [ne_of_gt hσ2_pos, ne_of_gt hk_pos]]
      rw [Real.exp_log (by positivity : (0 : ℝ) < 1 / δ), one_div, inv_inv]

private lemma streamMeasure_concentration_bound {α : Type*} [MeasurableSpace α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (a : α) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : m ≠ 0) :
    streamMeasure ν {ω : ℕ → α → ℝ | ∑ i ∈ range m, ω i a ∈
        {x | x / m + √(2 * ↑σ2 * Real.log (1 / δ) / m) ≤ (ν a)[id]} ∪
        {x | (ν a)[id] ≤ x / m - √(2 * ↑σ2 * Real.log (1 / δ) / m)}} ≤
      ENNReal.ofReal (2 * δ) :=
  calc streamMeasure ν {ω : ℕ → α → ℝ | ∑ i ∈ range m, ω i a ∈
        {x | x / m + √(2 * ↑σ2 * Real.log (1 / δ) / m) ≤ (ν a)[id]} ∪
        {x | (ν a)[id] ≤ x / m - √(2 * ↑σ2 * Real.log (1 / δ) / m)}}
      ≤ streamMeasure ν {ω | (∑ i ∈ range m, ω i a) / m +
            √(2 * ↑σ2 * Real.log (1 / δ) / m) ≤ (ν a)[id]} +
          streamMeasure ν {ω | (ν a)[id] ≤ (∑ i ∈ range m, ω i a) / m -
            √(2 * ↑σ2 * Real.log (1 / δ) / m)} := by
        apply (measure_mono (fun ω hω ↦ ?_)).trans (measure_union_le _ _)
        simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢; exact hω
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
        gcongr
        · exact streamMeasure_concentration_le_delta hσ2 hν a m hm δ hδ hδ1
        · exact streamMeasure_concentration_ge_delta hσ2 hν a m hm δ hδ hδ1
    _ = ENNReal.ofReal (2 * δ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

lemma prob_concentration_single_delta_cond [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ Set.Icc lo hi)
    (a : Fin K) (s : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : max |lo| |hi| < √(2 * ↑σ2 * Real.log (1 / δ))) :
    ∀ᵐ e ∂(P.map (E')),
      (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
        {ω | √(2 * ↑σ2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s ω) : ℝ)) ≤
          |empMean IT.action IT.reward a s ω - (κ (e, a))[id]|} ≤
      ENNReal.ofReal (2 * s * δ) := by
  have h_cond_ae : ∀ᵐ e ∂(P.map E'), IsAlgEnvSeq IT.action IT.reward
      (tsAlgorithm hK Q κ) (stationaryEnv (κ.sectR e))
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E' P e) := by
    rw [h.hasLaw_env.map_eq]; exact IsBayesAlgEnvSeq.ae_IsAlgEnvSeq h
  filter_upwards [h_cond_ae] with e h_isAlgEnvSeq
  let ν := κ.sectR e
  have h_subG : ∀ a', HasSubgaussianMGF (fun x ↦ x - (ν a')[id]) σ2 (ν a') := fun a' ↦ by
    simp only [ν, Kernel.sectR_apply]; exact hs a' e
  have h_mean : (ν a)[id] = (κ (e, a))[id] := by simp only [ν, Kernel.sectR_apply]
  rw [← h_mean]
  let P' := condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e
  have h_law := h_isAlgEnvSeq.law_pullCount_sumRewards_unique'
    (ArrayModel.isAlgEnvSeq_arrayMeasure (tsAlgorithm hK Q κ) ν) (n := s)
  let B_low := fun m : ℕ ↦
    {x : ℝ | x / m + √(2 * ↑σ2 * Real.log (1 / δ) / m) ≤ (ν a)[id]}
  let B_high := fun m : ℕ ↦
    {x : ℝ | (ν a)[id] ≤ x / m - √(2 * ↑σ2 * Real.log (1 / δ) / m)}
  have h_stream_bound : ∀ m : ℕ, m ≠ 0 →
      streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ≤
        ENNReal.ofReal (2 * δ) :=
    fun m hm0 ↦ streamMeasure_concentration_bound hσ2 h_subG a hδ hδ1 m hm0
  let badSet := {ω : ℕ → (Fin K) × ℝ |
    √(2 * ↑σ2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s ω) : ℝ)) ≤
      |empMean IT.action IT.reward a s ω - (ν a)[id]|}
  have h_bound_per_m : ∀ m : ℕ, m ≠ 0 → m ≤ s →
      P' {ω | pullCount IT.action a s ω = m ∧
        sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} := by
    intro m hm0 hms
    have hB_meas : MeasurableSet (B_low m ∪ B_high m) :=
      MeasurableSet.union (measurableSet_le (by fun_prop) (by fun_prop))
        (measurableSet_le (by fun_prop) (by fun_prop))
    exact prob_pullCount_eq_and_sumRewards_mem_le h_isAlgEnvSeq hms hB_meas
  have h_bad_subset : badSet ⊆
      ⋃ m ∈ (Finset.range (s + 1)).filter (· ≠ 0),
        {ω | pullCount IT.action a s ω = m ∧
          sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, badSet] at hω
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    set m := pullCount IT.action a s ω with hm_def
    have hms : m ≤ s := pullCount_le (A := IT.action) a s ω
    by_cases hm0 : m = 0
    · exfalso
      have h_empMean_zero : empMean IT.action IT.reward a s ω = 0 := by
        simp only [empMean, ← hm_def, hm0, Nat.cast_zero, div_zero]
      simp only [hm0, Nat.cast_zero, h_empMean_zero, max_eq_left (zero_le_one' ℝ), div_one] at hω
      rw [h_mean, zero_sub, abs_neg] at hω
      linarith [abs_le_max_abs_abs (hm a e).1 (hm a e).2]
    · -- Case: m ≥ 1
      use m
      refine ⟨⟨Nat.lt_succ_of_le hms, hm0⟩, rfl, ?_⟩
      simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq]
      have hmax_eq : (max 1 (m : ℕ) : ℝ) = m := by
        simp only [Nat.one_le_cast, Nat.one_le_iff_ne_zero.mpr hm0, max_eq_right]
      rw [hmax_eq] at hω
      rw [show empMean IT.action IT.reward a s ω =
          sumRewards IT.action IT.reward a s ω / m from by simp only [empMean, hm_def]] at hω
      by_cases h_le : sumRewards IT.action IT.reward a s ω / m ≤ (ν a)[id]
      · left; rw [abs_of_nonpos (sub_nonpos.mpr h_le), neg_sub] at hω; linarith
      · right; rw [abs_of_pos (sub_pos.mpr (not_le.mp h_le))] at hω; linarith
  calc P' badSet
      ≤ P' (⋃ m ∈ (Finset.range (s + 1)).filter (· ≠ 0),
          {ω | pullCount IT.action a s ω = m ∧
            sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m}) :=
        measure_mono h_bad_subset
    _ ≤ ∑ m ∈ (Finset.range (s + 1)).filter (· ≠ 0),
          P' {ω | pullCount IT.action a s ω = m ∧
            sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ (Finset.range (s + 1)).filter (· ≠ 0),
          streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} :=
        Finset.sum_le_sum fun m hm ↦ h_bound_per_m m (Finset.mem_filter.mp hm).2
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))
    _ ≤ ∑ _m ∈ (Finset.range (s + 1)).filter (· ≠ 0), ENNReal.ofReal (2 * δ) :=
        Finset.sum_le_sum fun m hm ↦ h_stream_bound m (Finset.mem_filter.mp hm).2
    _ = ((Finset.range (s + 1)).filter (· ≠ 0)).card • ENNReal.ofReal (2 * δ) := by
        simp only [Finset.sum_const]
    _ = s • ENNReal.ofReal (2 * δ) := by
        congr 1
        have hS_eq : (Finset.range (s + 1)).filter (· ≠ 0) = Finset.Icc 1 s := by
          ext m; simp only [Finset.mem_filter, Finset.mem_range, ne_eq, Finset.mem_Icc]; omega
        rw [hS_eq, Nat.card_Icc, Nat.add_sub_cancel]
    _ = ENNReal.ofReal (2 * s * δ) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast s, ← ENNReal.ofReal_mul (Nat.cast_nonneg s)]
        congr 1; ring

lemma prob_concentration_single_delta [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ Set.Icc lo hi)
    (a : Fin K) (s : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : max |lo| |hi| < √(2 * ↑σ2 * Real.log (1 / δ))) :
    P {ω | √(2 * ↑σ2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|} ≤
      ENNReal.ofReal (2 * s * δ) := by
  let badSet : E → Set (ℕ → (Fin K) × ℝ) := fun e ↦
    {t | √(2 * ↑σ2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s t) : ℝ)) ≤
      |empMean IT.action IT.reward a s t - (κ (e, a))[id]|}
  have h_set_eq : {ω | √(2 * ↑σ2 * Real.log (1 / δ) /
      (max 1 (pullCount A a s ω) : ℝ)) ≤
      |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|} =
      (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
        {p | p.2 ∈ badSet p.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, badSet, IsBayesAlgEnvSeq.actionMean]
    have h1 : pullCount A a s ω = pullCount IT.action a s ((fun ω n => (A n ω, R' n ω)) ω) := by
      unfold pullCount IT.action; rfl
    have h2 : empMean A R' a s ω =
        empMean IT.action IT.reward a s ((fun ω n => (A n ω, R' n ω)) ω) := by
      unfold empMean IT.action IT.reward; rfl
    rw [h1, h2]
  have h_meas_pair :
      Measurable (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) :=
    h.measurable_E.prodMk (measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n))
  have h_disint : P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) =
      P.map (E') ⊗ₘ
        condDistrib ((fun ω n => (A n ω, R' n ω))) E' P :=
    (compProd_map_condDistrib ((measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable)).symm
  have h_cond := prob_concentration_single_delta_cond hK E' A R' Q κ P h hσ2 hs hm a s δ hδ hδ1
    hδ_large
  have h_kernel : Measurable (fun p : E × (ℕ → (Fin K) × ℝ) ↦ (κ (p.1, a))[id]) :=
    stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_fst.prodMk measurable_const)
  have h_meas_set : MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) | p.2 ∈ badSet p.1} := by
    change MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
        √(2 * ↑σ2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s p.2) : ℝ)) ≤
        |empMean IT.action IT.reward a s p.2 - (κ (p.1, a))[id]|}
    exact measurableSet_le (by fun_prop)
      (((measurable_empMean IT.measurable_action IT.measurable_reward a s).comp measurable_snd).sub
        h_kernel).abs
  calc P _ = P ((fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
          {p | p.2 ∈ badSet p.1}) := by rw [h_set_eq]
    _ = (P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)))
          {p | p.2 ∈ badSet p.1} := by
        rw [Measure.map_apply h_meas_pair h_meas_set]
    _ = (P.map (E') ⊗ₘ
          condDistrib ((fun ω n => (A n ω, R' n ω))) E' P)
          {p | p.2 ∈ badSet p.1} := by rw [h_disint]
    _ = ∫⁻ e, (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
          (badSet e) ∂(P.map (E')) := by
        rw [Measure.compProd_apply h_meas_set]; rfl
    _ ≤ ∫⁻ _e, ENNReal.ofReal (2 * s * δ) ∂(P.map (E')) := by
        apply lintegral_mono_ae
        filter_upwards [h_cond] with e h_e; exact h_e
    _ = ENNReal.ofReal (2 * s * δ) := by
        rw [lintegral_const, Measure.map_apply h.measurable_E MeasurableSet.univ]
        simp [measure_univ]

private lemma concentration_cond_bound [Nonempty (Fin K)]
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (e : E) (h_isAlgEnvSeq : IsAlgEnvSeq IT.action IT.reward (tsAlgorithm hK Q κ)
      (stationaryEnv (κ.sectR e))
      (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e))
    (a : Fin K) :
    (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
      (⋃ s ∈ Finset.range n, {ω | pullCount IT.action a s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s ω : ℝ)) ≤
          |empMean IT.action IT.reward a s ω - (κ (e, a))[id]|}) ≤
      ENNReal.ofReal (2 * n * δ) := by
  let ν := κ.sectR e
  let P' := condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e
  have h_subG : ∀ a', HasSubgaussianMGF (fun x ↦ x - (ν a')[id]) σ2 (ν a') := fun a' ↦ by
    simp only [ν, Kernel.sectR_apply]; exact hs a' e
  have h_mean : (ν a)[id] = (κ (e, a))[id] := by simp only [ν, Kernel.sectR_apply]
  let B_low := fun m : ℕ ↦
    {x : ℝ | x / m + √(2 * ↑σ2 * Real.log (1 / δ) / m) ≤ (ν a)[id]}
  let B_high := fun m : ℕ ↦
    {x : ℝ | (ν a)[id] ≤ x / m - √(2 * ↑σ2 * Real.log (1 / δ) / m)}
  have h_stream_bound : ∀ m : ℕ, m ≠ 0 →
      streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ≤
        ENNReal.ofReal (2 * δ) :=
    fun m hm0 ↦ streamMeasure_concentration_bound hσ2 h_subG a hδ hδ1 m hm0
  have hB_meas : ∀ m, MeasurableSet (B_low m ∪ B_high m) := fun m ↦
    MeasurableSet.union (measurableSet_le (by fun_prop) (by fun_prop))
      (measurableSet_le (by fun_prop) (by fun_prop))
  let badSetIT := fun (s : ℕ) ↦ {ω : ℕ → (Fin K) × ℝ |
    pullCount IT.action a s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s ω : ℝ)) ≤
        |empMean IT.action IT.reward a s ω - (κ (e, a))[id]|}
  let S := Finset.Icc 1 (n - 1)
  have hS_card : S.card = n - 1 := by simp only [Nat.card_Icc, S]; omega
  have h_decomp : ⋃ s ∈ Finset.range n, badSetIT s =
      ⋃ m ∈ S, {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
        sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, badSetIT, Set.mem_setOf_eq,
      Finset.mem_Icc, S]
    constructor
    · rintro ⟨s, hs, hbad⟩
      let m := pullCount IT.action a s ω
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hbad.1
      have hm_le : m ≤ n - 1 := by
        have h1 : m ≤ s := pullCount_le (A := IT.action) a s ω
        omega
      refine ⟨m, ⟨hm_pos, hm_le⟩, s, hs, rfl, ?_⟩
      simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq]
      simp only [empMean] at hbad
      rcases le_abs'.mp hbad.2 with h | h <;> [left; right] <;> linarith
    · rintro ⟨m, ⟨hm_pos, hm_le⟩, s, hs, hpc, hB⟩
      refine ⟨s, hs, ?_⟩
      simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq] at hB
      simp only [empMean, hpc]
      refine ⟨Nat.one_le_iff_ne_zero.mp hm_pos, ?_⟩
      rcases hB with h | h
      · exact le_abs.mpr (.inr (by linarith))
      · exact le_abs.mpr (.inl (by linarith))
  rw [h_decomp]
  calc P' (⋃ m ∈ S, {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
          sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m})
      ≤ ∑ m ∈ S, P' {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
          sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} :=
        measure_biUnion_finset_le S _
    _ ≤ ∑ m ∈ S, streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} := by
        apply Finset.sum_le_sum
        intro m hm
        have hm_pos : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1
        have hm_le : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
        have h_contain : {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
            sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} ⊆
            {ω | pullCount IT.action a (n - 1) ω = m ∧
              sumRewards IT.action IT.reward a (n - 1) ω ∈ B_low m ∪ B_high m} ∪
            {ω | pullCount IT.action a (n - 1) ω > m ∧
              ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
                sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} := by
          intro ω ⟨s, hs, hpc, hB⟩
          simp only [Set.mem_union, Set.mem_setOf_eq]
          have hs' : s ≤ n - 1 := Nat.le_sub_one_of_lt hs
          have h_pc_mono := pullCount_mono (A := IT.action) a hs' ω
          by_cases h_eq : pullCount IT.action a (n - 1) ω = m
          · left
            refine ⟨h_eq, ?_⟩
            have h_pc_eq : pullCount IT.action a s ω = pullCount IT.action a (n - 1) ω :=
              hpc.symm ▸ h_eq.symm
            rw [← sumRewards_eq_of_pullCount_eq h_pc_eq]
            exact hB
          · right
            exact ⟨by omega, s, hs, hpc, hB⟩
        calc P' {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
                sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m}
            ≤ P' {ω | ∃ s, s ≤ n - 1 ∧ pullCount IT.action a s ω = m ∧
                sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} := by
              apply measure_mono
              intro ω ⟨s, hs, hpc, hB⟩
              exact ⟨s, Nat.le_sub_one_of_lt hs, hpc, hB⟩
          _ ≤ streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} :=
              prob_exists_pullCount_eq_and_sumRewards_mem_le (n := n - 1)
                h_isAlgEnvSeq (hB_meas m)
    _ ≤ ∑ _m ∈ S, ENNReal.ofReal (2 * δ) :=
        Finset.sum_le_sum fun m hm ↦
          h_stream_bound m (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1)
    _ = (n - 1) • ENNReal.ofReal (2 * δ) := by
        simp only [Finset.sum_const, hS_card]
    _ ≤ ENNReal.ofReal (2 * n * δ) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (n - 1),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg (n - 1))]
        exact ENNReal.ofReal_le_ofReal (by
          nlinarith [(Nat.cast_le (α := ℝ)).mpr (Nat.sub_le n 1), hδ.le])

lemma prob_concentration_fail_delta [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ∃ s < n, ∃ a, pullCount A a s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
        |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|}
      ≤ ENNReal.ofReal (2 * K * n * δ) := by
  let badSet := fun (s : ℕ) (a : Fin K) ↦ {ω : Ω | pullCount A a s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
        |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|}
  have h_set_eq : {ω | ∃ s < n, ∃ a, pullCount A a s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
        |empMean A R' a s ω - IsBayesAlgEnvSeq.actionMean κ E' a ω|} =
      ⋃ s ∈ Finset.range n, ⋃ a : Fin K, badSet s a := by
    ext ω; simp only [Set.mem_setOf_eq, Finset.mem_range, Set.mem_iUnion, badSet, exists_prop]
  rw [h_set_eq]
  have h_reorg : ⋃ s ∈ Finset.range n, ⋃ a : Fin K, badSet s a =
      ⋃ a : Fin K, ⋃ s ∈ Finset.range n, badSet s a := by
    ext ω; simp only [Set.mem_iUnion, Finset.mem_range]; exact
      ⟨fun ⟨s, hs, a, ha⟩ ↦ ⟨a, s, hs, ha⟩, fun ⟨a, s, hs, ha⟩ ↦ ⟨s, hs, a, ha⟩⟩
  rw [h_reorg]
  have h_arm_bound : ∀ a : Fin K, P (⋃ s ∈ Finset.range n, badSet s a) ≤
      ENNReal.ofReal (2 * n * δ) := by
    intro a
    by_cases hn : n = 0
    · simp [hn]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    let badSetIT := fun (s : ℕ) (e : E) ↦ {ω : ℕ → (Fin K) × ℝ |
      pullCount IT.action a s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s ω : ℝ)) ≤
          |empMean IT.action IT.reward a s ω - (κ (e, a))[id]|}
    have h_set_eq : ⋃ s ∈ Finset.range n, badSet s a =
        (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
          {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
      ext ω
      simp only [Set.mem_iUnion, Finset.mem_range, badSet, badSetIT, Set.mem_preimage,
        Set.mem_setOf_eq, IsBayesAlgEnvSeq.actionMean]
      exact Iff.rfl
    rw [h_set_eq]
    have h_meas_pair :
        Measurable (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) :=
      h.measurable_E.prodMk (measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n))
    have h_disint : P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) =
        P.map (E') ⊗ₘ
          condDistrib ((fun ω n => (A n ω, R' n ω))) E' P :=
      (compProd_map_condDistrib ((measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable)).symm
    have h_cond_bound : ∀ᵐ e ∂(P.map (E')),
        (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
          (⋃ s ∈ Finset.range n, badSetIT s e) ≤ ENNReal.ofReal (2 * n * δ) := by
      have h_cond_ae : ∀ᵐ e ∂(P.map E'), IsAlgEnvSeq IT.action IT.reward
          (tsAlgorithm hK Q κ) (stationaryEnv (κ.sectR e))
          (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E' P e) := by
        rw [h.hasLaw_env.map_eq]; exact IsBayesAlgEnvSeq.ae_IsAlgEnvSeq h
      filter_upwards [h_cond_ae] with e h_isAlgEnvSeq
      exact concentration_cond_bound (hK := hK) (E' := E') (A := A) (R' := R')
        (Q := Q) (κ := κ) (P := P) hσ2 hs hn' hδ hδ1 e h_isAlgEnvSeq a
    have h_kernel : Measurable (fun p : E × (ℕ → (Fin K) × ℝ) ↦ (κ (p.1, a))[id]) :=
      stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_fst.prodMk measurable_const)
    have h_meas_set : MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
        p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
      have h_eq : {p : E × (ℕ → (Fin K) × ℝ) | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} =
          ⋃ s ∈ Finset.range n, {p | p.2 ∈ badSetIT s p.1} := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      rw [h_eq]
      exact .biUnion (Finset.range n).countable_toSet fun s _ ↦ by
        simp only [badSetIT]
        change MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
            pullCount IT.action a s p.2 ≠ 0 ∧
              √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s p.2 : ℝ)) ≤
              |empMean IT.action IT.reward a s p.2 - (κ (p.1, a))[id]|}
        exact MeasurableSet.inter
          (((measurable_pullCount IT.measurable_action a s).comp measurable_snd)
            (measurableSet_singleton (0 : ℕ)).compl)
          (measurableSet_le (by fun_prop)
            (((measurable_empMean IT.measurable_action IT.measurable_reward a s).comp
              measurable_snd).sub h_kernel).abs)
    calc P ((fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
          {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1})
        = (P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)))
            {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
          rw [Measure.map_apply h_meas_pair h_meas_set]
      _ = (P.map (E') ⊗ₘ
            condDistrib ((fun ω n => (A n ω, R' n ω))) E' P)
              {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
          rw [h_disint]
      _ = ∫⁻ e, (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
            (⋃ s ∈ Finset.range n, badSetIT s e) ∂(P.map (E')) := by
          rw [Measure.compProd_apply h_meas_set]; rfl
      _ ≤ ∫⁻ _e, ENNReal.ofReal (2 * n * δ) ∂(P.map (E')) := by
          apply lintegral_mono_ae h_cond_bound
      _ = ENNReal.ofReal (2 * n * δ) := by
          rw [lintegral_const, Measure.map_apply h.measurable_E MeasurableSet.univ]
          simp [measure_univ]
  calc P (⋃ a : Fin K, ⋃ s ∈ Finset.range n, badSet s a)
      ≤ ∑ a : Fin K, P (⋃ s ∈ Finset.range n, badSet s a) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : Fin K, ENNReal.ofReal (2 * n * δ) :=
        Finset.sum_le_sum fun a _ ↦ h_arm_bound a
    _ = K • ENNReal.ofReal (2 * n * δ) := by simp [Finset.sum_const]
    _ = ENNReal.ofReal (2 * K * n * δ) := by
        simp only [nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
        congr 1; ring

lemma prob_concentration_bestArm_fail_delta [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ∃ s < n, pullCount A (IsBayesAlgEnvSeq.bestAction κ E' ω) s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) /
        (pullCount A (IsBayesAlgEnvSeq.bestAction κ E' ω) s ω : ℝ)) ≤
        |empMean A R' (IsBayesAlgEnvSeq.bestAction κ E' ω) s ω -
         IsBayesAlgEnvSeq.actionMean κ E' (IsBayesAlgEnvSeq.bestAction κ E' ω) ω|}
      ≤ ENNReal.ofReal (2 * n * δ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  rw [show IsBayesAlgEnvSeq.bestAction κ E' = IsBayesAlgEnvSeq.bestAction κ id ∘ E' from
    rfl]
  let badSetIT := fun (a : Fin K) (s : ℕ) (e : E) ↦ {ω : ℕ → (Fin K) × ℝ |
    pullCount IT.action a s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s ω : ℝ)) ≤
        |empMean IT.action IT.reward a s ω - (κ (e, a))[id]|}
  have h_set_eq : {ω | ∃ s < n, pullCount A ((IsBayesAlgEnvSeq.bestAction κ id ∘ E') ω) s ω ≠ 0 ∧
      √(2 * ↑σ2 * Real.log (1 / δ) /
        (pullCount A ((IsBayesAlgEnvSeq.bestAction κ id ∘ E') ω) s ω : ℝ)) ≤
        |empMean A R' ((IsBayesAlgEnvSeq.bestAction κ id ∘ E') ω) s ω -
         IsBayesAlgEnvSeq.actionMean κ E' ((IsBayesAlgEnvSeq.bestAction κ id ∘ E') ω) ω|} =
      (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
        {p | p.2 ∈ ⋃ s ∈ Finset.range n,
          badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.mem_range, Set.mem_preimage, Set.mem_iUnion,
      badSetIT, IsBayesAlgEnvSeq.actionMean, Function.comp_apply, exists_prop]
    rfl
  rw [h_set_eq]
  have h_meas_pair :
      Measurable (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) :=
    h.measurable_E.prodMk (measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n))
  have h_disint : P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) =
      P.map E' ⊗ₘ condDistrib ((fun ω n => (A n ω, R' n ω))) E' P :=
    (compProd_map_condDistrib ((measurable_pi_lambda _ fun n =>
      (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable)).symm
  have h_cond_bound : ∀ᵐ e ∂(P.map E'), ∀ a : Fin K,
      (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
        (⋃ s ∈ Finset.range n, badSetIT a s e) ≤ ENNReal.ofReal (2 * n * δ) := by
    have h_cond_ae : ∀ᵐ e ∂(P.map E'), IsAlgEnvSeq IT.action IT.reward
        (tsAlgorithm hK Q κ) (stationaryEnv (κ.sectR e))
        (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E' P e) := by
      rw [h.hasLaw_env.map_eq]; exact IsBayesAlgEnvSeq.ae_IsAlgEnvSeq h
    filter_upwards [h_cond_ae] with e h_isAlgEnvSeq
    intro a
    exact concentration_cond_bound (hK := hK) (E' := E') (A := A) (R' := R')
      (Q := Q) (κ := κ) (P := P) hσ2 hs hn' hδ hδ1 e h_isAlgEnvSeq a
  have h_cond_best : ∀ᵐ e ∂(P.map E'),
      (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
        (⋃ s ∈ Finset.range n, badSetIT (IsBayesAlgEnvSeq.bestAction κ id e) s e) ≤
          ENNReal.ofReal (2 * n * δ) := by
    filter_upwards [h_cond_bound] with e he
    exact he (IsBayesAlgEnvSeq.bestAction κ id e)
  have h_kernel : ∀ a, Measurable (fun p : E × (ℕ → (Fin K) × ℝ) ↦ (κ (p.1, a))[id]) :=
    fun a ↦ stronglyMeasurable_id.integral_kernel.measurable.comp
      (measurable_fst.prodMk measurable_const)
  have h_meas_badSetIT : ∀ a s, MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
      p.2 ∈ badSetIT a s p.1} := by
    intro a s
    simp only [badSetIT]
    change MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
        pullCount IT.action a s p.2 ≠ 0 ∧
          √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount IT.action a s p.2 : ℝ)) ≤
          |empMean IT.action IT.reward a s p.2 - (κ (p.1, a))[id]|}
    exact MeasurableSet.inter
      (((measurable_pullCount IT.measurable_action a s).comp measurable_snd)
        (measurableSet_singleton (0 : ℕ)).compl)
      (measurableSet_le (by fun_prop)
        (((measurable_empMean IT.measurable_action IT.measurable_reward a s).comp
          measurable_snd).sub (h_kernel a)).abs)
  have h_meas_set : MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
      p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1} := by
    have h_eq : {p : E × (ℕ → (Fin K) × ℝ) |
        p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1} =
      ⋃ a : Fin K, ((IsBayesAlgEnvSeq.bestAction κ id ∘ Prod.fst) ⁻¹' {a} ∩
        ⋃ s ∈ Finset.range n, {p | p.2 ∈ badSetIT a s p.1}) := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Finset.mem_range]
      constructor
      · intro ⟨s, hs, hm⟩; exact ⟨IsBayesAlgEnvSeq.bestAction κ id p.1, rfl, s, hs, hm⟩
      · rintro ⟨a, ha, s, hs, hm⟩; exact ⟨s, hs, ha ▸ hm⟩
    rw [h_eq]
    exact .iUnion fun a ↦ .inter
      ((IsBayesAlgEnvSeq.measurable_bestAction (κ := κ) measurable_id |>.comp
        measurable_fst) (measurableSet_singleton a))
      (.biUnion (Finset.range n).countable_toSet fun s _ ↦ h_meas_badSetIT a s)
  calc P ((fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)) ⁻¹'
        {p | p.2 ∈ ⋃ s ∈ Finset.range n,
          badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1})
      = (P.map (fun ω ↦ (E' ω, (fun ω n => (A n ω, R' n ω)) ω)))
          {p | p.2 ∈ ⋃ s ∈ Finset.range n,
            badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1} := by
        rw [Measure.map_apply h_meas_pair h_meas_set]
    _ = (P.map E' ⊗ₘ
          condDistrib ((fun ω n => (A n ω, R' n ω))) E' P)
            {p | p.2 ∈ ⋃ s ∈ Finset.range n,
              badSetIT (IsBayesAlgEnvSeq.bestAction κ id p.1) s p.1} := by
        rw [h_disint]
    _ = ∫⁻ e, (condDistrib ((fun ω n => (A n ω, R' n ω))) E' P e)
          (⋃ s ∈ Finset.range n,
            badSetIT (IsBayesAlgEnvSeq.bestAction κ id e) s e) ∂(P.map E') := by
        rw [Measure.compProd_apply h_meas_set]; rfl
    _ ≤ ∫⁻ _e, ENNReal.ofReal (2 * n * δ) ∂(P.map E') := by
        apply lintegral_mono_ae h_cond_best
    _ = ENNReal.ofReal (2 * n * δ) := by
        rw [lintegral_const, Measure.map_apply h.measurable_E MeasurableSet.univ]
        simp [measure_univ]

lemma bayesRegret_le_of_delta [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ (Set.Icc lo hi))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    P[IsBayesAlgEnvSeq.regret κ E' A n]
      ≤ (hi - lo) * ↑K + 2 * (↑K + 1) * (hi - lo) * n ^ 2 * δ +
        2 * √(8 * ↑σ2 * Real.log (1 / δ)) * √(↑K * ↑n) := by
  have ⟨h1, h2⟩ := hm (Classical.arbitrary _) (Classical.arbitrary _)
  have hlo : lo ≤ hi := h1.trans h2
  let bestArm := IsBayesAlgEnvSeq.bestAction κ E'
  let armMean := IsBayesAlgEnvSeq.actionMean κ E'
  let ucb := ucbIndex A R' (↑σ2) lo hi δ
  set Eδ : Set Ω := {ω | ∀ s < n, ∀ a, pullCount A a s ω ≠ 0 →
    |empMean A R' a s ω - armMean a ω|
      < √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ))}
  set Fδ : Set Ω := {ω | ∀ s < n, pullCount A (bestArm ω) s ω ≠ 0 →
    |empMean A R' (bestArm ω) s ω - armMean (bestArm ω) ω|
      < √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A (bestArm ω) s ω : ℝ))}
  have hm_ucb : ∀ a t, Measurable (ucbIndex A R' (↑σ2) lo hi δ a t) :=
    fun a t ↦ measurable_ucbIndex hK E' A R' Q κ P h (↑σ2) lo hi δ a t
  have hm_arm : ∀ a, Measurable (IsBayesAlgEnvSeq.actionMean κ E' a) :=
    fun a ↦ IsBayesAlgEnvSeq.measurable_actionMean (a := a) h.measurable_E
  have hm_best : Measurable (IsBayesAlgEnvSeq.bestAction κ E') :=
    IsBayesAlgEnvSeq.measurable_bestAction h.measurable_E
  have h_first_bound : ∀ ω,
      |∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)|
        ≤ n * (hi - lo) := fun ω ↦
    calc |∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)|
        ≤ ∑ s ∈ range n, |armMean (bestArm ω) ω - ucb (bestArm ω) s ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (hi - lo) := Finset.sum_le_sum fun s _ ↦
          abs_sub_le_of_mem_Icc (hm _ _) (ucbIndex_mem_Icc A R' (↑σ2) lo hi δ hlo _ _ _)
      _ = ↑n * (hi - lo) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_second_bound : ∀ ω,
      |∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)|
        ≤ n * (hi - lo) := fun ω ↦
    calc |∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)|
        ≤ ∑ s ∈ range n, |ucb (A s ω) s ω - armMean (A s ω) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (hi - lo) := Finset.sum_le_sum fun s _ ↦
          abs_sub_le_of_mem_Icc (ucbIndex_mem_Icc A R' (↑σ2) lo hi δ hlo _ _ _) (hm _ _)
      _ = ↑n * (hi - lo) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_int_sum1 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)) P := by
    apply Integrable.of_bound (C := ↑n * (hi - lo))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin hm_arm hm_best).sub
          (measurable_apply_fin (fun a ↦ hm_ucb a s) hm_best)).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_first_bound ω
  have h_int_sum2 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (ucb (A s ω) s ω - armMean (A s ω) ω)) P := by
    apply Integrable.of_bound (C := ↑n * (hi - lo))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin (fun a ↦ hm_ucb a s) (h.measurable_A s)).sub
          (measurable_apply_fin hm_arm (h.measurable_A s))).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_second_bound ω
  have h_swap :
      P[IsBayesAlgEnvSeq.regret κ E' A n] =
      P[fun ω ↦ ∑ s ∈ range n,
        (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)] +
      P[fun ω ↦ ∑ s ∈ range n,
        (ucb (A s ω) s ω - armMean (A s ω) ω)] := by
    have h_regret_eq : P[IsBayesAlgEnvSeq.regret κ E' A n] =
        ∑ s ∈ range n, P[fun ω ↦ armMean (bestArm ω) ω - armMean (A s ω) ω] := by
      rw [bayesRegret_eq_sum_integral_gap (h := h)
        (hm := fun a e ↦ abs_le_max_abs_abs (hm a e).1 (hm a e).2) (t := n)]
      congr 1 with s
      exact integral_congr_ae (ae_of_all _ fun ω ↦ gap_eq_armMean_sub E' A κ hm s ω)
    have h_int_ucb : ∀ s {f : Ω → Fin K}, Measurable f →
        Integrable (fun ω ↦ ucb (f ω) s ω) P := fun s {_} hf ↦
      ⟨(measurable_apply_fin (fun a ↦ hm_ucb a s) hf).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (ae_of_all _ fun ω ↦
          norm_ucbIndex_le A R' (↑σ2) lo hi δ hlo _ _ _)⟩
    have h_int_ucb_sub : ∀ s, Integrable (fun ω ↦ ucb (A s ω) s ω - ucb (bestArm ω) s ω) P :=
      fun s ↦ (h_int_ucb s (h.measurable_A s)).sub (h_int_ucb s hm_best)
    have h_ucb_zero : ∀ a (ω : Ω), ucbIndex A R' (↑σ2) lo hi δ a 0 ω = hi := by
      intro a ω; unfold ucbIndex; simp [pullCount_zero]
    have h_ucb_swap : ∀ s, ∫ ω, (ucb (A s ω) s ω - ucb (bestArm ω) s ω) ∂P = 0 := by
      intro s
      cases s with
      | zero =>
        have : ∀ ω, ucb (A 0 ω) 0 ω - ucb (bestArm ω) 0 ω = 0 := fun ω ↦ by
          change ucbIndex A R' (↑σ2) lo hi δ _ 0 ω - ucbIndex A R' (↑σ2) lo hi δ _ 0 ω = 0
          simp [h_ucb_zero]
        exact (integral_congr_ae (ae_of_all _ this)).trans (integral_zero _ _)
      | succ t =>
        have hts := ts_identity hK E' A R' Q κ P h t
        have h_map_eq : P.map (fun ω ↦ (IsAlgEnvSeq.hist A R' t ω, A (t + 1) ω)) =
            P.map (fun ω ↦ (IsAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestAction κ E' ω)) := by
          rw [← compProd_map_condDistrib (hY := (h.measurable_A (t + 1)).aemeasurable),
              ← compProd_map_condDistrib (hY := hm_best.aemeasurable)]
          exact Measure.compProd_congr hts
        have h_int_eq : ∀ (f : (Iic t → Fin K × ℝ) × Fin K → ℝ), Measurable f →
            ∫ ω, f (IsAlgEnvSeq.hist A R' t ω, A (t + 1) ω) ∂P =
            ∫ ω, f (IsAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestAction κ E' ω) ∂P := by
          intro f hf
          have hm_hist := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t
          rw [← integral_map
                (hm_hist.prodMk (h.measurable_A (t + 1))).aemeasurable
                hf.aestronglyMeasurable,
              ← integral_map
                (hm_hist.prodMk hm_best).aemeasurable
                hf.aestronglyMeasurable,
              h_map_eq]
        set g : (Iic t → Fin K × ℝ) × Fin K → ℝ :=
          fun p ↦ if pullCount' t p.1 p.2 = 0 then hi
            else max lo (min hi (empMean' t p.1 p.2 +
              √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount' t p.1 p.2 : ℝ))))
        have h_hist_eq : ∀ ω : Ω, (fun (i : Iic t) ↦ (A (↑i) ω, R' (↑i) ω)) =
            IsAlgEnvSeq.hist A R' t ω := fun ω ↦ rfl
        have hg_eq : ∀ a (ω : Ω), ucbIndex A R' (↑σ2) lo hi δ a (t + 1) ω =
            g (IsAlgEnvSeq.hist A R' t ω, a) := by
          intro a ω
          simp only [g, ucbIndex]
          rw [empMean_add_one_eq_empMean' (A := A) (R' := R'),
              pullCount_add_one_eq_pullCount' (A := A) (R' := R'),
              h_hist_eq]
        have hg_meas : Measurable g := by
          apply Measurable.ite
          · have : MeasurableSet {p : (Iic t → Fin K × ℝ) × Fin K |
                (pullCount' t p.1 p.2 : ℝ) = (0 : ℝ)} :=
              measurableSet_eq_fun
                (measurable_apply_fin
                  (fun a ↦ measurable_from_top.comp
                    ((measurable_pullCount' t a).comp measurable_fst))
                  measurable_snd)
                measurable_const
            simp only [Nat.cast_eq_zero] at this; exact this
          · exact measurable_const
          · apply Measurable.max measurable_const
            apply Measurable.min measurable_const
            apply Measurable.add
            · exact measurable_apply_fin (fun a ↦ (measurable_empMean' t a).comp measurable_fst)
                measurable_snd
            · apply Measurable.sqrt
              apply Measurable.div measurable_const
              exact measurable_apply_fin
                (fun a ↦ measurable_from_top.comp ((measurable_pullCount' t a).comp measurable_fst))
                measurable_snd
        rw [show (fun ω ↦ ucb (A (t + 1) ω) (t + 1) ω -
            ucb (bestArm ω) (t + 1) ω) =
            fun ω ↦ (fun ω ↦ ucb (A (t + 1) ω) (t + 1) ω) ω -
              (fun ω ↦ ucb (bestArm ω) (t + 1) ω) ω from rfl,
          integral_sub (h_int_ucb (t + 1) (h.measurable_A (t + 1)))
            (h_int_ucb (t + 1) hm_best),
          funext fun ω ↦ hg_eq _ _, funext fun ω ↦ hg_eq _ _,
          h_int_eq g hg_meas, sub_self]
    have h_ucb_sum_zero : ∫ ω, ∑ s ∈ range n,
        (ucb (A s ω) s ω - ucb (bestArm ω) s ω) ∂P = 0 := by
      rw [integral_finset_sum _ (fun s _ ↦ h_int_ucb_sub s)]
      exact Finset.sum_eq_zero fun s _ ↦ h_ucb_swap s
    rw [h_regret_eq]
    have h_pw : ∀ ω, (∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)) +
        (∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)) =
        (∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω)) +
        (∑ s ∈ range n, (ucb (A s ω) s ω - ucb (bestArm ω) s ω)) := by
      intro ω
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intros; ring
    have h_int_ucb_swap : Integrable
        (fun ω ↦ ∑ s ∈ range n, (ucb (A s ω) s ω - ucb (bestArm ω) s ω)) P :=
      integrable_finset_sum _ fun s _ ↦ h_int_ucb_sub s
    have h_int_gap_s : ∀ s ∈ range n,
        Integrable (fun ω ↦ armMean (bestArm ω) ω - armMean (A s ω) ω) P := by
      intro s _
      refine Integrable.of_bound
        ((measurable_apply_fin hm_arm hm_best).sub
          (measurable_apply_fin hm_arm (h.measurable_A s))).aestronglyMeasurable
        (hi - lo) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      exact abs_sub_le_of_mem_Icc (hm _ _) (hm _ _)
    have h_int_gap : Integrable
        (fun ω ↦ ∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω)) P :=
      integrable_finset_sum _ h_int_gap_s
    calc ∑ s ∈ range n, ∫ (x : Ω), (fun ω ↦ armMean (bestArm ω) ω - armMean (A s ω) ω) x ∂P
        = ∫ ω, ∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω) ∂P :=
          (integral_finset_sum _ h_int_gap_s).symm
      _ = ∫ ω, ((∑ s ∈ range n, (armMean (bestArm ω) ω - armMean (A s ω) ω)) +
            (∑ s ∈ range n, (ucb (A s ω) s ω - ucb (bestArm ω) s ω))) ∂P := by
          rw [integral_add h_int_gap h_int_ucb_swap, h_ucb_sum_zero, add_zero]
      _ = ∫ ω, ((∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)) +
            (∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω))) ∂P := by
          congr 1; ext ω; linarith [h_pw ω]
      _ = _ := integral_add h_int_sum1 h_int_sum2
  have h_first_Fδ : ∀ ω ∈ Fδ,
      ∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)
        ≤ 0 := by
    intro ω hω
    apply Finset.sum_nonpos
    intro s hs
    linarith [armMean_le_ucbIndex E' A R' κ hm (↑σ2) δ
      (bestArm ω) s ω (hω s (mem_range.mp hs))]
  have h_second_Eδ : ∀ ω ∈ Eδ,
      ∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)
        ≤ (hi - lo) * ↑K + 2 * √(8 * ↑σ2 * Real.log (1 / δ)) * √(↑K * ↑n) := by
    intro ω hω
    exact sum_ucbIndex_sub_armMean_le E' A R' κ hm hlo (↑σ2) δ n ω hω
  have h_prob : P Eδᶜ ≤ ENNReal.ofReal (2 * K * n * δ) := by
    have : Eδᶜ = {ω | ∃ s < n, ∃ a, pullCount A a s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A a s ω : ℝ)) ≤
        |empMean A R' a s ω - armMean a ω|} := by
      ext ω; simp only [Eδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push_neg; rfl
    rw [this]
    exact prob_concentration_fail_delta (hK := hK) (E' := E') (A := A) (R' := R')
      (Q := Q) (κ := κ) (P := P) h hσ2 hs n δ hδ hδ1
  have hm_emp : ∀ a s, Measurable (fun ω ↦ empMean A R' a s ω) :=
    fun a s ↦ measurable_empMean (fun n ↦ h.measurable_A n) (fun n ↦ h.measurable_R n) a s
  have hm_pc : ∀ a s, Measurable (fun ω ↦ (pullCount A a s ω : ℝ)) :=
    fun a s ↦ measurable_from_top.comp (measurable_pullCount (fun n ↦ h.measurable_A n) a s)
  have h_arm_meas : ∀ s a, MeasurableSet {ω : Ω | pullCount A a s ω ≠ 0 →
      |empMean A R' a s ω - armMean a ω|
        < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} := by
    intro s a
    have : {ω : Ω | pullCount A a s ω ≠ 0 →
        |empMean A R' a s ω - armMean a ω|
          < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} =
        {ω | (pullCount A a s ω : ℝ) = 0} ∪ {ω |
          |empMean A R' a s ω - armMean a ω|
            < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, Nat.cast_eq_zero]; tauto
    rw [this]
    exact MeasurableSet.union (hm_pc a s (measurableSet_singleton (0 : ℝ)))
      (measurableSet_lt
        ((hm_emp a s).sub
          (IsBayesAlgEnvSeq.measurable_actionMean (a := a) h.measurable_E)).abs
        ((measurable_const.div (hm_pc a s)).sqrt))
  have hEδ_meas : MeasurableSet Eδ := by
    simp only [Eδ, Set.setOf_forall]
    exact .iInter fun s ↦ .iInter fun _ ↦ .iInter fun a ↦ h_arm_meas s a
  have hFδ_meas : MeasurableSet Fδ := by
    simp only [Fδ, Set.setOf_forall]
    apply MeasurableSet.iInter; intro s
    apply MeasurableSet.iInter; intro _
    have : {ω : Ω | pullCount A (bestArm ω) s ω ≠ 0 →
        |empMean A R' (bestArm ω) s ω - armMean (bestArm ω) ω|
          < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A (bestArm ω) s ω))} =
      ⋃ a : Fin K, (bestArm ⁻¹' {a}) ∩ {ω | pullCount A a s ω ≠ 0 →
          |empMean A R' a s ω - armMean a ω|
            < √(2 * ↑σ2 * Real.log (1 / δ) / ↑(pullCount A a s ω))} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · exact fun h => ⟨_, rfl, h⟩
      · rintro ⟨_, rfl, h⟩; exact h
    rw [this]
    exact .iUnion fun a => .inter (hm_best (measurableSet_singleton a)) (h_arm_meas s a)
  have h_prob_F : P Fδᶜ ≤ ENNReal.ofReal (2 * ↑n * δ) := by
    have : Fδᶜ = {ω | ∃ s < n, pullCount A (bestArm ω) s ω ≠ 0 ∧
        √(2 * ↑σ2 * Real.log (1 / δ) / (pullCount A (bestArm ω) s ω : ℝ)) ≤
          |empMean A R' (bestArm ω) s ω - armMean (bestArm ω) ω|} := by
      ext ω; simp only [Fδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push_neg; rfl
    rw [this]
    exact prob_concentration_bestArm_fail_delta (hK := hK) (E' := E') (A := A) (R' := R')
      (Q := Q) (κ := κ) (P := P) h hσ2 hs n δ hδ hδ1
  rw [h_swap]
  set f1 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)
  set f2 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (ucb (A s ω) s ω - armMean (A s ω) ω)
  set B := (hi - lo) * ↑K + 2 * √(8 * ↑σ2 * Real.log (1 / δ)) * √(↑K * ↑n)
  have h1g : ∫ ω in Fδ, f1 ω ∂P ≤ 0 :=
    setIntegral_nonpos hFδ_meas fun ω hω ↦ h_first_Fδ ω hω
  have h1b : ∫ ω in Fδᶜ, f1 ω ∂P ≤ ↑n * (hi - lo) * P.real Fδᶜ := by
    have := setIntegral_mono_on (hf := h_int_sum1.integrableOn) (hg := integrableOn_const)
      hFδ_meas.compl fun ω _ ↦ (abs_le.mp (h_first_bound ω)).2
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have h2g : ∫ ω in Eδ, f2 ω ∂P ≤ B := by
    have hB : 0 ≤ B := add_nonneg (mul_nonneg (sub_nonneg.mpr hlo) (Nat.cast_nonneg K))
      (by positivity)
    have := setIntegral_mono_on (hf := h_int_sum2.integrableOn)
      (hg := integrableOn_const) hEδ_meas
      fun ω hω ↦ h_second_Eδ ω hω
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact le_trans this (mul_le_of_le_one_right hB measureReal_le_one)
  have h2b : ∫ ω in Eδᶜ, f2 ω ∂P ≤ ↑n * (hi - lo) * P.real Eδᶜ := by
    have := setIntegral_mono_on (hf := h_int_sum2.integrableOn) (hg := integrableOn_const)
      hEδ_meas.compl fun ω _ ↦ (abs_le.mp (h_second_bound ω)).2
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hPF : P.real Fδᶜ ≤ 2 * ↑n * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h_prob_F
  have hPE : P.real Eδᶜ ≤ 2 * ↑K * ↑n * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h_prob
  rw [(integral_add_compl hFδ_meas h_int_sum1).symm,
    (integral_add_compl hEδ_meas h_int_sum2).symm]
  nlinarith [mul_le_mul_of_nonneg_left hPF
      (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hlo)),
    mul_le_mul_of_nonneg_left hPE
      (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hlo)),
    measureReal_nonneg (μ := P) (s := Fδᶜ),
    measureReal_nonneg (μ := P) (s := Eδᶜ)]

lemma TS.bayesRegret_le [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E' A R' P)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    {lo hi : ℝ} (hm : ∀ a e, (κ (e, a))[id] ∈ (Set.Icc lo hi)) (t : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E' A t]
      ≤ (3 * K + 2) * (hi - lo) + 8 * √(σ2 * K * t * Real.log t) := by
  have ⟨h1, h2⟩ := hm (Classical.arbitrary _) (Classical.arbitrary _)
  have hlo : lo ≤ hi := h1.trans h2
  by_cases ht : t = 0
  · simp [ht, IsBayesAlgEnvSeq.regret, Bandits.regret]
    nlinarith [sub_nonneg.mpr hlo, show (0 : ℝ) < K from Nat.cast_pos.mpr hK,
      Real.sqrt_nonneg (↑σ2 * ↑K * (0 : ℝ) * Real.log (0 : ℝ))]
  by_cases ht1_eq : t = 1
  · subst ht1_eq
    simp only [Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
    calc P[IsBayesAlgEnvSeq.regret κ E' A 1]
        ≤ hi - lo := by
          unfold IsBayesAlgEnvSeq.regret Bandits.regret
          simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, one_mul,
            Kernel.sectR_apply]
          refine (integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sub_nonneg.mpr
              (le_ciSup ⟨hi, by rintro _ ⟨a, rfl⟩; exact (hm a _).2⟩ _))
            (integrable_const (hi - lo)) (ae_of_all _ fun ω ↦ by
              linarith [ciSup_le fun a ↦ (hm a (E' ω)).2,
                (hm (A 0 ω) (E' ω)).1])).trans ?_
          simp
      _ ≤ (3 * ↑K + 2) * (hi - lo) := by
          nlinarith [show (1 : ℝ) ≤ K from Nat.one_le_cast.mpr (Nat.one_le_of_lt hK),
            sub_nonneg.mpr hlo]
  -- For t ≥ 2, we have δ = 1/t² < 1
  · have ht2 : 2 ≤ t := by omega
    have htpos : (0 : ℝ) < t := by positivity
    have _ht1 : (1 : ℝ) ≤ t := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero ht)
    have hδ : (0 : ℝ) < 1 / (t : ℝ) ^ 2 := by positivity
    have hδ1 : 1 / (t : ℝ) ^ 2 < 1 := by
      rw [div_lt_one (pow_pos htpos 2)]
      have ht2_real : (2 : ℝ) ≤ t := Nat.ofNat_le_cast.mpr ht2
      calc (1 : ℝ) < 2 ^ 2 := by norm_num
        _ ≤ (t : ℝ) ^ 2 := by gcongr
    -- First term: (hi-lo)*K + 2*(K+1)*(hi-lo)*t²*(1/t²) = (3K+2)*(hi-lo)
    have h_first : (hi - lo) * ↑K + 2 * (↑K + 1) * (hi - lo) * ↑t ^ 2 * (1 / (↑t) ^ 2)
        = (3 * ↑K + 2) * (hi - lo) := by
      field_simp; ring
    -- Second term simplification: log(1/(1/t²)) = log(t²) = 2 log(t)
    have h_log : Real.log (1 / (1 / (↑t : ℝ) ^ 2)) = 2 * Real.log ↑t := by
      rw [one_div_one_div, Real.log_pow]; norm_cast
    calc P[IsBayesAlgEnvSeq.regret κ E' A t]
        ≤ (hi - lo) * ↑K + 2 * (↑K + 1) * (hi - lo) * ↑t ^ 2 * (1 / (↑t) ^ 2)
          + 2 * √(8 * ↑σ2 * Real.log (1 / (1 / (↑t) ^ 2))) * √(↑K * ↑t) :=
          bayesRegret_le_of_delta (hK := hK) (E' := E') (A := A) (R' := R') (Q := Q)
            (κ := κ) (P := P) h hσ2 hs hm t (1 / (↑t) ^ 2) hδ hδ1
      _ = (3 * ↑K + 2) * (hi - lo) + 8 * (√(↑σ2 * Real.log ↑t) * √(↑K * ↑t)) := by
          rw [h_first, h_log,
            show (8 : ℝ) * ↑σ2 * (2 * Real.log ↑t) = 4 ^ 2 * (↑σ2 * Real.log ↑t) by ring,
            Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          ring
      _ = (3 * ↑K + 2) * (hi - lo) + 8 * √(↑σ2 * ↑K * ↑t * Real.log ↑t) := by
          rw [← Real.sqrt_mul (mul_nonneg (NNReal.coe_nonneg σ2)
            (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero ht))))]
          congr 1; congr 1; congr 1; ring

end Regret

end Bandits
