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

open scoped ENNReal

namespace Bandits

namespace TS

variable {K : ℕ} (hK : 0 < K)
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]

/-- The distribution over actions for every given history for TS. -/
noncomputable
def policy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.posteriorBestArm Q κ (uniformAlgorithm hK) n
deriving IsMarkovKernel

/-- The initial distribution over actions for TS. -/
noncomputable
def initialPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.priorBestArm Q κ (uniformAlgorithm hK)

instance : IsProbabilityMeasure (initialPolicy hK Q κ) := by
  unfold initialPolicy
  infer_instance

end TS

variable {K : ℕ}
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

/-- The Thompson Sampling (TS) algorithm: actions are chosen according to the probability that they
are optimal given prior knowledge represented by a prior distribution `Q` and a data generation
model represented by a kernel `κ`. -/
noncomputable
def tsAlgorithm (hK : 0 < K) (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ] : Algorithm (Fin K) ℝ where
  policy := TS.policy hK Q κ
  p0 := TS.initialPolicy hK Q κ

section Regret

variable (hK : 0 < K)
variable {Ω : Type*} [MeasurableSpace Ω]
variable (A : ℕ → Ω → (Fin K)) (R' : ℕ → Ω → E × ℝ)
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]
variable (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable
def ucbIndex (A : ℕ → Ω → Fin K) (R' : ℕ → Ω → E × ℝ) (δ : ℝ)
    (a : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  max 0 (min 1
    (empMean A (IsBayesAlgEnvSeq.reward R') a t ω
      + √(2 * Real.log (1 / δ) / (max 1 (pullCount A a t ω) : ℝ))))

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma ucbIndex_nonneg (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω) : 0 ≤ ucbIndex A R' δ a t ω :=
  le_max_left 0 _

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma ucbIndex_le_one (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω) : ucbIndex A R' δ a t ω ≤ 1 :=
  max_le (by norm_num) (min_le_left 1 _)

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma ucbIndex_mem_Icc (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω) :
    ucbIndex A R' δ a t ω ∈ Set.Icc 0 1 :=
  ⟨ucbIndex_nonneg A R' δ a t ω, ucbIndex_le_one A R' δ a t ω⟩

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma norm_ucbIndex_le_one (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω) :
    ‖ucbIndex A R' δ a t ω‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (ucbIndex_nonneg A R' δ a t ω)]
  exact ucbIndex_le_one A R' δ a t ω

omit mE [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] in
lemma abs_sub_le_one_of_mem_Icc {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |x - y| ≤ 1 := by
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
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (δ : ℝ) (a : Fin K) (t : ℕ) :
    Measurable (ucbIndex A R' δ a t) := by
  unfold ucbIndex
  apply Measurable.max measurable_const
  apply Measurable.min measurable_const
  apply Measurable.add
  · exact measurable_empMean (fun n ↦ h.measurable_A n)
      (fun n ↦ h.measurable_reward n) a t
  · have hpc : Measurable (fun ω ↦ (pullCount A a t ω : ℝ)) :=
      measurable_from_top.comp (measurable_pullCount (fun n ↦ h.measurable_A n) a t)
    exact (measurable_const.div (measurable_const.max hpc)).sqrt

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma armMean_le_ucbIndex (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1))
    (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω)
    (hconc :
      |empMean A (IsBayesAlgEnvSeq.reward R') a t ω - IsBayesAlgEnvSeq.armMean κ R' a ω|
        < √(2 * Real.log (1 / δ) / (max 1 (pullCount A a t ω) : ℝ))) :
    IsBayesAlgEnvSeq.armMean κ R' a ω ≤ ucbIndex A R' δ a t ω := by
  unfold ucbIndex
  have hmean := hm a (IsBayesAlgEnvSeq.env R' ω)
  simp only [IsBayesAlgEnvSeq.armMean] at hmean hconc ⊢
  have habs := abs_sub_lt_iff.mp hconc
  refine le_max_of_le_right (le_min hmean.2 ?_)
  linarith [habs.2]

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma ucbIndex_sub_armMean_le (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1))
    (δ : ℝ) (a : Fin K) (t : ℕ) (ω : Ω)
    (hconc :
      |empMean A (IsBayesAlgEnvSeq.reward R') a t ω - IsBayesAlgEnvSeq.armMean κ R' a ω|
        < √(2 * Real.log (1 / δ) / (max 1 (pullCount A a t ω) : ℝ))) :
    ucbIndex A R' δ a t ω - IsBayesAlgEnvSeq.armMean κ R' a ω
      ≤ 2 * √(2 * Real.log (1 / δ) / (max 1 (pullCount A a t ω) : ℝ)) := by
  unfold ucbIndex
  simp only [IsBayesAlgEnvSeq.armMean] at hconc ⊢
  set w := √(2 * Real.log (1 / δ) / max 1 ↑(pullCount A a t ω))
  set emp := empMean A (IsBayesAlgEnvSeq.reward R') a t ω
  have habs := abs_sub_lt_iff.mp hconc
  have hmean := hm a (IsBayesAlgEnvSeq.env R' ω)
  have h1 : max 0 (min 1 (emp + w)) ≤ emp + w :=
    max_le_iff.mpr ⟨by linarith [hmean.1, habs.2], min_le_right _ _⟩
  linarith [habs.2]

lemma ts_identity [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P) (t : ℕ) :
    condDistrib (A (t + 1)) (IsBayesAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsBayesAlgEnvSeq.hist A R' t)]
    condDistrib (IsBayesAlgEnvSeq.bestArm κ R') (IsBayesAlgEnvSeq.hist A R' t) P :=
  (h.hasCondDistrib_action' t).condDistrib_eq.trans
    (posteriorBestArm_eq_uniform Q κ h hK t).symm

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma le_armMean_bestArm [Nonempty (Fin K)] (ω : Ω) (i : Fin K) :
    IsBayesAlgEnvSeq.armMean κ R' i ω ≤
    IsBayesAlgEnvSeq.armMean κ R' (IsBayesAlgEnvSeq.bestArm κ R' ω) ω := by
  have := isMaxOn_measurableArgmax (fun ω a ↦ IsBayesAlgEnvSeq.armMean κ R' a ω) ω i
  simp only [IsBayesAlgEnvSeq.bestArm]; convert this

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma iSup_armMean_eq_bestArm [Nonempty (Fin K)] (hm : ∀ a e, (κ (a, e))[id] ∈ Set.Icc 0 1)
    (ω : Ω) : ⨆ i, IsBayesAlgEnvSeq.armMean κ R' i ω =
    IsBayesAlgEnvSeq.armMean κ R' (IsBayesAlgEnvSeq.bestArm κ R' ω) ω :=
  le_antisymm (ciSup_le (le_armMean_bestArm R' κ ω))
    (le_ciSup (f := fun i ↦ IsBayesAlgEnvSeq.armMean κ R' i ω)
      ⟨1, by rintro _ ⟨i, rfl⟩; exact (hm i _).2⟩ _)

omit [StandardBorelSpace E] [Nonempty E] [MeasurableSpace Ω] [IsMarkovKernel κ] in
lemma gap_eq_armMean_sub [Nonempty (Fin K)] (hm : ∀ a e, (κ (a, e))[id] ∈ Set.Icc 0 1)
    (s : ℕ) (ω : Ω) : gap (κ.comap (·, IsBayesAlgEnvSeq.env R' ω) (by fun_prop)) (A s ω) =
    IsBayesAlgEnvSeq.armMean κ R' (IsBayesAlgEnvSeq.bestArm κ R' ω) ω -
    IsBayesAlgEnvSeq.armMean κ R' (A s ω) ω := by
  simp only [gap, Kernel.comap_apply]
  exact congr_arg (· - _) (iSup_armMean_eq_bestArm R' κ hm ω)

lemma bayesRegret_eq_sum_integral_gap [Nonempty (Fin K)]
    {alg : Algorithm (Fin K) ℝ}
    (h : IsBayesAlgEnvSeq Q κ A R' alg P)
    {C : ℝ} (hm : ∀ a e, |(κ (a, e))[id]| ≤ C) (t : ℕ) :
    IsBayesAlgEnvSeq.bayesRegret κ A R' P t =
    ∑ s ∈ range t, P[fun ω ↦ gap (κ.comap (·, IsBayesAlgEnvSeq.env R' ω) (by fun_prop))
      (A s ω)] := by
  simp only [IsBayesAlgEnvSeq.bayesRegret, IsBayesAlgEnvSeq.regret, regret_eq_sum_gap]
  refine integral_finset_sum _ (fun s _ => ?_)
  have hmeas : Measurable (fun ω ↦ gap (κ.comap (·, IsBayesAlgEnvSeq.env R' ω) (by fun_prop))
      (A s ω)) :=
    (Measurable.iSup h.measurable_armMean).sub
      (stronglyMeasurable_id.integral_kernel.measurable.comp (h.measurable_action_env s))
  refine ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 2 * C)
    (Filter.Eventually.of_forall fun ω => ?_)⟩
  simp only [Real.norm_eq_abs, gap, Kernel.comap_apply]
  set e := IsBayesAlgEnvSeq.env R' ω
  have hbdd : BddAbove (Set.range fun i => (κ (i, e))[id]) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; exact le_of_abs_le (hm i e)⟩
  rw [abs_of_nonneg (sub_nonneg.mpr (le_ciSup hbdd _))]
  have h1 : (⨆ i, (κ (i, e))[id]) ≤ C := ciSup_le fun i => le_of_abs_le (hm i e)
  have h2 : -C ≤ (κ (A s ω, e))[id] := neg_le_of_abs_le (hm (A s ω) e)
  linarith

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
lemma sum_ucbIndex_sub_armMean_le (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1))
    (δ : ℝ) (n : ℕ) (ω : Ω)
    (hconc : ∀ s < n, ∀ a,
      |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|
        < √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ))) :
    ∑ s ∈ range n, (ucbIndex A R' δ (A s ω) s ω - IsBayesAlgEnvSeq.armMean κ R' (A s ω) ω)
      ≤ 2 * √(8 * Real.log (1 / δ)) * √(↑K * ↑n) := by
  have hterm : ∀ s ∈ range n,
      ucbIndex A R' δ (A s ω) s ω - IsBayesAlgEnvSeq.armMean κ R' (A s ω) ω
        ≤ 2 * √(2 * Real.log (1 / δ) / (max 1 (pullCount A (A s ω) s ω) : ℝ)) :=
    fun s hs => ucbIndex_sub_armMean_le A R' κ hm δ (A s ω) s ω (hconc s (mem_range.mp hs) _)
  calc ∑ s ∈ range n,
        (ucbIndex A R' δ (A s ω) s ω - IsBayesAlgEnvSeq.armMean κ R' (A s ω) ω)
      ≤ ∑ s ∈ range n,
        2 * √(2 * Real.log (1 / δ) / (max 1 (pullCount A (A s ω) s ω) : ℝ)) :=
        sum_le_sum hterm
    _ ≤ 2 * √(8 * Real.log (1 / δ)) * √(↑K * ↑n) := by
        set c := Real.log (1 / δ)
        by_cases hc : 0 ≤ 2 * c
        · open Real in
          calc ∑ s ∈ range n, 2 * √(2 * c / max 1 ↑(pullCount A (A s ω) s ω))
              = ∑ s ∈ range n, √(8 * c) *
                  (1 / √(↑(max 1 (pullCount A (A s ω) s ω)) : ℝ)) :=
                sum_congr rfl fun s _ => by
                  rw [show (8 : ℝ) * c = (2 : ℝ) ^ 2 * (2 * c) from by ring]
                  rw [sqrt_mul (by positivity : (0:ℝ) ≤ 2 ^ 2),
                      sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
                  rw [sqrt_div (by linarith : 0 ≤ 2 * c)]; push_cast; ring
            _ = √(8 * c) * ∑ s ∈ range n,
                  (1 / √(↑(max 1 (pullCount A (A s ω) s ω)) : ℝ)) := by
                rw [mul_sum]
            _ = √(8 * c) * ∑ a : Fin K, ∑ j ∈ range (pullCount A a n ω),
                  (1 / √(↑(max 1 j) : ℝ)) := by
                congr 1; exact sum_comp_pullCount A (fun j => 1 / √(↑(max 1 j) : ℝ)) n ω
            _ ≤ √(8 * c) * ∑ a : Fin K, (2 * √↑(pullCount A a n ω)) := by
                gcongr with a; exact sum_inv_sqrt_max_one_le _
            _ = √(8 * c) * (2 * ∑ a : Fin K, √↑(pullCount A a n ω)) := by
              simp only [mul_sum]
            _ ≤ √(8 * c) * (2 * √(↑K * ↑n)) := by
                gcongr
                calc ∑ a : Fin K, √↑(pullCount A a n ω)
                    ≤ √(↑(Finset.univ.card) * ∑ a, ↑(pullCount A a n ω)) :=
                      sum_sqrt_le Finset.univ _ fun a => by positivity
                  _ = √(↑K * ↑n) := by
                      congr 1; rw [Finset.card_fin]; congr 1
                      have h := sum_pullCount (A := A) (t := n) (ω := ω)
                      exact_mod_cast h
            _ = 2 * √(8 * c) * √(↑K * ↑n) := by ring
        · have h0 : ∀ s ∈ range n,
              2 * √(2 * c / max 1 ↑(pullCount A (A s ω) s ω)) = 0 :=
            fun s _ => by
              open Real in
              have : 2 * c / max 1 ↑(pullCount A (A s ω) s ω) ≤ 0 :=
                div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
              simp [sqrt_eq_zero'.mpr this]
          rw [sum_congr rfl h0]; simp only [sum_const_zero]; positivity

lemma streamMeasure_concentration_le_delta {α : Type*} [MeasurableSpace α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : α) (k : ℕ) (hk : k ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * Real.log (1 / δ) / k) ≤ (ν a)[id]} ≤
      ENNReal.ofReal δ := by
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hδ |>.mpr hδ1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  calc
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * Real.log (1 / δ) / k) ≤ (ν a)[id]}
  _ = streamMeasure ν
        {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) / k ≤ -√(2 * Real.log (1 / δ) / k)} := by
      congr with ω
      field_simp
      rw [Finset.sum_sub_distrib]
      simp
      grind
  _ = streamMeasure ν
        {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ -√(2 * k * Real.log (1 / δ))} := by
      congr with ω
      field_simp
      congr! 2
      rw [Real.sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, Real.div_sqrt,
        mul_assoc (k : ℝ), Real.sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * k * Real.log (1 / δ)))^2 / (2 * k * 1))) := by
      rw [← ofReal_measureReal]
      gcongr
      refine HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun (c := 1) ?_ ?_ (by positivity)
      · exact (iIndepFun_eval_streamMeasure'' ν a).comp
          (fun i ω ↦ ω - (ν a)[id]) (fun _ ↦ by fun_prop)
      · intro i _; exact (hν a).congr_identDistrib
          ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)
  _ = ENNReal.ofReal δ := by
      rw [Real.sq_sqrt (by positivity)]
      simp only [neg_div, Real.exp_neg, mul_one]
      rw [mul_div_assoc, mul_div_cancel₀ _ (by positivity : (2 * k : ℝ) ≠ 0),
        Real.exp_log (by positivity : (0 : ℝ) < 1 / δ), one_div, inv_inv]

lemma streamMeasure_concentration_ge_delta {α : Type*} [MeasurableSpace α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : α) (k : ℕ) (hk : k ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * Real.log (1 / δ) / k)} ≤
      ENNReal.ofReal δ := by
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hδ |>.mpr hδ1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  calc
    streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * Real.log (1 / δ) / k)}
  _ = streamMeasure ν
        {ω | √(2 * Real.log (1 / δ) / k) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id])) / k} := by
      congr with ω
      field_simp
      rw [Finset.sum_sub_distrib]
      simp
      grind
  _ = streamMeasure ν
        {ω | √(2 * k * Real.log (1 / δ)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))} := by
      congr with ω
      field_simp
      congr! 1
      rw [Real.sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, Real.div_sqrt]
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.log (1 / δ)), mul_comm]
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * k * Real.log (1 / δ)))^2 / (2 * k * 1))) := by
      rw [← ofReal_measureReal]
      gcongr
      refine HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (c := 1) ?_ ?_ (by positivity)
      · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
          (fun _ ↦ by fun_prop)
      · intro i _; exact (hν a).congr_identDistrib
          ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)
  _ = ENNReal.ofReal δ := by
      rw [Real.sq_sqrt (by positivity)]
      simp only [neg_div, Real.exp_neg, mul_one]
      rw [mul_div_assoc, mul_div_cancel₀ _ (by positivity : (2 * k : ℝ) ≠ 0)]
      rw [Real.exp_log (by positivity), one_div, inv_inv]

lemma prob_concentration_single_delta_cond [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ Set.Icc 0 1)
    (a : Fin K) (s : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : 1 < 2 * Real.log (1 / δ)) :
    ∀ᵐ e ∂(P.map (IsBayesAlgEnvSeq.env R')),
      (condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e)
        {ω | √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s ω) : ℝ)) ≤
          |empMean IT.action IT.reward a s ω - (κ (a, e))[id]|} ≤
      ENNReal.ofReal (2 * s * δ) := by
  filter_upwards [IsBayesAlgEnvSeq.condDistrib_traj_isAlgEnvSeq h] with e h_isAlgEnvSeq
  let ν := κ.comap (·, e) (by fun_prop)
  have h_subG : ∀ a', HasSubgaussianMGF (fun x ↦ x - (ν a')[id]) 1 (ν a') := fun a' ↦ by
    simp only [ν, Kernel.comap_apply]; exact hs a' e
  have h_mean : (ν a)[id] = (κ (a, e))[id] := by simp only [ν, Kernel.comap_apply]
  rw [← h_mean]
  let P' := condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e
  have h_law := h_isAlgEnvSeq.law_pullCount_sumRewards_unique'
    (ArrayModel.isAlgEnvSeq_arrayMeasure (tsAlgorithm hK Q κ) ν) (n := s)
  let B_low := fun m : ℕ ↦ {x : ℝ | x / m + √(2 * Real.log (1 / δ) / m) ≤ (ν a)[id]}
  let B_high := fun m : ℕ ↦ {x : ℝ | (ν a)[id] ≤ x / m - √(2 * Real.log (1 / δ) / m)}
  have h_stream_bound : ∀ m : ℕ, m ≠ 0 →
      streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ≤
        ENNReal.ofReal (2 * δ) := by
    intro m hm0
    calc streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m}
        ≤ streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m} +
          streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_high m} := by
          have h_union : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ⊆
              {ω | ∑ i ∈ range m, ω i a ∈ B_low m} ∪ {ω | ∑ i ∈ range m, ω i a ∈ B_high m} := by
            intro ω hω; simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢; exact hω
          exact (measure_mono h_union).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
          gcongr
          · have h_eq : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m} =
                {ω | (∑ i ∈ range m, ω i a) / m + √(2 * Real.log (1 / δ) / m) ≤ (ν a)[id]} := by
              ext ω; simp only [Set.mem_setOf_eq, B_low]
            rw [h_eq]; exact streamMeasure_concentration_le_delta h_subG a m hm0 δ hδ hδ1
          · have h_eq : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_high m} =
                {ω | (ν a)[id] ≤ (∑ i ∈ range m, ω i a) / m - √(2 * Real.log (1 / δ) / m)} := by
              ext ω; simp only [Set.mem_setOf_eq, B_high]
            rw [h_eq]; exact streamMeasure_concentration_ge_delta h_subG a m hm0 δ hδ hδ1
      _ = ENNReal.ofReal (2 * δ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  let badSet := {ω : ℕ → (Fin K) × ℝ |
    √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s ω) : ℝ)) ≤
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
    · have h_empMean_zero : empMean IT.action IT.reward a s ω = 0 := by
        simp only [empMean, ← hm_def, hm0, Nat.cast_zero, div_zero]
      simp only [hm0, Nat.cast_zero, h_empMean_zero] at hω
      exfalso
      have h_mu := hm a e
      simp only [max_eq_left (zero_le_one' ℝ), div_one] at hω
      rw [h_mean, zero_sub, abs_neg, abs_of_nonneg h_mu.1] at hω
      have : 1 < √(2 * Real.log (1 / δ)) := by
        rw [Real.lt_sqrt (by norm_num)]; simpa using hδ_large
      linarith [h_mu.2]
    · -- Case: m ≥ 1
      use m
      refine ⟨⟨Nat.lt_succ_of_le hms, hm0⟩, rfl, ?_⟩
      simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq]
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
      have hmax_eq : (max 1 (m : ℕ) : ℝ) = m := by
        simp only [Nat.one_le_cast, Nat.one_le_iff_ne_zero.mpr hm0, max_eq_right]
      rw [hmax_eq] at hω
      have h_empMean : empMean IT.action IT.reward a s ω =
          sumRewards IT.action IT.reward a s ω / m := by
        simp only [empMean, hm_def]
      rw [h_empMean] at hω
      by_cases h_le : sumRewards IT.action IT.reward a s ω / m ≤ (ν a)[id]
      · left
        have habs : |sumRewards IT.action IT.reward a s ω / ↑m - (ν a)[id]| =
            (ν a)[id] - sumRewards IT.action IT.reward a s ω / m := by
          rw [abs_of_nonpos (sub_nonpos.mpr h_le), neg_sub]
        rw [habs] at hω
        linarith
      · right
        have h_gt : (ν a)[id] < sumRewards IT.action IT.reward a s ω / m := not_le.mp h_le
        have habs : |sumRewards IT.action IT.reward a s ω / ↑m - (ν a)[id]| =
            sumRewards IT.action IT.reward a s ω / m - (ν a)[id] :=
          abs_of_pos (sub_pos.mpr h_gt)
        rw [habs] at hω
        linarith
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
          streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2
        have hms : m ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
        exact h_bound_per_m m hm0 hms
    _ ≤ ∑ _m ∈ (Finset.range (s + 1)).filter (· ≠ 0), ENNReal.ofReal (2 * δ) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2
        exact h_stream_bound m hm0
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
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ Set.Icc 0 1)
    (a : Fin K) (s : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : 1 < 2 * Real.log (1 / δ)) :
    P {ω | √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|} ≤
      ENNReal.ofReal (2 * s * δ) := by
  let badSet : E → Set (ℕ → (Fin K) × ℝ) := fun e ↦
    {t | √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s t) : ℝ)) ≤
      |empMean IT.action IT.reward a s t - (κ (a, e))[id]|}
  have h_set_eq : {ω | √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
      |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|} =
      (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) ⁻¹'
        {p | p.2 ∈ badSet p.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, badSet, IsBayesAlgEnvSeq.armMean]
    have h1 : pullCount A a s ω = pullCount IT.action a s (IsBayesAlgEnvSeq.traj A R' ω) := by
      unfold pullCount IsBayesAlgEnvSeq.traj IT.action; rfl
    have h2 : empMean A (IsBayesAlgEnvSeq.reward R') a s ω =
        empMean IT.action IT.reward a s (IsBayesAlgEnvSeq.traj A R' ω) := by
      unfold empMean IsBayesAlgEnvSeq.traj IsBayesAlgEnvSeq.reward IT.action IT.reward; rfl
    rw [h1, h2]
  have h_meas_pair :
      Measurable (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) :=
    h.measurable_env.prodMk h.measurable_traj
  have h_disint : P.map (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) =
      P.map (IsBayesAlgEnvSeq.env R') ⊗ₘ
        condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P :=
    (compProd_map_condDistrib (h.measurable_traj.aemeasurable)).symm
  have h_cond := prob_concentration_single_delta_cond hK A R' Q κ P h hs hm a s δ hδ hδ1 hδ_large
  have h_kernel : Measurable (fun p : E × (ℕ → (Fin K) × ℝ) ↦ (κ (a, p.1))[id]) :=
    stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_const.prodMk measurable_fst)
  have h_meas_set : MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) | p.2 ∈ badSet p.1} := by
    change MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
        √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s p.2) : ℝ)) ≤
        |empMean IT.action IT.reward a s p.2 - (κ (a, p.1))[id]|}
    exact measurableSet_le (by fun_prop)
      (((measurable_empMean IT.measurable_action IT.measurable_reward a s).comp measurable_snd).sub
        h_kernel).abs
  calc P _ = P ((fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) ⁻¹'
          {p | p.2 ∈ badSet p.1}) := by rw [h_set_eq]
    _ = (P.map (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)))
          {p | p.2 ∈ badSet p.1} := by
        rw [Measure.map_apply h_meas_pair h_meas_set]
    _ = (P.map (IsBayesAlgEnvSeq.env R') ⊗ₘ
          condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P)
          {p | p.2 ∈ badSet p.1} := by rw [h_disint]
    _ = ∫⁻ e, (condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e)
          (badSet e) ∂(P.map (IsBayesAlgEnvSeq.env R')) := by
        rw [Measure.compProd_apply h_meas_set]; rfl
    _ ≤ ∫⁻ _e, ENNReal.ofReal (2 * s * δ) ∂(P.map (IsBayesAlgEnvSeq.env R')) := by
        apply lintegral_mono_ae
        filter_upwards [h_cond] with e h_e; exact h_e
    _ = ENNReal.ofReal (2 * s * δ) := by
        rw [lintegral_const, Measure.map_apply h.measurable_env MeasurableSet.univ]
        simp [measure_univ]

lemma prob_concentration_fail_delta [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ Set.Icc 0 1)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : 1 < 2 * Real.log (1 / δ)) :
    P {ω | ∃ s < n, ∃ a,
      √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|}
      ≤ ENNReal.ofReal (2 * K * n * δ) := by
  let badSet := fun (s : ℕ) (a : Fin K) ↦ {ω : Ω |
      √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|}
  have h_set_eq : {ω | ∃ s < n, ∃ a, √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - IsBayesAlgEnvSeq.armMean κ R' a ω|} =
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
      √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s ω) : ℝ)) ≤
        |empMean IT.action IT.reward a s ω - (κ (a, e))[id]|}
    have h_set_eq : ⋃ s ∈ Finset.range n, badSet s a =
        (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) ⁻¹'
          {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
      ext ω
      simp only [Set.mem_iUnion, Finset.mem_range, badSet, badSetIT, Set.mem_preimage,
        Set.mem_setOf_eq, IsBayesAlgEnvSeq.armMean]
      exact Iff.rfl
    rw [h_set_eq]
    have h_meas_pair :
        Measurable (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) :=
      h.measurable_env.prodMk h.measurable_traj
    have h_disint : P.map (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) =
        P.map (IsBayesAlgEnvSeq.env R') ⊗ₘ
          condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P :=
      (compProd_map_condDistrib (h.measurable_traj.aemeasurable)).symm
    have h_cond_bound : ∀ᵐ e ∂(P.map (IsBayesAlgEnvSeq.env R')),
        (condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e)
          (⋃ s ∈ Finset.range n, badSetIT s e) ≤ ENNReal.ofReal (2 * n * δ) := by
      filter_upwards [IsBayesAlgEnvSeq.condDistrib_traj_isAlgEnvSeq h] with e h_isAlgEnvSeq
      let ν := κ.comap (·, e) (by fun_prop)
      let P' := condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e
      have h_subG : ∀ a', HasSubgaussianMGF (fun x ↦ x - (ν a')[id]) 1 (ν a') := fun a' ↦ by
        simp only [ν, Kernel.comap_apply]; exact hs a' e
      have h_mean' : ∀ a', (κ (a', e))[id] ∈ Set.Icc 0 1 := fun a' ↦ hm a' e
      have h_mean : (ν a)[id] = (κ (a, e))[id] := by simp only [ν, Kernel.comap_apply]
      let B_low := fun m : ℕ ↦
        {x : ℝ | x / m + √(2 * Real.log (1 / δ) / m) ≤ (ν a)[id]}
      let B_high := fun m : ℕ ↦
        {x : ℝ | (ν a)[id] ≤ x / m - √(2 * Real.log (1 / δ) / m)}
      have h_stream_bound : ∀ m : ℕ, m ≠ 0 →
          streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ≤
            ENNReal.ofReal (2 * δ) := by
        intro m hm0
        calc streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m}
            ≤ streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m} +
              streamMeasure ν {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_high m} := by
              have h_union : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m ∪ B_high m} ⊆
                  {ω | ∑ i ∈ range m, ω i a ∈ B_low m} ∪
                  {ω | ∑ i ∈ range m, ω i a ∈ B_high m} := by
                intro ω hω; simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢; exact hω
              exact (measure_mono h_union).trans (measure_union_le _ _)
          _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
              gcongr
              · have h_eq : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_low m} =
                    {ω | (∑ i ∈ range m, ω i a) / m + √(2 * Real.log (1 / δ) / m) ≤ (ν a)[id]} := by
                  ext ω; simp only [Set.mem_setOf_eq, B_low]
                rw [h_eq]; exact streamMeasure_concentration_le_delta h_subG a m hm0 δ hδ hδ1
              · have h_eq : {ω : ℕ → Fin K → ℝ | ∑ i ∈ range m, ω i a ∈ B_high m} =
                    {ω | (ν a)[id] ≤ (∑ i ∈ range m, ω i a) / m - √(2 * Real.log (1 / δ) / m)} := by
                  ext ω; simp only [Set.mem_setOf_eq, B_high]
                rw [h_eq]; exact streamMeasure_concentration_ge_delta h_subG a m hm0 δ hδ hδ1
          _ = ENNReal.ofReal (2 * δ) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      have hB_meas : ∀ m, MeasurableSet (B_low m ∪ B_high m) := fun m ↦
        MeasurableSet.union (measurableSet_le (by fun_prop) (by fun_prop))
          (measurableSet_le (by fun_prop) (by fun_prop))
      let S := Finset.Icc 1 (n - 1)
      have hS_card : S.card = n - 1 := by simp only [Nat.card_Icc, S]; omega
      have h_decomp : ⋃ s ∈ Finset.range n, badSetIT s e =
          ⋃ m ∈ S, {ω | ∃ s, s < n ∧ pullCount IT.action a s ω = m ∧
            sumRewards IT.action IT.reward a s ω ∈ B_low m ∪ B_high m} := by
        ext ω
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, badSetIT, Set.mem_setOf_eq,
          Finset.mem_Icc, S]
        constructor
        · rintro ⟨s, hs, hbad⟩
          let m := pullCount IT.action a s ω
          have hm_pos : 0 < m := by
            by_contra hm0; push_neg at hm0
            have hm0' : pullCount IT.action a s ω = 0 := by omega
            simp only [hm0', Nat.cast_zero, max_eq_left (zero_le_one' ℝ), div_one,
              empMean, div_zero] at hbad
            rw [zero_sub, abs_neg, abs_of_nonneg (h_mean' a).1] at hbad
            have : 1 < √(2 * Real.log (1 / δ)) := by
              rw [Real.lt_sqrt (by norm_num)]; simpa using hδ_large
            linarith [(h_mean' a).2]
          have hm_le : m ≤ n - 1 := by
            have h1 : m ≤ s := pullCount_le (A := IT.action) a s ω
            omega
          refine ⟨m, ⟨hm_pos, hm_le⟩, s, hs, rfl, ?_⟩
          simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq]
          have h_pc_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
          simp only [empMean] at hbad
          rw [show (max 1 (pullCount IT.action a s ω) : ℝ) = m by
            simp only [m]; rw [max_eq_right]; exact Nat.one_le_cast.mpr hm_pos] at hbad
          have h_abs := le_abs'.mp hbad
          rcases h_abs with h_neg | h_pos
          · left; linarith
          · right; linarith
        · rintro ⟨m, ⟨hm_pos, hm_le⟩, s, hs, hpc, hB⟩
          refine ⟨s, hs, ?_⟩
          simp only [Set.mem_union, B_low, B_high, Set.mem_setOf_eq] at hB
          have h_pc_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
          simp only [empMean, hpc]
          rw [show (max 1 m : ℝ) = m by rw [max_eq_right]; exact Nat.one_le_cast.mpr hm_pos]
          cases hB with
          | inl h =>
            have h1 : sumRewards IT.action IT.reward a s ω / m - (κ (a, e))[id] ≤
                -√(2 * Real.log (1 / δ) / m) := by linarith
            calc √(2 * Real.log (1 / δ) / m)
                ≤ -(sumRewards IT.action IT.reward a s ω / m - (κ (a, e))[id]) := by linarith
              _ ≤ |sumRewards IT.action IT.reward a s ω / m - (κ (a, e))[id]| := neg_le_abs _
          | inr h =>
            have h1 : √(2 * Real.log (1 / δ) / m) ≤
                sumRewards IT.action IT.reward a s ω / m - (κ (a, e))[id] := by linarith
            exact h1.trans (le_abs_self _)
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
                rw [← sumRewards_eq_of_pullCount_eq hs' h_pc_eq]
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
        _ ≤ ∑ _m ∈ S, ENNReal.ofReal (2 * δ) := by
            apply Finset.sum_le_sum
            intro m hm
            have hm_pos : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1
            exact h_stream_bound m hm_pos
        _ = S.card • ENNReal.ofReal (2 * δ) := by simp only [Finset.sum_const]
        _ = (n - 1) • ENNReal.ofReal (2 * δ) := by rw [hS_card]
        _ ≤ ENNReal.ofReal (2 * n * δ) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (n - 1),
              ← ENNReal.ofReal_mul (Nat.cast_nonneg (n - 1))]
            apply ENNReal.ofReal_le_ofReal
            have h1 : (n - 1 : ℕ) ≤ n := Nat.sub_le n 1
            have h2 : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr h1
            nlinarith [h2, hδ.le]
    have h_kernel : Measurable (fun p : E × (ℕ → (Fin K) × ℝ) ↦ (κ (a, p.1))[id]) :=
      stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_const.prodMk measurable_fst)
    have h_meas_set : MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
        p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
      have h_eq : {p : E × (ℕ → (Fin K) × ℝ) | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} =
          ⋃ s ∈ Finset.range n, {p | p.2 ∈ badSetIT s p.1} := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      rw [h_eq]
      exact .biUnion (Finset.range n).countable_toSet fun s _ ↦ by
        simp only [badSetIT]
        change MeasurableSet {p : E × (ℕ → (Fin K) × ℝ) |
            √(2 * Real.log (1 / δ) / (max 1 (pullCount IT.action a s p.2) : ℝ)) ≤
            |empMean IT.action IT.reward a s p.2 - (κ (a, p.1))[id]|}
        exact measurableSet_le (by fun_prop)
          (((measurable_empMean IT.measurable_action IT.measurable_reward a s).comp
            measurable_snd).sub h_kernel).abs
    calc P ((fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)) ⁻¹'
          {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1})
        = (P.map (fun ω ↦ (IsBayesAlgEnvSeq.env R' ω, IsBayesAlgEnvSeq.traj A R' ω)))
            {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
          rw [Measure.map_apply h_meas_pair h_meas_set]
      _ = (P.map (IsBayesAlgEnvSeq.env R') ⊗ₘ
            condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P)
              {p | p.2 ∈ ⋃ s ∈ Finset.range n, badSetIT s p.1} := by
          rw [h_disint]
      _ = ∫⁻ e, (condDistrib (IsBayesAlgEnvSeq.traj A R') (IsBayesAlgEnvSeq.env R') P e)
            (⋃ s ∈ Finset.range n, badSetIT s e) ∂(P.map (IsBayesAlgEnvSeq.env R')) := by
          rw [Measure.compProd_apply h_meas_set]; rfl
      _ ≤ ∫⁻ _e, ENNReal.ofReal (2 * n * δ) ∂(P.map (IsBayesAlgEnvSeq.env R')) := by
          apply lintegral_mono_ae h_cond_bound
      _ = ENNReal.ofReal (2 * n * δ) := by
          rw [lintegral_const, Measure.map_apply h.measurable_env MeasurableSet.univ]
          simp [measure_univ]
  calc P (⋃ a : Fin K, ⋃ s ∈ Finset.range n, badSet s a)
      ≤ ∑ a : Fin K, P (⋃ s ∈ Finset.range n, badSet s a) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : Fin K, ENNReal.ofReal (2 * n * δ) := by
        apply Finset.sum_le_sum; intro a _; exact h_arm_bound a
    _ = K • ENNReal.ofReal (2 * n * δ) := by simp [Finset.sum_const]
    _ = ENNReal.ofReal (2 * K * n * δ) := by
        simp only [nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
        congr 1; ring

lemma bayesRegret_le_of_delta [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδ_large : 1 < 2 * Real.log (1 / δ)) :
    IsBayesAlgEnvSeq.bayesRegret κ A R' P n
      ≤ 4 * K * n ^ 2 * δ + 2 * √(8 * Real.log (1 / δ)) * √(↑K * ↑n) := by
  let bestArm := IsBayesAlgEnvSeq.bestArm κ R'
  let armMean := IsBayesAlgEnvSeq.armMean κ R'
  let ucb := ucbIndex A R' δ
  set Eδ : Set Ω := {ω | ∀ s < n, ∀ a,
    |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - armMean a ω|
      < √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ))}
  have hm_ucb : ∀ a t, Measurable (ucbIndex A R' δ a t) :=
    fun a t ↦ measurable_ucbIndex hK A R' Q κ P h δ a t
  have hm_arm : ∀ a, Measurable (IsBayesAlgEnvSeq.armMean κ R' a) :=
    fun a ↦ h.measurable_armMean a
  have hm_best : Measurable (IsBayesAlgEnvSeq.bestArm κ R') := h.measurable_bestArm
  have h_first_bound : ∀ ω,
      |∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)| ≤ n := fun ω ↦
    calc |∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)|
        ≤ ∑ s ∈ range n, |armMean (bestArm ω) ω - ucb (bestArm ω) s ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun s _ ↦
          abs_sub_le_one_of_mem_Icc (hm _ _) (ucbIndex_mem_Icc A R' δ _ _ _)
      _ = ↑n := by simp
  have h_second_bound : ∀ ω,
      |∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)| ≤ n := fun ω ↦
    calc |∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)|
        ≤ ∑ s ∈ range n, |ucb (A s ω) s ω - armMean (A s ω) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun s _ ↦
          abs_sub_le_one_of_mem_Icc (ucbIndex_mem_Icc A R' δ _ _ _) (hm _ _)
      _ = ↑n := by simp
  have h_int_sum1 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)) P := by
    apply Integrable.of_bound (C := (↑n))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin hm_arm hm_best).sub
          (measurable_apply_fin (fun a ↦ hm_ucb a s) hm_best)).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_first_bound ω
  have h_int_sum2 : Integrable (fun ω ↦ ∑ s ∈ range n,
      (ucb (A s ω) s ω - armMean (A s ω) ω)) P := by
    apply Integrable.of_bound (C := (↑n))
    · exact (Finset.measurable_fun_sum _ fun s _ ↦
        (measurable_apply_fin (fun a ↦ hm_ucb a s) (h.measurable_A s)).sub
          (measurable_apply_fin hm_arm (h.measurable_A s))).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact h_second_bound ω
  have h_swap :
      IsBayesAlgEnvSeq.bayesRegret κ A R' P n =
      P[fun ω ↦ ∑ s ∈ range n,
        (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)] +
      P[fun ω ↦ ∑ s ∈ range n,
        (ucb (A s ω) s ω - armMean (A s ω) ω)] := by
    have hC : ∀ a e, |(κ (a, e))[id]| ≤ 1 := fun a e ↦ by
      have := hm a e; rw [abs_le]; exact ⟨by linarith [this.1], this.2⟩
    have h_regret_gap := bayesRegret_eq_sum_integral_gap (h := h) (hm := hC) (t := n)
    have h_regret_eq : IsBayesAlgEnvSeq.bayesRegret κ A R' P n =
        ∑ s ∈ range n, P[fun ω ↦ armMean (bestArm ω) ω - armMean (A s ω) ω] := by
      rw [h_regret_gap]; congr 1 with s
      exact integral_congr_ae (ae_of_all _ fun ω ↦ gap_eq_armMean_sub A R' κ hm s ω)
    have h_int_ucb_sub : ∀ s, Integrable (fun ω ↦ ucb (A s ω) s ω - ucb (bestArm ω) s ω) P := by
      intro s
      apply Integrable.sub
      · exact ⟨(measurable_apply_fin (fun a ↦ hm_ucb a s) (h.measurable_A s)).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (ae_of_all _ fun ω ↦ norm_ucbIndex_le_one A R' _ _ _ _)⟩
      · exact ⟨(measurable_apply_fin (fun a ↦ hm_ucb a s) hm_best).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (ae_of_all _ fun ω ↦ norm_ucbIndex_le_one A R' _ _ _ _)⟩
    have h_ucb_zero : ∀ a (ω : Ω), ucbIndex A R' δ a 0 ω =
        max 0 (min 1 (√(2 * Real.log (1 / δ)))) := by
      intro a ω; unfold ucbIndex empMean sumRewards; simp [pullCount_zero]
    have h_ucb_swap : ∀ s, ∫ ω, (ucb (A s ω) s ω - ucb (bestArm ω) s ω) ∂P = 0 := by
      intro s
      cases s with
      | zero =>
        have : ∀ ω, ucb (A 0 ω) 0 ω - ucb (bestArm ω) 0 ω = 0 := fun ω ↦ by
          change ucbIndex A R' δ _ 0 ω - ucbIndex A R' δ _ 0 ω = 0
          simp [h_ucb_zero]
        exact (integral_congr_ae (ae_of_all _ this)).trans (integral_zero _ _)
      | succ t =>
        have hts := ts_identity hK A R' Q κ P h t
        have h_map_eq : P.map (fun ω ↦ (IsBayesAlgEnvSeq.hist A R' t ω, A (t + 1) ω)) =
            P.map (fun ω ↦ (IsBayesAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestArm κ R' ω)) := by
          rw [← compProd_map_condDistrib (hY := (h.measurable_A (t + 1)).aemeasurable),
              ← compProd_map_condDistrib (hY := hm_best.aemeasurable)]
          exact Measure.compProd_congr hts
        have h_int_eq : ∀ (f : (Iic t → Fin K × ℝ) × Fin K → ℝ), Measurable f →
            ∫ ω, f (IsBayesAlgEnvSeq.hist A R' t ω, A (t + 1) ω) ∂P =
            ∫ ω, f (IsBayesAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestArm κ R' ω) ∂P := by
          intro f hf
          rw [← integral_map
                ((h.measurable_hist t).prodMk (h.measurable_A (t + 1))).aemeasurable
                hf.aestronglyMeasurable,
              ← integral_map
                ((h.measurable_hist t).prodMk hm_best).aemeasurable
                hf.aestronglyMeasurable,
              h_map_eq]
        set g : (Iic t → Fin K × ℝ) × Fin K → ℝ :=
          fun p ↦ max 0 (min 1 (empMean' t p.1 p.2 +
            √(2 * Real.log (1 / δ) / (max 1 (pullCount' t p.1 p.2) : ℝ))))
        have h_hist_eq : ∀ (ω : Ω),
            (fun (i : Iic t) ↦ (A (↑i) ω,
              IsBayesAlgEnvSeq.reward R' (↑i) ω)) =
            IsBayesAlgEnvSeq.hist A R' t ω := by
          intro ω; rfl
        have hg_eq : ∀ a (ω : Ω), ucbIndex A R' δ a (t + 1) ω =
            g (IsBayesAlgEnvSeq.hist A R' t ω, a) := by
          intro a ω
          simp only [g, ucbIndex]
          rw [empMean_add_one_eq_empMean' (A := A) (R' := IsBayesAlgEnvSeq.reward R'),
              pullCount_add_one_eq_pullCount' (A := A) (R' := IsBayesAlgEnvSeq.reward R'),
              h_hist_eq]
        have hg_meas : Measurable g := by
          apply Measurable.max measurable_const
          apply Measurable.min measurable_const
          apply Measurable.add
          · exact measurable_apply_fin (fun a ↦ (measurable_empMean' t a).comp measurable_fst)
              measurable_snd
          · apply Measurable.sqrt
            apply Measurable.div measurable_const
            apply Measurable.max measurable_const
            exact measurable_apply_fin
              (fun a ↦ measurable_from_top.comp ((measurable_pullCount' t a).comp measurable_fst))
              measurable_snd
        have h_eq_g1 : (fun ω ↦ ucb (A (t + 1) ω) (t + 1) ω) =
            fun ω ↦ g (IsBayesAlgEnvSeq.hist A R' t ω, A (t + 1) ω) :=
          funext fun ω ↦ hg_eq _ _
        have h_eq_g2 : (fun ω ↦ ucb (bestArm ω) (t + 1) ω) =
            fun ω ↦ g (IsBayesAlgEnvSeq.hist A R' t ω, IsBayesAlgEnvSeq.bestArm κ R' ω) :=
          funext fun ω ↦ hg_eq _ _
        have h_int_ucb : ∀ {f : Ω → Fin K}, Measurable f →
            Integrable (fun ω ↦ ucb (f ω) (t + 1) ω) P := fun hf ↦
          ⟨(measurable_apply_fin (fun a ↦ hm_ucb a (t + 1)) hf).aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (ae_of_all _ fun ω ↦ norm_ucbIndex_le_one A R' _ _ _ _)⟩
        have h_int1 := h_int_ucb (h.measurable_A (t + 1))
        have h_int2 := h_int_ucb hm_best
        rw [show (fun ω ↦ ucb (A (t + 1) ω) (t + 1) ω -
            ucb (bestArm ω) (t + 1) ω) =
            fun ω ↦ (fun ω ↦ ucb (A (t + 1) ω) (t + 1) ω) ω -
              (fun ω ↦ ucb (bestArm ω) (t + 1) ω) ω from rfl,
          integral_sub h_int1 h_int2, h_eq_g1, h_eq_g2,
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
        1 (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      exact abs_sub_le_one_of_mem_Icc (hm _ _) (hm _ _)
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
  have h_first_Eδ : ∀ ω ∈ Eδ,
      ∑ s ∈ range n, (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)
        ≤ 0 := by
    intro ω hω
    apply Finset.sum_nonpos
    intro s hs
    linarith [armMean_le_ucbIndex A R' κ hm δ
      (bestArm ω) s ω (hω s (mem_range.mp hs) _)]
  have h_second_Eδ : ∀ ω ∈ Eδ,
      ∑ s ∈ range n, (ucb (A s ω) s ω - armMean (A s ω) ω)
        ≤ 2 * √(8 * Real.log (1 / δ)) * √(↑K * ↑n) := by
    intro ω hω
    exact sum_ucbIndex_sub_armMean_le A R' κ hm δ n ω hω
  have h_prob : P Eδᶜ ≤ ENNReal.ofReal (2 * K * n * δ) := by
    have : Eδᶜ = {ω | ∃ s < n, ∃ a, √(2 * Real.log (1 / δ) / (max 1 (pullCount A a s ω) : ℝ)) ≤
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - armMean a ω|} := by
      ext ω; simp only [Eδ, Set.mem_compl_iff, Set.mem_setOf_eq]; push_neg; rfl
    rw [this]
    exact prob_concentration_fail_delta (hK := hK) (A := A) (R' := R')
      (Q := Q) (κ := κ) (P := P) h hs hm n δ hδ hδ1 hδ_large
  have hm_emp : ∀ a s, Measurable (fun ω ↦ empMean A (IsBayesAlgEnvSeq.reward R') a s ω) :=
    fun a s ↦ measurable_empMean (fun n ↦ h.measurable_A n) (fun n ↦ h.measurable_reward n) a s
  have hm_pc : ∀ a s, Measurable (fun ω ↦ (pullCount A a s ω : ℝ)) :=
    fun a s ↦ measurable_from_top.comp (measurable_pullCount (fun n ↦ h.measurable_A n) a s)
  have hEδ_meas : MeasurableSet Eδ := by
    suffices ∀ s a, MeasurableSet {ω |
        |empMean A (IsBayesAlgEnvSeq.reward R') a s ω - armMean a ω|
          < √(2 * Real.log (1 / δ) / max 1 ↑(pullCount A a s ω))} by
      simp only [Eδ, Set.setOf_forall]
      exact .iInter fun s ↦ .iInter fun _ ↦ .iInter fun a ↦ this s a
    intro s a
    exact measurableSet_lt
      ((hm_emp a s).sub (h.measurable_armMean a)).abs
      ((measurable_const.div (measurable_const.max (hm_pc a s))).sqrt)
  rw [h_swap]
  set f1 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (armMean (bestArm ω) ω - ucb (bestArm ω) s ω)
  set f2 : Ω → ℝ := fun ω ↦ ∑ s ∈ range n,
    (ucb (A s ω) s ω - armMean (A s ω) ω)
  set B := 2 * √(8 * Real.log (1 / δ)) * √(↑K * ↑n)
  have s1 := (integral_add_compl hEδ_meas h_int_sum1).symm
  have s2 := (integral_add_compl hEδ_meas h_int_sum2).symm
  have h1g : ∫ ω in Eδ, f1 ω ∂P ≤ 0 :=
    setIntegral_nonpos hEδ_meas fun ω hω ↦ h_first_Eδ ω hω
  have h_compl_bound : ∀ {f}, Integrable f P → (∀ ω, f ω ≤ ↑n) →
      ∫ ω in Eδᶜ, f ω ∂P ≤ ↑n * P.real Eδᶜ := fun hint hle ↦ by
    have := setIntegral_mono_on (hf := hint.integrableOn) (hg := integrableOn_const)
      hEδ_meas.compl fun ω _ ↦ hle ω
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have h1b := h_compl_bound h_int_sum1 fun ω ↦ (abs_le.mp (h_first_bound ω)).2
  have h2g : ∫ ω in Eδ, f2 ω ∂P ≤ B := by
    have hB : 0 ≤ B := by positivity
    have := setIntegral_mono_on (hf := h_int_sum2.integrableOn)
      (hg := integrableOn_const) hEδ_meas
      fun ω hω ↦ h_second_Eδ ω hω
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact le_trans this (mul_le_of_le_one_right hB measureReal_le_one)
  have h2b := h_compl_bound h_int_sum2 fun ω ↦ (abs_le.mp (h_second_bound ω)).2
  have hP : P.real Eδᶜ ≤ 2 * ↑K * ↑n * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h_prob
  rw [s1, s2]
  have hP0 : 0 ≤ P.real Eδᶜ := by positivity
  nlinarith

lemma TS.bayesRegret_le [Nonempty (Fin K)] [StandardBorelSpace Ω] [Nonempty Ω]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1)) (t : ℕ) :
    IsBayesAlgEnvSeq.bayesRegret κ A R' P t ≤ 4 * K + 8 * √(K * t * Real.log t) := by
  by_cases ht : t = 0
  · simp [ht, IsBayesAlgEnvSeq.bayesRegret, IsBayesAlgEnvSeq.regret, regret]
  by_cases ht1_eq : t = 1
  · subst ht1_eq
    simp only [Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
    calc IsBayesAlgEnvSeq.bayesRegret κ A R' P 1
        ≤ 1 := by
          unfold IsBayesAlgEnvSeq.bayesRegret IsBayesAlgEnvSeq.regret Bandits.regret
          simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, one_mul,
            Kernel.comap_apply]
          refine (integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sub_nonneg.mpr
              (le_ciSup ⟨1, by rintro _ ⟨a, rfl⟩; exact (hm a _).2⟩ _))
            (integrable_const 1) (ae_of_all _ fun ω ↦ by
              linarith [ciSup_le fun a ↦ (hm a (IsBayesAlgEnvSeq.env R' ω)).2,
                (hm (A 0 ω) (IsBayesAlgEnvSeq.env R' ω)).1])).trans ?_
          simp
      _ ≤ 4 * (K : ℝ) := by
          nlinarith [show (1 : ℝ) ≤ K from Nat.one_le_cast.mpr (Nat.one_le_of_lt hK)]
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
    -- First term simplification: 4K · t² · (1/t²) = 4K
    have h_first : 4 * (K : ℝ) * ↑t ^ 2 * (1 / (↑t) ^ 2) = 4 * ↑K := by
      field_simp
    -- Second term simplification: log(1/(1/t²)) = log(t²) = 2 log(t)
    have h_log : Real.log (1 / (1 / (↑t : ℝ) ^ 2)) = 2 * Real.log ↑t := by
      rw [one_div_one_div, Real.log_pow]; norm_cast
    -- For t ≥ 2, we have 2 * log(t²) = 4 log(t) ≥ 4 log(2) > 1 (since log(2) > 0.69)
    have hδ_large : 1 < 2 * Real.log (1 / (1 / (↑t : ℝ) ^ 2)) := by
      rw [h_log]
      have h_log2 : (1 : ℝ) / 2 < Real.log 2 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
        calc Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by rw [← Real.exp_half]
          _ < Real.sqrt 4 := by gcongr; linarith [Real.exp_one_lt_d9]
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have ht2_real : (2 : ℝ) ≤ t := Nat.ofNat_le_cast.mpr ht2
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2_real]
    have hK_real_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have hKt_nonneg : (0 : ℝ) ≤ ↑K * ↑t := by positivity
    calc IsBayesAlgEnvSeq.bayesRegret κ A R' P t
        ≤ 4 * ↑K * ↑t ^ 2 * (1 / (↑t) ^ 2)
          + 2 * √(8 * Real.log (1 / (1 / (↑t) ^ 2))) * √(↑K * ↑t) :=
          bayesRegret_le_of_delta (hK := hK) (A := A) (R' := R') (Q := Q)
            (κ := κ) (P := P) h hs hm t (1 / (↑t) ^ 2) hδ hδ1 hδ_large
      _ = 4 * ↑K + 2 * √(16 * Real.log ↑t) * √(↑K * ↑t) := by rw [h_first, h_log]; ring_nf
      _ = 4 * ↑K + 8 * (√(Real.log ↑t) * √(↑K * ↑t)) := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 2),
              Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]; ring
      _ = 4 * ↑K + 8 * √(↑K * ↑t * Real.log ↑t) := by
          rw [← Real.sqrt_mul (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero ht)))]
          ring_nf

end Regret

end Bandits
