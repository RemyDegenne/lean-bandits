/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} {X Y : Ω → ℝ} {Z W : Ω' → ℝ}

lemma IdentDistrib.prod [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hXZ : IdentDistrib X Z μ ν) (hYW : IdentDistrib Y W μ ν)
    (hXY : IndepFun X Y μ) (hZW : IndepFun Z W ν) :
    IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω' ↦ (Z ω', W ω')) μ ν where
  aemeasurable_fst := hXZ.aemeasurable_fst.prodMk hYW.aemeasurable_fst
  aemeasurable_snd := hXZ.aemeasurable_snd.prodMk hYW.aemeasurable_snd
  map_eq := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hXZ.aemeasurable_fst hYW.aemeasurable_fst).mp hXY,
      (indepFun_iff_map_prod_eq_prod_map_map hXZ.aemeasurable_snd hYW.aemeasurable_snd).mp hZW,
      hXZ.map_eq, hYW.map_eq]

end ProbabilityTheory
