/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-- Euclidean space of dimension `d`.
Used as the domain for LIPO optimization problems. -/
abbrev ED (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[inherit_doc ED]
notation3 "ℝᵈ " d => ED d
