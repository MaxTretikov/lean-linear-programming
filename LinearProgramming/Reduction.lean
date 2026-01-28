/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 1 LP Reduction

This module provides the LP-specific Phase 1 reduction algorithm that uses Gaussian
elimination to transform inequality-form LPs into reduced form and check for infeasibility.

## Overview

The Phase 1 reduction performs two steps:

1. **Convert to Standard Form**: Transform `Ax ≤ b` into `By = c, y ≥ 0` using
   slack variables and variable decomposition (via `toStandardForm`)

2. **Apply Gaussian Elimination**: Transform to reduced form where `c = (0,...,0,c_m)`

The algorithm can detect infeasibility: if `c_m = 0` and the reduced matrix has
full row rank, then the only solution is `y = 0`, which is infeasible when `c ≠ 0`.

## Main Definitions

- `Phase1Result`: Either `infeasible` or `reduced R` with the reduced form
- `phase1Reduction`: The main Phase 1 algorithm for Standard Form
- `phase1ReductionLP`: Wrapper for Inequality Form LPs
- `fullReduction`: Direct reduction without infeasibility check
- `fullReduction_correct`: Correctness theorem for the full reduction

## Re-exports

This module re-exports key definitions from the reduction pipeline for convenience:
- `InequalityForm.feasible`, `InequalityForm.isFeasible`
- `StandardForm.feasible`, `StandardForm.isFeasible`
- `ReducedForm`, `ReducedForm.feasible`, `fullRowRank`

-/

import LinearProgramming.GaussianElimination
import LinearProgramming.Equivalence

noncomputable section

open Matrix

-- Re-export definitions from LinearProgramming for convenience
export InequalityForm (feasible isFeasible)
export StandardForm (feasible isFeasible)

-- Alias for the conversion function (backwards compatibility)
abbrev toInitialStandardForm {m n : ℕ} (P : InequalityForm m n) : StandardForm m (2 * n + m) :=
  toStandardForm P

/-! ## Phase 1 Result Type -/

/-- Phase 1 output: either infeasible or a reduced form `B, c_m`.

- `infeasible`: The LP has no feasible solution (detected via rank condition)
- `reduced R`: The LP has been reduced to form `R`, feasibility still needs checking -/
inductive Phase1Result (m p : ℕ) where
  | infeasible
  | reduced (R : ReducedForm m p)

/-! ## Phase 1 Reduction Algorithm -/

/--
Phase 1 as stated in the paper: apply Gaussian elimination, then check whether
`c_m = 0` and `B` has full row rank. If so, return infeasible; otherwise return
the reduced form.

**Infeasibility criterion**: When `c_m = 0` and the reduced matrix has full row rank,
the system `By = 0, y ≥ 0` has only the trivial solution `y = 0`. But if the original
`c ≠ 0`, this means the original system `By = c` has no nonnegative solution.
-/
def phase1Reduction {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
    Phase1Result m p := by
  classical
  let R := (gaussianElimination S hm).toReducedForm
  by_cases h : R.c_m = 0 ∧ fullRowRank R.B
  · exact Phase1Result.infeasible
  · exact Phase1Result.reduced R

/-- When Phase 1 returns a reduced form, feasibility of the original LP is equivalent
    to feasibility of the reduced form. -/
theorem phase1Reduction_reduced_correct {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
    match phase1Reduction S hm with
    | Phase1Result.infeasible => True
    | Phase1Result.reduced R => S.isFeasible ↔ ∃ y, R.feasible hm y := by
  classical
  unfold phase1Reduction
  -- The reduced branch uses the Gaussian-elimination reduced form.
  by_cases h : ((gaussianElimination S hm).toReducedForm).c_m = 0 ∧
      fullRowRank ((gaussianElimination S hm).toReducedForm).B
  · simp [h]
  · simpa [h] using (gaussianElimination_correct S hm)

/-- When the original RHS is nonzero, Phase 1 never returns `infeasible`.

This is because Gaussian elimination transforms nonzero `c` to `(0,...,0,1)` with `c_m = 1 ≠ 0`,
so the infeasibility criterion `c_m = 0 ∧ fullRowRank` cannot be satisfied. -/
theorem phase1Reduction_not_infeasible_of_c_ne_zero {m p : ℕ}
    (S : StandardForm m p) (hm : m > 0) (hc : S.c ≠ 0) :
    phase1Reduction S hm ≠ Phase1Result.infeasible := by
  classical
  -- In the `S.c ≠ 0` branch, Gaussian elimination sets `c_m = 1`,
  -- so the infeasible guard cannot trigger.
  unfold phase1Reduction
  let R := (gaussianElimination S hm).toReducedForm
  have hcm' : R.c_m = 1 := by
    -- `gaussianElimination` uses the nonzero branch and sets `c_m = 1`.
    have hcm' : (gaussianElimination S hm).c_m = 1 := by
      by_cases hc0 : S.c = 0
      · exact (hc hc0).elim
      · simp [gaussianElimination, hc0]
    simpa [R, RowReduction.toReducedForm] using hcm'
  have hcm : R.c_m ≠ 0 := by
    simpa [hcm']
  have h' : ¬ (R.c_m = 0 ∧ fullRowRank R.B) := by
    intro h
    exact hcm h.1
  simpa [phase1Reduction, R, h']

/-! ## Convenience Functions -/

/-- Phase 1 reduction starting from an Inequality Form LP `Ax ≤ b`.

First converts to Standard Form, then applies Phase 1 reduction. -/
def phase1ReductionLP {m n : ℕ} (P : InequalityForm m n) (hm : m > 0) :
    Phase1Result m (2 * n + m) :=
  phase1Reduction (toStandardForm P) hm

/-- Full reduction from Inequality Form to Reduced Form, bypassing the infeasibility check.

This directly applies Gaussian elimination without checking the `c_m = 0 ∧ fullRowRank`
condition. Use this when you want the reduced form regardless of potential infeasibility. -/
def fullReduction {m n : ℕ} (P : InequalityForm m n) (hm : m > 0) : ReducedForm m (2 * n + m) :=
  (gaussianElimination (toStandardForm P) hm).toReducedForm

/-- The full reduction preserves feasibility: the original Inequality Form LP is feasible
    if and only if the resulting Reduced Form LP is feasible. -/
theorem fullReduction_correct {m n : ℕ} (P : InequalityForm m n) (hm : m > 0) :
    P.isFeasible ↔ ∃ y, (fullReduction P hm).feasible hm y := by
  calc P.isFeasible
      ↔ (toStandardForm P).isFeasible := reduction_correct P
    _ ↔ ∃ y, (fullReduction P hm).feasible hm y :=
        (gaussianElimination_correct (toStandardForm P) hm)

end
