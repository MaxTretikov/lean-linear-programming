/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Standard Form Equivalence for Linear Programs

This file re-exports all LP-related definitions and theorems.

## Main Results

* `StandardFormLP` - Definition of a linear program in standard form
* `GeneralLP` - Definition of a general linear program
* `minToMax_optimal_iff` - Step 1: Min/max equivalence
* `geToLe_optimal_iff` - Step 2: Converting ≥ to ≤ constraints
* `eqToLeq_optimal_iff` - Step 3: Converting = to ≤ constraints
* `free_decomposition` - Step 4: Making variables nonnegative
* `general_to_standard_form_equivalence` - Full equivalence theorem

## Reduction to Reduced Form

* `ReducedForm` - LP in reduced form after row reduction
* `ReducedForm.feasible` - Feasibility predicate for reduced form
* `fullRowRank` - Full row rank predicate for matrices
* `rowReduceStandardForm` - Row-reduces Standard Form LP to Reduced Form
* `fullReduction` - Full reduction from inequality form to reduced form
* `fullReduction_correct` - Correctness theorem for the full reduction
-/

import LinearProgramming.Defs
import LinearProgramming.MinToMax
import LinearProgramming.SwapInequalities
import LinearProgramming.NonnegConstraint
import LinearProgramming.Equivalence
import LinearProgramming.RowOperations
import LinearProgramming.Reduction
import LinearProgramming.Preprocess
import LinearProgramming.FacialReduction
