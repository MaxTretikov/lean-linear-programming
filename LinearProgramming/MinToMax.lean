/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Step 1: Minimization to Maximization

Converting minimization LPs to maximization by negating the objective.
-/

import LinearProgramming.Defs

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

variable {n m₁ m₂ m₃ : ℕ}

/-- Convert a minimization LP to maximization by negating the objective -/
def minToMax (lp : GeneralLP n m₁ m₂ m₃) : GeneralLP n m₁ m₂ m₃ :=
  { lp with
    dir := .maximize
    c := -lp.c }

theorem minToMax_feasible_iff (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (minToMax lp).IsFeasible y ↔ lp.IsFeasible y := by
  simp only [GeneralLP.IsFeasible, minToMax]

theorem minToMax_objective (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (minToMax lp).objective y = -lp.objective y := by
  simp only [GeneralLP.objective, minToMax, inner_neg_left]

/-- Key theorem: y* minimizes c^T y iff y* maximizes (-c)^T y -/
theorem minToMax_optimal_iff (lp : GeneralLP n m₁ m₂ m₃)
    (h : lp.dir = .minimize) (y : Vec n) :
    lp.IsOptimal y ↔ (minToMax lp).IsOptimal y := by
  constructor
  · intro ⟨hfeas, hopt⟩
    constructor
    · exact (minToMax_feasible_iff lp y).mpr hfeas
    · intro z hzfeas
      rw [minToMax_objective, minToMax_objective]
      have hz_orig := (minToMax_feasible_iff lp z).mp hzfeas
      simp only [h] at hopt
      exact neg_le_neg (hopt z hz_orig)
  · intro ⟨hfeas, hopt⟩
    constructor
    · exact (minToMax_feasible_iff lp y).mp hfeas
    · simp only [h]
      intro z hz_feas
      have hz_max := (minToMax_feasible_iff lp z).mpr hz_feas
      have := hopt z hz_max
      rw [minToMax_objective, minToMax_objective] at this
      exact neg_le_neg_iff.mp this

end
