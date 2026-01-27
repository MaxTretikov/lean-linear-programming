/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Standard Form Equivalence

Full equivalence theorem: any general LP can be converted to standard form.
This file provides the complete pipeline for transforming a general LP.
-/

import LeanLinearProgramming.Defs
import LeanLinearProgramming.MinToMax
import LeanLinearProgramming.SwapInequalities
import LeanLinearProgramming.NonnegConstraint

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

variable {n m₁ m₂ m₃ m : ℕ}

/-- Convert a general LP to a simplified LP (after Steps 2 and 3) -/
def generalToSimplified (lp : GeneralLP n m₁ m₂ m₃) : SimplifiedLP n (m₁ + m₂ + 2 * m₃) :=
  let lp' := geToLe lp
  let lp'' := eqToLeq lp'
  { dir := lp''.dir
    c := lp''.c
    A := lp''.A₁
    b := lp''.b₁
    σ := lp''.σ }

/-- The simplified LP preserves feasibility from the original general LP -/
theorem generalToSimplified_feasible_iff (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (generalToSimplified lp).IsFeasible y ↔ lp.IsFeasible y := by
  simp only [generalToSimplified, SimplifiedLP.IsFeasible]
  -- Use the chain of equivalences from geToLe and eqToLeq
  have hge := geToLe_feasible_iff lp y
  have heq := eqToLeq_feasible_iff (geToLe lp) y
  -- Chain: SimplifiedLP.IsFeasible ↔ (eqToLeq (geToLe lp)).IsFeasible ↔ lp.IsFeasible
  constructor
  · intro ⟨hconstr, hsign⟩
    -- First, show (eqToLeq (geToLe lp)).IsFeasible y
    have h_eqToLeq : (eqToLeq (geToLe lp)).IsFeasible y := by
      simp only [GeneralLP.IsFeasible, eqToLeq, geToLe]
      refine ⟨hconstr, ?_, ?_, hsign⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
    -- Then use equivalences
    exact hge.mp (heq.mp h_eqToLeq)
  · intro hy
    -- Use equivalences in reverse
    have h_geToLe := hge.mpr hy
    have h_eqToLeq := heq.mpr h_geToLe
    simp only [GeneralLP.IsFeasible, eqToLeq, geToLe] at h_eqToLeq
    exact ⟨h_eqToLeq.1, h_eqToLeq.2.2.2⟩

/-- The simplified LP preserves optimality direction -/
theorem generalToSimplified_dir (lp : GeneralLP n m₁ m₂ m₃) :
    (generalToSimplified lp).dir = lp.dir := rfl

/-- The simplified LP preserves the objective function -/
theorem generalToSimplified_objective (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (generalToSimplified lp).objective y = lp.objective y := rfl

/-- Main result: The transformation pipeline preserves feasibility -/
theorem general_feasibility_equivalence (lp : GeneralLP n m₁ m₂ m₃) :
    lp.isFeasible ↔ (generalToSimplified lp).isFeasible := by
  simp only [GeneralLP.isFeasible, SimplifiedLP.isFeasible]
  constructor
  · intro ⟨y, hy⟩
    exact ⟨y, (generalToSimplified_feasible_iff lp y).mpr hy⟩
  · intro ⟨y, hy⟩
    exact ⟨y, (generalToSimplified_feasible_iff lp y).mp hy⟩

/-- For maximization LPs, the transformation preserves optimality -/
theorem general_optimal_max (lp : GeneralLP n m₁ m₂ m₃) (h : lp.dir = .maximize) (y : Vec n) :
    lp.IsOptimal y ↔ (generalToSimplified lp).IsFeasible y ∧
      ∀ z, (generalToSimplified lp).IsFeasible z →
        (generalToSimplified lp).objective z ≤ (generalToSimplified lp).objective y := by
  simp only [GeneralLP.IsOptimal, h]
  simp only [generalToSimplified_feasible_iff, generalToSimplified_objective]

/-- For minimization LPs, we can convert to maximization first -/
theorem general_optimal_min (lp : GeneralLP n m₁ m₂ m₃) (h : lp.dir = .minimize) (y : Vec n) :
    lp.IsOptimal y ↔ (minToMax lp).IsOptimal y := minToMax_optimal_iff lp h y

end
