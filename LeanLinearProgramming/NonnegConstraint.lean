/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Step 4: Making variables nonnegative

Transformations for handling sign constraints on variables:
- Nonpositive variables y ≤ 0 become nonnegative via y = -x
- Free variables y are decomposed as y = x⁺ - x⁻ where x⁺, x⁻ ≥ 0
-/

import LeanLinearProgramming.Defs

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

/-- For a nonpositive variable y ≤ 0, substituting y = -x gives x ≥ 0 -/
theorem nonpos_to_nonneg (y : ℝ) : y ≤ 0 ↔ -y ≥ 0 := by
  constructor <;> intro h <;> linarith

/-- For a free variable, y = x⁺ - x⁻ where x⁺, x⁻ ≥ 0 -/
theorem free_decomposition (y : ℝ) :
    ∃ xp xm : ℝ, xp ≥ 0 ∧ xm ≥ 0 ∧ y = xp - xm := by
  use max y 0, max (-y) 0
  refine ⟨le_max_right y 0, le_max_right (-y) 0, ?_⟩
  by_cases h : y ≥ 0
  · simp only [max_eq_left h, neg_nonpos.mpr h, max_eq_right, sub_zero]
  · push_neg at h
    have hy_neg : -y > 0 := neg_pos.mpr h
    simp only [le_of_lt h, max_eq_right, le_of_lt hy_neg, max_eq_left,
      sub_neg_eq_add, zero_add]

/-- The decomposition of a free variable is surjective -/
theorem free_decomposition_surj (xp xm : ℝ) (_hp : xp ≥ 0) (_hm : xm ≥ 0) :
    ∃ y : ℝ, y = xp - xm :=
  ⟨xp - xm, rfl⟩

/-- max(x,0) - max(-x,0) = x for all x -/
theorem max_pos_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · have hneg : -x ≤ 0 := by linarith
    simp [hx, hneg]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -x := by linarith
    simp [hx', hneg]

end
