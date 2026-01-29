/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Row Operations for LP Reduction

This module defines the explicit row operation machinery that transforms a Standard Form LP
into a Reduced Form LP while preserving feasibility.

## Overview

The key structure is `RowReduction`, which packages:
- An invertible matrix `P` representing the row operations
- Its inverse `P_inv`
- Proofs that `P * P_inv = 1` and `P_inv * P = 1`
- A scalar `c_m` and proof that `P * c = (0, ..., 0, c_m)`

This explicit representation allows us to prove that feasibility is preserved:
a vector `y` is feasible for the original Standard Form iff it's feasible for
the resulting Reduced Form.

## Main Definitions

- `RowReduction`: Structure containing invertible row operation matrix and proofs
- `RowReduction.B`: The reduced constraint matrix `P * S.B`
- `RowReduction.toReducedForm`: Convert to a `ReducedForm` structure
- `RowReduction.feasible_iff`: Key theorem showing feasibility equivalence

-/

import LinearProgramming.ReducedForm
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open Matrix

/-! ## Row Reduction Structure -/

/-- Explicit row-reduction data: an invertible row operation `P` such that
    `P * B` and `P * c` give the reduced system with `c = (0,…,0,c_m)`.

    This packages the result of Gaussian elimination with all necessary proofs
    for establishing feasibility equivalence. -/
structure RowReduction (m p : ℕ) (S : StandardForm m p) (hm : m > 0) where
  /-- The row operation matrix -/
  P : Mat m m
  /-- The inverse of P -/
  P_inv : Mat m m
  /-- Proof that P * P_inv = identity -/
  P_mul_Pinv : P * P_inv = 1
  /-- Proof that P_inv * P = identity -/
  Pinv_mul_P : P_inv * P = 1
  /-- The scalar from the transformed RHS -/
  c_m : ℝ
  /-- Proof that P transforms c to the special form (0,...,0,c_m) -/
  c_eq : P.mulVec S.c = cVec m hm c_m

namespace RowReduction

variable {m p : ℕ} {S : StandardForm m p} {hm : m > 0}

/-- The reduced constraint matrix `P * S.B`. -/
def B (RR : RowReduction m p S hm) : Mat m p :=
  RR.P * S.B

/-- Convert a `RowReduction` to a `ReducedForm` by extracting the reduced matrix and scalar. -/
def toReducedForm (RR : RowReduction m p S hm) : ReducedForm m p :=
  { B := RR.B, c_m := RR.c_m }

/-! ## Invertibility Properties -/

private lemma P_isUnit (RR : RowReduction m p S hm) : IsUnit RR.P := by
  refine ⟨⟨RR.P, RR.P_inv, RR.P_mul_Pinv, RR.Pinv_mul_P⟩, rfl⟩

/-! ## Feasibility Equivalence -/

private lemma reducedForm_mulVec_eq (R : ReducedForm m p) (hm : m > 0) (y : Vec p) :
    R.B.mulVec y = R.c hm ↔
      (R.Bbar hm).mulVec y = 0 ∧ inner (𝕜 := ℝ) (R.a hm) y = R.c_m := by
  classical
  constructor
  · intro h
    have hrow : ∀ i : Fin m, (R.B.mulVec y) i = (R.c hm) i := by
      intro i
      simpa using congrArg (fun v => v i) h
    have hbar : (R.Bbar hm).mulVec y = 0 := by
      ext i
      have hrow' := hrow ⟨i.val, by omega⟩
      have hne : (⟨i.val, by omega⟩ : Fin m) ≠ lastRow m hm := by
        intro hEq
        have hval : i.val = m - 1 := by
          exact congrArg Fin.val hEq
        have hi : i.val < m - 1 := i.isLt
        omega
      have hczero : (R.c hm) ⟨i.val, by omega⟩ = 0 := by
        simp [ReducedForm.c, cVec_apply, hne]
      have hbar' :
          (R.Bbar hm).mulVec y i =
            (R.B.mulVec y) ⟨i.val, by omega⟩ := by
        rfl
      simpa [hbar'] using hrow'.trans hczero
    have hinner :
        inner (𝕜 := ℝ) (R.a hm) y = (R.B.mulVec y) (lastRow m hm) := by
      -- Expand the definitions of `a` and `mulVec`.
      simp [ReducedForm.a, Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
    have hclast : (R.c hm) (lastRow m hm) = R.c_m := by
      simp [ReducedForm.c, cVec_apply]
    have hlast : inner (𝕜 := ℝ) (R.a hm) y = R.c_m := by
      calc
        inner (𝕜 := ℝ) (R.a hm) y =
            (R.B.mulVec y) (lastRow m hm) := hinner
        _ = (R.c hm) (lastRow m hm) := hrow _
        _ = R.c_m := hclast
    exact ⟨hbar, hlast⟩
  · intro h
    rcases h with ⟨hbar, hlast⟩
    ext i
    by_cases hi : i = lastRow m hm
    · subst hi
      have hinner :
          inner (𝕜 := ℝ) (R.a hm) y = (R.B.mulVec y) (lastRow m hm) := by
        simp [ReducedForm.a, Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct,
          dotProduct_comm]
      have hclast : (R.c hm) (lastRow m hm) = R.c_m := by
        simp [ReducedForm.c, cVec_apply]
      simpa [hclast] using hinner.symm.trans hlast
    ·
      have hi' : i.val < m - 1 := by
        -- If `i` is not the last row, its value is strictly below `m-1`.
        have hne : i.val ≠ m - 1 := by
          intro hEq
          apply hi
          apply Fin.ext
          simpa [lastRow, hEq]
        omega
      let j : Fin (m - 1) := ⟨i.val, hi'⟩
      have hbar' :
          (R.Bbar hm).mulVec y j =
            (R.B.mulVec y) i := by
        rfl
      have hzero : (R.Bbar hm).mulVec y j = 0 := by
        simpa using congrArg (fun v => v j) hbar
      have hczero : (R.c hm) i = 0 := by
        simp [ReducedForm.c, cVec_apply, hi]
      simpa [hbar'] using hzero.trans hczero.symm

private lemma feasible_iff_mulVec (R : ReducedForm m p) (hm : m > 0)
    (y : Vec p) :
    R.feasible hm y ↔ R.B.mulVec y = R.c hm ∧ y ∈ nonnegOrthant p := by
  constructor
  · intro h
    rcases h with ⟨hbar, hinner, hy⟩
    have hmul : R.B.mulVec y = R.c hm :=
      (reducedForm_mulVec_eq (R := R) (hm := hm) (y := y)).2 ⟨hbar, hinner⟩
    exact ⟨hmul, hy⟩
  · intro h
    rcases h with ⟨hmul, hy⟩
    have h' :
        (R.Bbar hm).mulVec y = 0 ∧ inner (𝕜 := ℝ) (R.a hm) y = R.c_m :=
      (reducedForm_mulVec_eq (R := R) (hm := hm) (y := y)).1 hmul
    exact ⟨h'.1, h'.2, hy⟩

/-- **Key theorem**: A vector `y` is feasible for the original Standard Form LP
    if and only if it is feasible for the Reduced Form obtained via row operations.

    This justifies using the reduced form for feasibility checking. -/
theorem feasible_iff (RR : RowReduction m p S hm) (y : Vec p) :
    S.feasible y ↔ (RR.toReducedForm).feasible hm y := by
  classical
  let R := RR.toReducedForm
  constructor
  · intro hS
    rcases hS with ⟨hB, hy⟩
    have hmul : R.B.mulVec y = R.c hm := by
      calc
        R.B.mulVec y = (RR.P * S.B).mulVec y := by rfl
        _ = RR.P.mulVec (S.B.mulVec y) := by
          simpa using (Matrix.mulVec_mulVec RR.P S.B y)
        _ = RR.P.mulVec S.c := by simpa [hB]
        _ = cVec m hm RR.c_m := RR.c_eq
        _ = R.c hm := by rfl
    exact (feasible_iff_mulVec (R := R) (hm := hm) (y := y)).2 ⟨hmul, hy⟩
  · intro hR
    rcases (feasible_iff_mulVec (R := R) (hm := hm) (y := y)).1 hR with
      ⟨hmul, hy⟩
    have hmul' : S.B.mulVec y = S.c := by
      -- cancel `RR.P` using the explicit inverse
      have hP : RR.P.mulVec (S.B.mulVec y) = RR.P.mulVec S.c := by
        calc
          RR.P.mulVec (S.B.mulVec y) = (RR.P * S.B).mulVec y := by
            simpa using (Matrix.mulVec_mulVec RR.P S.B y).symm
          _ = R.B.mulVec y := by rfl
          _ = R.c hm := hmul
          _ = cVec m hm RR.c_m := by rfl
          _ = RR.P.mulVec S.c := RR.c_eq.symm
      have hP' : (RR.P_inv * RR.P).mulVec (S.B.mulVec y) =
          (RR.P_inv * RR.P).mulVec S.c := by
        -- apply `RR.P_inv.mulVec` and rewrite with `mulVec_mulVec`
        have hP' := congrArg (RR.P_inv.mulVec) hP
        simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hP'
      -- cancel the product using `P_inv * P = 1`
      calc
        S.B.mulVec y =
            (RR.P_inv * RR.P).mulVec (S.B.mulVec y) := by
          simpa [RR.Pinv_mul_P] using (Matrix.one_mulVec (S.B.mulVec y)).symm
        _ = (RR.P_inv * RR.P).mulVec S.c := hP'
        _ = S.c := by
          simpa [RR.Pinv_mul_P] using (Matrix.one_mulVec S.c)
    exact ⟨hmul', hy⟩

/-! ## Full Row Rank Preservation -/

private lemma fullRowRank_iff_vecMul_injective {m p : ℕ} (B : Mat m p) :
    fullRowRank B ↔ Function.Injective B.vecMul := by
  simpa [fullRowRank] using (Matrix.vecMul_injective_iff (M := B)).symm

/-- Row operations preserve full row rank: the reduced matrix has full row rank
    if and only if the original matrix does. -/
theorem fullRowRank_iff (RR : RowReduction m p S hm) :
    fullRowRank (RR.B) ↔ fullRowRank S.B := by
  classical
  -- Use the characterization via injectivity of `vecMul`.
  have hunit : IsUnit RR.P := RR.P_isUnit
  have hunit_inv : IsUnit RR.P_inv := by
    refine ⟨⟨RR.P_inv, RR.P, RR.Pinv_mul_P, RR.P_mul_Pinv⟩, rfl⟩
  -- `vecMul` for the reduced matrix is composition with `vecMul RR.P`.
  have hcomp : ∀ v : Fin m → ℝ, (RR.B).vecMul v = (S.B).vecMul ((RR.P).vecMul v) := by
    intro v
    -- `(vᵥ* P)ᵥ* B = vᵥ* (P * B)`
    simpa [RowReduction.B] using (Matrix.vecMul_vecMul v RR.P S.B).symm
  have hcancel : ∀ v : Fin m → ℝ, (RR.P).vecMul ((RR.P_inv).vecMul v) = v := by
    intro v
    calc
      (RR.P).vecMul ((RR.P_inv).vecMul v) = v ᵥ* (RR.P_inv * RR.P) := by
        simpa using (Matrix.vecMul_vecMul v RR.P_inv RR.P)
      _ = v ᵥ* (1 : Mat m m) := by simp [RR.Pinv_mul_P]
      _ = v := by simpa using (Matrix.vecMul_one v)
  constructor
  · intro h
    -- if `vecMul (P*B)` is injective, then `vecMul B` is injective
    have hRR : Function.Injective (RR.B).vecMul :=
      (fullRowRank_iff_vecMul_injective (B := RR.B)).1 h
    have hinj : Function.Injective (S.B).vecMul := by
      intro v w hvw
      -- apply `vecMul` with `P_inv` to both sides
      have hvw' : (RR.B).vecMul ((RR.P_inv).vecMul v) =
          (RR.B).vecMul ((RR.P_inv).vecMul w) := by
        calc
          (RR.B).vecMul ((RR.P_inv).vecMul v) =
              (S.B).vecMul ((RR.P).vecMul ((RR.P_inv).vecMul v)) := by
                simpa using (hcomp ((RR.P_inv).vecMul v))
          _ = (S.B).vecMul v := by simpa [hcancel v]
          _ = (S.B).vecMul w := hvw
          _ = (S.B).vecMul ((RR.P).vecMul ((RR.P_inv).vecMul w)) := by
                simpa [hcancel w]
          _ = (RR.B).vecMul ((RR.P_inv).vecMul w) := by
                simpa using (hcomp ((RR.P_inv).vecMul w)).symm
      have hEq : (RR.P_inv).vecMul v = (RR.P_inv).vecMul w := hRR hvw'
      -- cancel `P_inv` using its inverse
      have hEq' : v = w := by
        -- use injectivity of `vecMul P_inv`
        have hPinv : Function.Injective (RR.P_inv).vecMul :=
          Matrix.vecMul_injective_of_isUnit hunit_inv
        exact hPinv hEq
      exact hEq'
    exact (fullRowRank_iff_vecMul_injective (B := S.B)).2 hinj
  · intro h
    -- if `vecMul B` is injective, then `vecMul (P*B)` is injective
    have hB : Function.Injective (S.B).vecMul :=
      (fullRowRank_iff_vecMul_injective (B := S.B)).1 h
    have hinj : Function.Injective (RR.B).vecMul := by
      intro v w hvw
      have hPinj : Function.Injective (RR.P).vecMul :=
        Matrix.vecMul_injective_of_isUnit hunit
      have h' : (S.B).vecMul ((RR.P).vecMul v) =
          (S.B).vecMul ((RR.P).vecMul w) := by
        simpa [hcomp v, hcomp w] using hvw
      have hEq : (RR.P).vecMul v = (RR.P).vecMul w := hB h'
      exact hPinj hEq
    exact (fullRowRank_iff_vecMul_injective (B := RR.B)).2 hinj

end RowReduction
