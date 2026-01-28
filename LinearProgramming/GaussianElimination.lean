/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Abstract Gaussian Elimination

This module implements abstract Gaussian elimination for transforming a Standard Form LP
into a Reduced Form LP.

## Overview

Given a Standard Form LP with constraints `By = c` and `y ≥ 0`, Gaussian elimination
finds an invertible matrix `P` such that `P * c = (0, ..., 0, c_m)`. The algorithm:

1. **Trivial case** (`c = 0`): Use `P = I` (identity matrix) with `c_m = 0`

2. **Nontrivial case** (`c ≠ 0`): Construct a basis of `ℝ^m` with `c` at the last position,
   then use the change-of-basis matrix as `P`

The construction is noncomputable because it relies on:
- Classical logic for case analysis
- Basis extension (which uses choice)
- Permutation to place `c` at the desired position

## Main Definitions

- `gaussianElimination`: Constructs a `RowReduction` from a `StandardForm`
- `gaussianElimination_correct`: Proves feasibility equivalence

-/

import LinearProgramming.RowOperations

noncomputable section

open Matrix

/--
Abstract Gaussian elimination: row-reduces `[B | c]` so that `c = (0, …, 0, c_m)`.

Given a Standard Form LP, this constructs a `RowReduction` containing:
- An invertible matrix `P` and its inverse `P_inv`
- A scalar `c_m` such that `P * c = (0, ..., 0, c_m)`

**Algorithm**:
- If `c = 0`: Use identity matrix, `c_m = 0`
- If `c ≠ 0`: Build a basis with `c` at the last position, use change-of-basis matrix, `c_m = 1`
-/
def gaussianElimination {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
    RowReduction m p S hm := by
  classical
  -- Handle the trivial right-hand side separately.
  by_cases hc : S.c = 0
  ·
    refine
      { P := 1
        P_inv := 1
        P_mul_Pinv := by simp
        Pinv_mul_P := by simp
        c_m := 0
        c_eq := by
          have h : (1 : Mat m m).mulVec S.c = S.c := by
            simpa using (Matrix.one_mulVec S.c)
          simpa [hc, cVec_zero] using h }
  ·
    -- Nontrivial right-hand side: build a row-equivalent system with `c = (0,…,0,1)`.
    have hb_ex : ∃ b : Module.Basis (Fin m) ℝ (Vec m), b (lastRow m hm) = S.c :=
      exists_basis_with_last (m := m) hm S.c hc
    let b : Module.Basis (Fin m) ℝ (Vec m) := Classical.choose hb_ex
    have hb : b (lastRow m hm) = S.c := Classical.choose_spec hb_ex
    let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)).toLinearEquiv
    let φ : Vec m ≃ₗ[ℝ] Vec m := b.equivFun.trans e.symm
    have hφc : φ S.c = cVec m hm 1 := by
      -- `b` sends `lastRow` to `S.c`, so `b.equivFun` sends `S.c` to the last basis vector.
      have hbfun :
          b.equivFun S.c = (fun i => if i = lastRow m hm then (1 : ℝ) else 0) := by
        ext i
        -- rewrite `S.c` as `b (lastRow ...)`
        simpa [hb, eq_comm] using (b.equivFun_self (i := lastRow m hm) (j := i))
      simp [φ, cVec, hbfun, e, EuclideanSpace.equiv, WithLp.coe_symm_linearEquiv]
    let v := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    let P : Mat m m := LinearMap.toMatrix v v φ.toLinearMap
    let P_inv : Mat m m := LinearMap.toMatrix v v φ.symm.toLinearMap
    have hPPinv : P * P_inv = 1 := by
      have hcomp :
          φ.toLinearMap.comp φ.symm.toLinearMap =
            (LinearMap.id : Vec m →ₗ[ℝ] Vec m) := by
        ext x; simp
      have hmat :
          LinearMap.toMatrix v v (φ.toLinearMap.comp φ.symm.toLinearMap) =
            P * P_inv := by
        simpa [P, P_inv] using
          (LinearMap.toMatrix_comp (v₁ := v) (v₂ := v) (v₃ := v)
            (φ.toLinearMap) (φ.symm.toLinearMap))
      calc
        P * P_inv = LinearMap.toMatrix v v (φ.toLinearMap.comp φ.symm.toLinearMap) := hmat.symm
        _ = LinearMap.toMatrix v v (LinearMap.id : Vec m →ₗ[ℝ] Vec m) := by
          simpa [hcomp]
        _ = 1 := LinearMap.toMatrix_id (v₁ := v)
    have hPinvP : P_inv * P = 1 := by
      have hcomp :
          φ.symm.toLinearMap.comp φ.toLinearMap =
            (LinearMap.id : Vec m →ₗ[ℝ] Vec m) := by
        ext x; simp
      have hmat :
          LinearMap.toMatrix v v (φ.symm.toLinearMap.comp φ.toLinearMap) =
            P_inv * P := by
        simpa [P, P_inv] using
          (LinearMap.toMatrix_comp (v₁ := v) (v₂ := v) (v₃ := v)
            (φ.symm.toLinearMap) (φ.toLinearMap))
      calc
        P_inv * P = LinearMap.toMatrix v v (φ.symm.toLinearMap.comp φ.toLinearMap) := hmat.symm
        _ = LinearMap.toMatrix v v (LinearMap.id : Vec m →ₗ[ℝ] Vec m) := by
          simpa [hcomp]
        _ = 1 := LinearMap.toMatrix_id (v₁ := v)
    have hPmul : P.mulVec S.c = φ S.c := by
      simpa [P] using (toMatrix_mulVec_basisFun (f := φ.toLinearMap) (x := S.c))
    have hφc_fun : (φ S.c : Fin m → ℝ) = (cVec m hm 1 : Fin m → ℝ) := by
      funext i
      have h := congrArg (fun v => v i) hφc
      simpa using h
    have hceq : P.mulVec S.c = cVec m hm 1 := by
      calc
        P.mulVec S.c = (φ S.c : Fin m → ℝ) := hPmul
        _ = (cVec m hm 1 : Fin m → ℝ) := hφc_fun
    exact
      { P := P
        P_inv := P_inv
        P_mul_Pinv := hPPinv
        Pinv_mul_P := hPinvP
        c_m := 1
        c_eq := hceq }

/-- Gaussian elimination preserves feasibility: the original Standard Form LP is feasible
    if and only if the resulting Reduced Form LP is feasible. -/
theorem gaussianElimination_correct {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
    S.isFeasible ↔ ∃ y, (gaussianElimination S hm).toReducedForm.feasible hm y := by
  let RR := gaussianElimination S hm
  constructor
  · intro hS
    rcases hS with ⟨y, hy⟩
    exact ⟨y, (RowReduction.feasible_iff (RR := RR) (y := y)).1 hy⟩
  · intro hR
    rcases hR with ⟨y, hy⟩
    exact ⟨y, (RowReduction.feasible_iff (RR := RR) (y := y)).2 hy⟩

end
