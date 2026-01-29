/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# LP Reduction Pipeline

This module provides the complete reduction from Inequality Form LPs to Reduced Form,
including the row reduction algorithm that transforms Standard Form to Reduced Form.

## Main Definitions

- `rowReduceStandardForm`: Row-reduces a Standard Form LP to Reduced Form
- `rowReduceStandardForm_correct`: Proves feasibility equivalence for Standard Form
- `fullReduction`: Complete reduction from Inequality Form to Reduced Form
- `fullReduction_correct`: Proves feasibility equivalence for the full pipeline

-/

import LinearProgramming.RowOperations
import LinearProgramming.Equivalence

noncomputable section

open Matrix

-- Re-export definitions for convenience
export InequalityForm (feasible isFeasible)
export StandardForm (feasible isFeasible)

/-! ## Row Reduction for Standard Form LPs -/

/--
Row-reduce a Standard Form LP to Reduced Form.

Given a Standard Form LP with `By = c, y ≥ 0`, this constructs a `RowReduction` containing
an invertible matrix `P` such that `P * c = (0, ..., 0, c_m)`.

**Algorithm**:
- If `c = 0`: Use identity matrix, `c_m = 0`
- If `c ≠ 0`: Build a basis with `c` at the last position, use change-of-basis matrix, `c_m = 1`
-/
def rowReduceStandardForm {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
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

/-- Row reduction preserves feasibility: the original Standard Form LP is feasible
    if and only if the resulting Reduced Form LP is feasible. -/
theorem rowReduceStandardForm_correct {m p : ℕ} (S : StandardForm m p) (hm : m > 0) :
    S.isFeasible ↔ ∃ y, (rowReduceStandardForm S hm).toReducedForm.feasible hm y := by
  let RR := rowReduceStandardForm S hm
  constructor
  · intro hS
    rcases hS with ⟨y, hy⟩
    exact ⟨y, (RowReduction.feasible_iff (RR := RR) (y := y)).1 hy⟩
  · intro hR
    rcases hR with ⟨y, hy⟩
    exact ⟨y, (RowReduction.feasible_iff (RR := RR) (y := y)).2 hy⟩

/-! ## Full Reduction Pipeline -/

/-- Full reduction from Inequality Form to Reduced Form.

This applies the complete reduction pipeline:
1. Convert `Ax ≤ b` to Standard Form `By = c, y ≥ 0` using slack variables
2. Apply row reduction to get Reduced Form with `c = (0,...,0,c_m)` -/
def fullReduction {m n : ℕ} (P : InequalityForm m n) (hm : m > 0) : ReducedForm m (2 * n + m) :=
  (rowReduceStandardForm (toStandardForm P) hm).toReducedForm

/-- The full reduction preserves feasibility: the original Inequality Form LP is feasible
    if and only if the resulting Reduced Form LP is feasible. -/
theorem fullReduction_correct {m n : ℕ} (P : InequalityForm m n) (hm : m > 0) :
    P.isFeasible ↔ ∃ y, (fullReduction P hm).feasible hm y := by
  calc P.isFeasible
      ↔ (toStandardForm P).isFeasible := reduction_correct P
    _ ↔ ∃ y, (fullReduction P hm).feasible hm y :=
        (rowReduceStandardForm_correct (toStandardForm P) hm)

/-! ## Solution Recovery from Reduced Form -/

/-- If `y` is feasible for the reduced form of `P`, then `extractX y` is feasible for `P`. -/
theorem fullReduction_extractX_feasible {m n : ℕ} (P : InequalityForm m n) (hm : m > 0)
    {y : Vec (2 * n + m)} :
    (fullReduction P hm).feasible hm y → P.feasible (extractX y) := by
  intro hy
  let S := toStandardForm P
  let RR := rowReduceStandardForm S hm
  have hyS : S.feasible y := (RowReduction.feasible_iff (RR := RR) (y := y)).2 hy
  exact reduction_backward (P := P) (y := y) hyS

end
