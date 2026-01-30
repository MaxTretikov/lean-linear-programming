/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linear Programming Definitions

Basic definitions for linear programs: vectors, matrices, standard form, and general form.
-/

import LinearAlgebraHelpers.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

-- Vec, Mat, nonnegOrthant are imported from LinearAlgebraHelpers.Defs

/-! ## Sign Constraints and Optimization Direction -/

/-- Sign constraint on a variable -/
inductive SignConstraint where
  | nonneg     -- y ≥ 0
  | nonpos     -- y ≤ 0
  | free       -- y unrestricted
  deriving DecidableEq, Repr

/-- Optimization direction -/
inductive OptDirection where
  | maximize
  | minimize
  deriving DecidableEq, Repr

/-- A vector y satisfies its sign constraint -/
def satisfiesSign (σ : SignConstraint) (y : ℝ) : Prop :=
  match σ with
  | .nonneg => 0 ≤ y
  | .nonpos => y ≤ 0
  | .free => True

/-! ## Standard Form LP -/

/-- A linear program in standard form:
    maximize c^T x
    subject to Ax ≤ b
               x ≥ 0 -/
structure StandardFormLP (n m : ℕ) where
  /-- Objective function coefficients -/
  c : Vec n
  /-- Constraint matrix -/
  A : Mat m n
  /-- Right-hand side of constraints -/
  b : Vec m

namespace StandardFormLP

variable {n m : ℕ}

/-- A vector x is feasible for a standard form LP if Ax ≤ b and x ≥ 0 -/
def IsFeasible (lp : StandardFormLP n m) (x : Vec n) : Prop :=
  (∀ i, (lp.A *ᵥ x) i ≤ lp.b i) ∧ x ∈ nonnegOrthant n

/-- The objective value c^T x -/
def objective (lp : StandardFormLP n m) (x : Vec n) : ℝ :=
  inner (𝕜 := ℝ) lp.c x

/-- x* is optimal if it's feasible and maximizes the objective -/
def IsOptimal (lp : StandardFormLP n m) (x : Vec n) : Prop :=
  lp.IsFeasible x ∧ ∀ y, lp.IsFeasible y → lp.objective y ≤ lp.objective x

/-- The feasible set of a standard form LP -/
def feasibleSet (lp : StandardFormLP n m) : Set (Vec n) :=
  {x | lp.IsFeasible x}

/-- The LP is feasible if its feasible set is nonempty -/
def isFeasible (lp : StandardFormLP n m) : Prop := ∃ x, lp.IsFeasible x

end StandardFormLP

/-! ## General Form LP -/

/-- A general linear program with mixed constraints:
    optimize c^T y
    subject to A₁ y ≤ b₁
               A₂ y ≥ b₂
               A₃ y = b₃
               y_j has sign constraint σ_j -/
structure GeneralLP (n m₁ m₂ m₃ : ℕ) where
  /-- Optimization direction -/
  dir : OptDirection
  /-- Objective function coefficients -/
  c : Vec n
  /-- Constraint matrix for ≤ constraints -/
  A₁ : Mat m₁ n
  /-- RHS for ≤ constraints -/
  b₁ : Vec m₁
  /-- Constraint matrix for ≥ constraints -/
  A₂ : Mat m₂ n
  /-- RHS for ≥ constraints -/
  b₂ : Vec m₂
  /-- Constraint matrix for = constraints -/
  A₃ : Mat m₃ n
  /-- RHS for = constraints -/
  b₃ : Vec m₃
  /-- Sign constraints for each variable -/
  σ : Fin n → SignConstraint

namespace GeneralLP

variable {n m₁ m₂ m₃ : ℕ}

/-- A vector y is feasible for a general LP -/
def IsFeasible (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) : Prop :=
  (∀ i, (lp.A₁ *ᵥ y) i ≤ lp.b₁ i) ∧
  (∀ i, (lp.A₂ *ᵥ y) i ≥ lp.b₂ i) ∧
  (∀ i, (lp.A₃ *ᵥ y) i = lp.b₃ i) ∧
  (∀ j, satisfiesSign (lp.σ j) (y j))

/-- The objective value c^T y -/
def objective (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) : ℝ :=
  inner (𝕜 := ℝ) lp.c y

/-- y* is optimal if it's feasible and optimizes the objective -/
def IsOptimal (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) : Prop :=
  lp.IsFeasible y ∧
  match lp.dir with
  | .maximize => ∀ z, lp.IsFeasible z → lp.objective z ≤ lp.objective y
  | .minimize => ∀ z, lp.IsFeasible z → lp.objective y ≤ lp.objective z

/-- The LP is feasible if there exists a feasible solution -/
def isFeasible (lp : GeneralLP n m₁ m₂ m₃) : Prop := ∃ y, lp.IsFeasible y

end GeneralLP

/-! ## Simplified LP (intermediate form) -/

/-- A simplified LP with only ≤ constraints -/
structure SimplifiedLP (n m : ℕ) where
  dir : OptDirection
  c : Vec n
  A : Mat m n
  b : Vec m
  σ : Fin n → SignConstraint

namespace SimplifiedLP

variable {n m : ℕ}

def IsFeasible (lp : SimplifiedLP n m) (y : Vec n) : Prop :=
  (∀ i, (lp.A *ᵥ y) i ≤ lp.b i) ∧
  (∀ j, satisfiesSign (lp.σ j) (y j))

def objective (lp : SimplifiedLP n m) (y : Vec n) : ℝ :=
  inner (𝕜 := ℝ) lp.c y

/-- The LP is feasible if there exists a feasible solution -/
def isFeasible (lp : SimplifiedLP n m) : Prop := ∃ y, lp.IsFeasible y

end SimplifiedLP

/-! ## Helper functions for combining constraints -/

/-- Combine two constraint matrices by stacking rows -/
def stackMatrices {m₁ m₂ n : ℕ} (A₁ : Mat m₁ n) (A₂ : Mat m₂ n) : Mat (m₁ + m₂) n :=
  fun i j =>
    if h : i.val < m₁ then
      A₁ ⟨i.val, h⟩ j
    else
      A₂ ⟨i.val - m₁, by omega⟩ j

/-- Combine two RHS vectors by appending -/
def appendVecs {m₁ m₂ : ℕ} (b₁ : Vec m₁) (b₂ : Vec m₂) : Vec (m₁ + m₂) :=
  (WithLp.equiv 2 (Fin (m₁ + m₂) → ℝ)).symm fun i =>
    if h : i.val < m₁ then
      b₁ ⟨i.val, h⟩
    else
      b₂ ⟨i.val - m₁, by omega⟩

@[simp]
lemma appendVecs_apply {m₁ m₂ : ℕ} (b₁ : Vec m₁) (b₂ : Vec m₂) (i : Fin (m₁ + m₂)) :
    appendVecs b₁ b₂ i = if h : i.val < m₁ then b₁ ⟨i.val, h⟩ else b₂ ⟨i.val - m₁, by omega⟩ := by
  rfl

/-- Count the number of free variables in a sign constraint vector -/
def countFree (n : ℕ) (σ : Fin n → SignConstraint) : ℕ :=
  (Finset.univ.filter (fun j => σ j = .free)).card

/-! ## Standard Form (Equality Form)

The canonical form for linear programs:
    Find y such that By = c and y ≥ 0

This is the "equality standard form" (ESF). Any LP can be converted to this form.
-/

/-- A linear program in standard form (equality form):
    Find y such that By = c and y ≥ 0 -/
structure StandardForm (m p : ℕ) where
  /-- Constraint matrix -/
  B : Mat m p
  /-- Right-hand side -/
  c : Vec m

namespace StandardForm

variable {m p : ℕ}

/-- A vector y is feasible if By = c and y ≥ 0 -/
def feasible (S : StandardForm m p) (y : Vec p) : Prop :=
  S.B.mulVec y = S.c ∧ y ∈ nonnegOrthant p

/-- The LP is feasible if there exists a feasible solution -/
def isFeasible (S : StandardForm m p) : Prop := ∃ y, S.feasible y

end StandardForm

/-! ## Inequality Form (Intermediate)

The inequality form: Find x such that Ax ≤ b

This is an intermediate form. It can be converted to standard form by adding
slack variables: define s = b - Ax, then Ax + s = b with s ≥ 0.

Note: This form does NOT require x ≥ 0. For the full conversion to standard form,
we also decompose each free variable x as x = x⁺ - x⁻ where x⁺, x⁻ ≥ 0.
-/

/-- A linear program in inequality form (intermediate):
    Find x such that Ax ≤ b -/
structure InequalityForm (m n : ℕ) where
  /-- Constraint matrix -/
  A : Mat m n
  /-- Right-hand side -/
  b : Vec m

namespace InequalityForm

variable {m n : ℕ}

/-- A vector x is feasible if Ax ≤ b componentwise -/
def feasible (P : InequalityForm m n) (x : Vec n) : Prop :=
  ∀ i : Fin m, (P.A.mulVec x) i ≤ P.b i

/-- The LP is feasible if there exists a feasible solution -/
def isFeasible (P : InequalityForm m n) : Prop := ∃ x, P.feasible x

end InequalityForm

/-! ## Reduced Form for Linear Programs -/

/-!
# Reduced Form for Linear Programs

This module defines the **Reduced Form** representation of a linear program, which is
the result of applying Gaussian elimination to a Standard Form LP.

## What is Reduced Form?

Given a Standard Form LP with constraints `By = c` and `y ≥ 0`, Gaussian elimination
transforms the augmented system `[B | c]` so that the right-hand side vector `c`
becomes the special form `(0, 0, ..., 0, c_m)` — all zeros except possibly the last entry.

This transformation is achieved by finding an invertible matrix `P` such that
`P * c = (0, ..., 0, c_m)`. The same matrix `P` is applied to `B`, giving us
the reduced constraint matrix `P * B`.

## How Reduced Form Differs from Standard Form

| Aspect         | Standard Form                | Reduced Form                           |
|----------------|------------------------------|----------------------------------------|
| Structure      | `By = c, y ≥ 0`              | `B̄y = 0, ⟪a,y⟫ = c_m, y ≥ 0`          |
| RHS            | Full vector `c : Vec m`      | Single scalar `c_m : ℝ`                |
| Constraints    | `m` equality constraints     | `m-1` homogeneous + 1 affine           |
| Matrix         | `B : Mat m p`                | `B̄ : Mat (m-1) p` and `a : Vec p`     |

The reduced form decomposes the original system into:
- **B̄** (pronounced "B-bar"): The first `m-1` rows of the reduced matrix, defining
  a homogeneous system `B̄y = 0`
- **a**: The last row of the reduced matrix, defining a single affine constraint
  `⟪a, y⟫ = c_m`

## Why Reduced Form is Useful

1. **Cone-based feasibility**: The homogeneous constraints `B̄y = 0` with `y ≥ 0`
   define a polyhedral cone. Finding a feasible solution reduces to finding a ray
   in this cone that can be scaled to satisfy `⟪a, y⟫ = c_m`.

2. **Infeasibility detection**: If `c_m = 0` and the reduced matrix has full row rank,
   the only solution to `B̄y = 0, ⟪a,y⟫ = 0, y ≥ 0` is `y = 0`, which means the
   original system is infeasible (assuming `c ≠ 0`).

3. **Algorithmic simplicity**: Working with a single scalar constraint `c_m`
   instead of a full vector `c` simplifies the feasibility algorithm.

## Relationship to Standard LP Terminology

"Reduced Form" is **not** a standard named conversion in linear programming literature.
It is a project-specific term for this particular transformation. The closest standard
concepts are:
- **Row echelon form**: What Gaussian elimination typically produces
- **Reduced row echelon form (RREF)**: A more normalized form with leading 1s

The key difference is that our "reduced form" specifically targets the RHS vector `c`,
not the coefficient matrix `B`, and the goal is to isolate a single scalar rather
than achieve a canonical matrix form.

## Main Definitions

- `ReducedForm`: The data structure containing the reduced matrix `B` and scalar `c_m`
- `ReducedForm.Bbar`: Extracts the first `m-1` rows (homogeneous part)
- `ReducedForm.a`: Extracts the last row (affine constraint coefficients)
- `ReducedForm.feasible`: The feasibility predicate for reduced form
- `fullRowRank`: Predicate for matrices with linearly independent rows
-/

/-! ## Helper Definitions -/

/-- Index of the last row in an `m`-row matrix, used to isolate the scalar `c_m`.
    Requires `m > 0` to ensure the matrix is non-empty. -/
def lastRow (m : ℕ) (hm : m > 0) : Fin m := ⟨m - 1, by omega⟩

/-- Vector `(0, ..., 0, c_m)` with all entries zero except the last.
    This is the target form for the RHS after Gaussian elimination. -/
def cVec (m : ℕ) (hm : m > 0) (c_m : ℝ) : Vec m :=
  ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)).toLinearEquiv).symm
    (fun i => if i = lastRow m hm then c_m else 0)

@[simp] lemma cVec_apply {m : ℕ} (hm : m > 0) (c_m : ℝ) (i : Fin m) :
    cVec m hm c_m i = if i = lastRow m hm then c_m else 0 := by
  simp [cVec, EuclideanSpace.equiv, PiLp.toLp_apply]

@[simp] lemma cVec_zero {m : ℕ} (hm : m > 0) : cVec m hm 0 = 0 := by
  ext i
  simp [cVec_apply]

/-! ## Reduced Form Structure -/

/-- A linear program in **reduced form**.

After Gaussian elimination on a Standard Form LP `By = c, y ≥ 0`, we obtain:
- A reduced matrix `B : Mat m p` (the original `B` left-multiplied by an invertible `P`)
- A scalar `c_m : ℝ` (the last entry of the transformed RHS)

The feasibility condition becomes: `B̄y = 0 ∧ ⟪a, y⟫ = c_m ∧ y ≥ 0`, where
`B̄` is the first `m-1` rows and `a` is the last row of `B`. -/
structure ReducedForm (m p : ℕ) where
  /-- The reduced constraint matrix (after row operations) -/
  B : Mat m p
  /-- The scalar from the last entry of the transformed RHS vector -/
  c_m : ℝ

namespace ReducedForm

variable {m p : ℕ}

/-- The transformed RHS vector `(0, ..., 0, c_m)` as a full vector.
    This is useful for stating equivalence with the original Standard Form. -/
def c (R : ReducedForm m p) (hm : m > 0) : Vec m :=
  cVec m hm R.c_m

/-- The first `m-1` rows of the reduced matrix, defining the homogeneous system `B̄y = 0`. -/
def Bbar (R : ReducedForm m p) (hm : m > 0) : Mat (m - 1) p :=
  fun i j => R.B ⟨i.val, by omega⟩ j

/-- The last row of the reduced matrix, used as the coefficient vector in `⟪a, y⟫ = c_m`. -/
def a (R : ReducedForm m p) (hm : m > 0) : Vec p :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)).symm (fun j => R.B (lastRow m hm) j)

@[simp] lemma a_apply (R : ReducedForm m p) (hm : m > 0) (j : Fin p) :
    R.a hm j = R.B (lastRow m hm) j := by
  simp [ReducedForm.a, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- A vector `y` is **feasible** for a reduced form LP if:
    1. `B̄y = 0` (homogeneous constraints from first `m-1` rows)
    2. `⟪a, y⟫ = c_m` (single affine constraint from last row)
    3. `y ≥ 0` (nonnegativity) -/
def feasible (R : ReducedForm m p) (hm : m > 0) (y : Vec p) : Prop :=
  (R.Bbar hm).mulVec y = 0 ∧ inner (𝕜 := ℝ) (R.a hm) y = R.c_m ∧ y ∈ nonnegOrthant p

/-- The reduced form LP is feasible if there exists a feasible solution. -/
def isFeasible (R : ReducedForm m p) (hm : m > 0) : Prop := ∃ y, R.feasible hm y

end ReducedForm

/-! ## Full Row Rank -/

/-- A matrix has **full row rank** if its rows are linearly independent.
    This is equivalent to the row space having dimension equal to the number of rows,
    or equivalently, `vecMul` being injective. -/
def fullRowRank {m p : ℕ} (B : Mat m p) : Prop :=
  LinearIndependent ℝ B.row

/-! ## Standalone Feasibility Predicate -/

open scoped RealInnerProductSpace

/-- Feasibility predicate in "paper notation": `By = 0, ⟪a, y⟫ = c, y ≥ 0`.

This standalone function takes the constraint matrix, affine constraint vector,
scalar RHS, and candidate solution as separate arguments. It is equivalent to
`ReducedForm.feasible` but matches the notation commonly used in LP literature. -/
def feasibleReduced {q p : ℕ} (B : Mat q p) (a : Vec p) (c : ℝ) (y : Vec p) : Prop :=
  B.mulVec y = 0 ∧ inner (𝕜 := ℝ) a y = c ∧ y ∈ nonnegOrthant p

/-- The `ReducedForm.feasible` predicate matches the paper's notation:
    `R.feasible hm y ↔ feasibleReduced (R.Bbar hm) (R.a hm) R.c_m y` -/
theorem reduced_form_matches_paper {m p : ℕ} (R : ReducedForm m p) (hm : m > 0) (y : Vec p) :
    R.feasible hm y ↔ feasibleReduced (R.Bbar hm) (R.a hm) R.c_m y := Iff.rfl

/-! ## Technical Lemmas -/

private lemma vec_finrank_eq (m : ℕ) : Module.finrank ℝ (Vec m) = m := by
  simp [Vec, finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m)]

/-! ## Constraint Independence via Row Space Basis -/

/-- The set of row vectors of a matrix. -/
def rowSet {m p : ℕ} (B : Mat m p) : Set (Vec p) :=
  Set.range (fun i : Fin m =>
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)).symm (B i))

/-- The row space of a matrix, as a submodule of `Vec p`. -/
def rowSpan {m p : ℕ} (B : Mat m p) : Submodule ℝ (Vec p) :=
  Submodule.span ℝ (rowSet B)

/-- A basis of the row space, viewed as constraint vectors in the ambient space. -/
noncomputable def rowBasisFun {m p : ℕ} (B : Mat m p) :
    Module.Basis.ofVectorSpaceIndex ℝ (rowSpan B) → Vec p :=
  fun i => (i : Vec p)

lemma rowBasisFun_linearIndependent {m p : ℕ} (B : Mat m p) :
    LinearIndependent ℝ (rowBasisFun B) := by
  classical
  let W := rowSpan B
  have hliW : LinearIndependent ℝ ((↑) : Module.Basis.ofVectorSpaceIndex ℝ W → W) := by
    simpa using (Module.Basis.ofVectorSpaceIndex.linearIndependent (K := ℝ) (V := W))
  -- Coercion from the submodule to the ambient space preserves linear independence.
  simpa [rowBasisFun, W] using
    (hliW.map' (Submodule.subtype W) (by simp))

lemma rowBasisFun_span_eq_rowSpan {m p : ℕ} (B : Mat m p) :
    Submodule.span ℝ (Set.range (rowBasisFun B)) = rowSpan B := by
  classical
  let W := rowSpan B
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ W) ℝ W :=
    Module.Basis.ofVectorSpace ℝ W
  have hset :
      Set.range (rowBasisFun B) = (Submodule.subtype W) '' Set.range b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simp [rowBasisFun, b, Module.Basis.coe_ofVectorSpace]
    · rintro ⟨x0, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [rowBasisFun, b, Module.Basis.coe_ofVectorSpace]
  calc
    Submodule.span ℝ (Set.range (rowBasisFun B)) =
        Submodule.span ℝ ((Submodule.subtype W) '' Set.range b) := by
          rw [hset]
    _ = Submodule.map (Submodule.subtype W)
          (Submodule.span ℝ (Set.range b)) := by
          symm
          exact (Submodule.map_span (f := Submodule.subtype W) (s := Set.range b))
    _ = Submodule.map (Submodule.subtype W) ⊤ := by
          rw [b.span_eq]
    _ = W := by
          exact Submodule.map_subtype_top W

/-- A finite basis for the row space, viewed in the ambient space. -/
noncomputable def rowBasisVec {m p : ℕ} (B : Mat m p) :
    Fin (Module.finrank ℝ (rowSpan B)) → Vec p :=
  fun i => ((Module.finBasis ℝ (rowSpan B) i : rowSpan B) : Vec p)

lemma rowBasisVec_linearIndependent {m p : ℕ} (B : Mat m p) :
    LinearIndependent ℝ (rowBasisVec B) := by
  classical
  let W := rowSpan B
  let b : Module.Basis (Fin (Module.finrank ℝ W)) ℝ W := Module.finBasis ℝ W
  have hliW : LinearIndependent ℝ (fun i => (b i : W)) := b.linearIndependent
  simpa [rowBasisVec, b, W] using
    (hliW.map' (Submodule.subtype W) (by simp))

lemma rowBasisVec_span_eq_rowSpan {m p : ℕ} (B : Mat m p) :
    Submodule.span ℝ (Set.range (rowBasisVec B)) = rowSpan B := by
  classical
  let W := rowSpan B
  let b : Module.Basis (Fin (Module.finrank ℝ W)) ℝ W := Module.finBasis ℝ W
  have hset :
      Set.range (rowBasisVec B) = (Submodule.subtype W) '' Set.range b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simp [rowBasisVec, b, W]
    · rintro ⟨x0, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [rowBasisVec, b, W]
  calc
    Submodule.span ℝ (Set.range (rowBasisVec B)) =
        Submodule.span ℝ ((Submodule.subtype W) '' Set.range b) := by
          rw [hset]
    _ = Submodule.map (Submodule.subtype W) (Submodule.span ℝ (Set.range b)) := by
          symm
          exact (Submodule.map_span (f := Submodule.subtype W) (s := Set.range b))
    _ = Submodule.map (Submodule.subtype W) ⊤ := by
          rw [b.span_eq]
    _ = W := by
          exact Submodule.map_subtype_top W

/-- A matrix whose rows are a basis of the row space. -/
noncomputable def rowBasisMat {m p : ℕ} (B : Mat m p) :
    Mat (Module.finrank ℝ (rowSpan B)) p :=
  fun i => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)) (rowBasisVec B i)

lemma rowBasisMat_fullRowRank {m p : ℕ} (B : Mat m p) :
    fullRowRank (rowBasisMat B) := by
  classical
  have hli : LinearIndependent ℝ (rowBasisVec B) :=
    rowBasisVec_linearIndependent (B := B)
  have hker :
      LinearMap.ker
          ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)).toLinearMap) = ⊥ := by
    simpa using
      (LinearMap.ker_eq_bot_of_injective
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)).injective)
  have hli' :
      LinearIndependent ℝ
        (fun i =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin p)) (rowBasisVec B i)) := by
    simpa using (hli.map' _ hker)
  simpa [fullRowRank, rowBasisMat] using hli'

lemma rowSpan_rowBasisMat {m p : ℕ} (B : Mat m p) :
    rowSpan (rowBasisMat B) = rowSpan B := by
  classical
  have hset : rowSet (rowBasisMat B) = Set.range (rowBasisVec B) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      simp [rowBasisMat]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp [rowBasisMat]
  calc
    rowSpan (rowBasisMat B) =
        Submodule.span ℝ (rowSet (rowBasisMat B)) := rfl
    _ = Submodule.span ℝ (Set.range (rowBasisVec B)) := by
        rw [hset]
    _ = rowSpan B := rowBasisVec_span_eq_rowSpan (B := B)

/-- There exists a full row rank matrix with the same row space as `B`. -/
lemma exists_fullRowRank_rowSpan_eq {m p : ℕ} (B : Mat m p) :
    ∃ q : ℕ, ∃ B' : Mat q p, fullRowRank B' ∧ rowSpan B' = rowSpan B := by
  refine ⟨Module.finrank ℝ (rowSpan B), rowBasisMat B, ?_, ?_⟩
  · exact rowBasisMat_fullRowRank (B := B)
  · exact rowSpan_rowBasisMat (B := B)

/-- Given a nonzero vector `c`, there exists a basis of `Vec m` with `c` at the last position.
    This is the key lemma enabling Gaussian elimination to place `c` in the desired form. -/
lemma exists_basis_with_last {m : ℕ} (hm : m > 0) (c : Vec m) (hc : c ≠ 0) :
    ∃ b : Module.Basis (Fin m) ℝ (Vec m), b (lastRow m hm) = c := by
  classical
  let s : Set (Vec m) := {c}
  have hs : LinearIndepOn ℝ (fun x : Vec m => x) s := by
    -- A singleton of a nonzero vector is linearly independent.
    simp [s, (linearIndepOn_singleton_iff (R := ℝ) (v := fun x : Vec m => x) (i := c)).2 hc]
  let b0 : Module.Basis (hs.extend (Set.subset_univ s)) ℝ (Vec m) := Module.Basis.extend hs
  have hc_mem : c ∈ hs.extend (Set.subset_univ s) := by
    exact hs.subset_extend _ (by simp [s])
  let ic : hs.extend (Set.subset_univ s) := ⟨c, hc_mem⟩
  have hb0c : b0 ic = c := by
    -- `Basis.extend` is the inclusion on its index set.
    have hinc : b0 ic = (ic : Vec m) := by
      simpa [b0] using (Module.Basis.extend_apply_self (hs := hs) ic)
    simpa [ic] using hinc
  have hfinite : (Set.range (EuclideanSpace.basisFun (Fin m) ℝ)).Finite := by
    exact Set.finite_range (EuclideanSpace.basisFun (Fin m) ℝ)
  have hspan : Submodule.span ℝ (Set.range (EuclideanSpace.basisFun (Fin m) ℝ)) = ⊤ := by
    exact (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.span_eq
  haveI : Finite (hs.extend (Set.subset_univ s)) :=
    basis_finite_of_finite_spans (R := ℝ) (M := Vec m) hfinite hspan b0
  letI : Fintype (hs.extend (Set.subset_univ s)) := Fintype.ofFinite _
  have hcard : Fintype.card (hs.extend (Set.subset_univ s)) = m := by
    have hcard' : Module.finrank ℝ (Vec m) = Fintype.card (hs.extend (Set.subset_univ s)) :=
      Module.finrank_eq_card_basis b0
    exact hcard'.symm.trans (vec_finrank_eq m)
  let e0 : (hs.extend (Set.subset_univ s)) ≃ Fin m :=
    Fintype.equivFinOfCardEq hcard
  -- Reindex so that `c` sits at `lastRow`.
  let σ : Equiv.Perm (Fin m) := Equiv.swap (e0 ic) (lastRow m hm)
  let e : (hs.extend (Set.subset_univ s)) ≃ Fin m := e0.trans σ
  refine ⟨b0.reindex e, ?_⟩
  -- `e ic = lastRow`, hence `e.symm lastRow = ic`.
  have he : e ic = lastRow m hm := by
    simp [e, σ]
  have he' : e.symm (lastRow m hm) = ic := by
    exact (e.symm_apply_eq.mpr he.symm)
  calc
    (b0.reindex e) (lastRow m hm) = b0 (e.symm (lastRow m hm)) := by
      simpa using (Module.Basis.reindex_apply (b := b0) (e := e) (i' := lastRow m hm))
    _ = b0 ic := by simpa [he']
    _ = c := hb0c

end
