/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linear Programming Definitions

Basic definitions for linear programs: vectors, matrices, standard form, and general form.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

/-! ## Type aliases -/

/-- Vector type as EuclideanSpace -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Matrix type -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The nonnegative orthant: all coordinates ≥ 0 -/
def nonnegOrthant (n : ℕ) : Set (Vec n) := { x | ∀ i, 0 ≤ x i }

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

end
