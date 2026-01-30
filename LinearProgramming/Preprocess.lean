/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# LP Preprocessing Interfaces and Strong-Polynomial Cost API

This module adds interfaces for preprocessing steps such as presolve,
facial reduction, and strict-interior (Phase I) checks. The goal is to
provide an API that supports **strongly-polynomial** cost proofs when
combined with a strongly-polynomial feasibility solver.
-/

import LinearProgramming.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic

noncomputable section

open scoped Matrix

namespace LinearProgramming

/-! ## Polynomial Cost Bounds -/

/-- Base for dimension-dependent bounds: `1 + m + n`. -/
def polyBase (m n : ℕ) : ℕ := 1 + m + n

lemma polyBase_pos (m n : ℕ) : 1 ≤ polyBase m n := by
  unfold polyBase
  -- 1 ≤ 1 + m + n
  omega

lemma pow_le_pow_of_le {m n k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    (polyBase m n) ^ k₁ ≤ (polyBase m n) ^ k₂ := by
  exact pow_le_pow_right' (polyBase_pos m n) hk

/-- A function is polynomially bounded in `(m,n)` if it is bounded by
`c * (1 + m + n)^k` for some constants `c,k`. -/
def IsPolyBound (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c k, ∀ m n, f m n ≤ c * (polyBase m n) ^ k

lemma IsPolyBound.of_le {f g : ℕ → ℕ → ℕ} (hg : IsPolyBound g)
    (hfg : ∀ m n, f m n ≤ g m n) : IsPolyBound f := by
  rcases hg with ⟨c, k, hk⟩
  refine ⟨c, k, ?_⟩
  intro m n
  exact Nat.le_trans (hfg m n) (hk m n)

lemma IsPolyBound.const (c : ℕ) : IsPolyBound (fun _ _ => c) := by
  refine ⟨c, 0, ?_⟩
  intro m n
  simp [polyBase]

lemma IsPolyBound.add {f g : ℕ → ℕ → ℕ}
    (hf : IsPolyBound f) (hg : IsPolyBound g) :
    IsPolyBound (fun m n => f m n + g m n) := by
  rcases hf with ⟨c₁, k₁, hf⟩
  rcases hg with ⟨c₂, k₂, hg⟩
  refine ⟨c₁ + c₂, max k₁ k₂, ?_⟩
  intro m n
  have h₁ := hf m n
  have h₂ := hg m n
  have hpow₁ : (polyBase m n) ^ k₁ ≤ (polyBase m n) ^ (max k₁ k₂) :=
    pow_le_pow_of_le (m := m) (n := n) (k₁ := k₁) (k₂ := max k₁ k₂) (Nat.le_max_left _ _)
  have hpow₂ : (polyBase m n) ^ k₂ ≤ (polyBase m n) ^ (max k₁ k₂) :=
    pow_le_pow_of_le (m := m) (n := n) (k₁ := k₂) (k₂ := max k₁ k₂) (Nat.le_max_right _ _)
  have h₁' : c₁ * (polyBase m n) ^ k₁ ≤ c₁ * (polyBase m n) ^ (max k₁ k₂) :=
    Nat.mul_le_mul_left _ hpow₁
  have h₂' : c₂ * (polyBase m n) ^ k₂ ≤ c₂ * (polyBase m n) ^ (max k₁ k₂) :=
    Nat.mul_le_mul_left _ hpow₂
  calc
    f m n + g m n ≤ c₁ * (polyBase m n) ^ k₁ + c₂ * (polyBase m n) ^ k₂ :=
      Nat.add_le_add h₁ h₂
    _ ≤ c₁ * (polyBase m n) ^ (max k₁ k₂) + c₂ * (polyBase m n) ^ (max k₁ k₂) :=
      Nat.add_le_add h₁' h₂'
    _ = (c₁ + c₂) * (polyBase m n) ^ (max k₁ k₂) := by
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- A dimension-uniform polynomial cost bound for algorithms over `InequalityForm`. -/
def IsPolyCost (cost : ∀ {m n}, InequalityForm m n → ℕ) : Prop :=
  ∃ c k, ∀ {m n} (P : InequalityForm m n), cost P ≤ c * (polyBase m n) ^ k

/-! ## Strongly-Polynomial Feasibility Solver -/

structure StronglyPolyFeasibilitySolver where
  solve : ∀ {m n}, InequalityForm m n → Option (Vec n)
  sound : ∀ {m n} {P : InequalityForm m n} {x},
    solve P = some x → P.feasible x
  complete : ∀ {m n} {P : InequalityForm m n},
    P.isFeasible → ∃ x, solve P = some x
  cost : ∀ {m n}, InequalityForm m n → ℕ
  poly_cost : IsPolyCost cost

/-! ## Feasibility Preprocessors -/

structure FeasibilityPreprocessor where
  /-- Return a new inequality form with the same variable dimension. -/
  run : ∀ {m n}, InequalityForm m n → Σ m', InequalityForm m' n
  /-- Any solution of the preprocessed LP is a solution of the original. -/
  sound : ∀ {m n} {P : InequalityForm m n} {x},
    let R := run P
    (R.2).feasible x → P.feasible x
  /-- Any solution of the original LP is feasible for the preprocessed LP. -/
  complete : ∀ {m n} {P : InequalityForm m n} {x},
    P.feasible x →
      let R := run P
      (R.2).feasible x
  /-- Preprocessing cost. -/
  cost : ∀ {m n}, InequalityForm m n → ℕ
  /-- Polynomial cost bound in `(m,n)`. -/
  poly_cost : IsPolyCost cost
  /-- Polynomial bound on the number of constraints after preprocessing. -/
  out_bound :
    ∃ c k, ∀ {m n} (P : InequalityForm m n),
      (run P).1 ≤ c * (polyBase m n) ^ k

/-- Apply preprocessing then solve. -/
def preprocessSolve (pre : FeasibilityPreprocessor) (solver : StronglyPolyFeasibilitySolver)
    {m n} (P : InequalityForm m n) : Option (Vec n) :=
  let R := pre.run P
  solver.solve R.2

theorem preprocessSolve_sound (pre : FeasibilityPreprocessor) (solver : StronglyPolyFeasibilitySolver)
    {m n} {P : InequalityForm m n} {x : Vec n} :
    preprocessSolve pre solver P = some x → P.feasible x := by
  intro h
  unfold preprocessSolve at h
  dsimp at h
  set R := pre.run P with hR
  have hx' : (R.2).feasible x := by
    have hsol : solver.solve R.2 = some x := by simpa [R] using h
    exact solver.sound hsol
  have : (let R := pre.run P; (R.2).feasible x → P.feasible x) := pre.sound
  simpa [R] using this hx'

theorem preprocessSolve_complete (pre : FeasibilityPreprocessor) (solver : StronglyPolyFeasibilitySolver)
    {m n} {P : InequalityForm m n} :
    P.isFeasible → ∃ x, preprocessSolve pre solver P = some x := by
  intro hfeas
  rcases hfeas with ⟨x, hx⟩
  have hx' : (let R := pre.run P; (R.2).feasible x) := pre.complete (P := P) (x := x) hx
  set R := pre.run P with hR
  have hx'' : (R.2).feasible x := by simpa [R] using hx'
  obtain ⟨x', hx'⟩ := solver.complete (P := R.2) ⟨x, hx''⟩
  refine ⟨x', ?_⟩
  unfold preprocessSolve
  simp [R, hx']

/-! ## Strong-Polynomial Cost for Preprocess + Solve -/

def preprocessSolve_cost (pre : FeasibilityPreprocessor) (solver : StronglyPolyFeasibilitySolver)
    {m n} (P : InequalityForm m n) : ℕ :=
  pre.cost P + solver.cost (pre.run P).2

lemma polyBase_le_of_out_bound {m n m' c k : ℕ}
    (h : m' ≤ c * (polyBase m n) ^ k) :
    polyBase m' n ≤ (c + 1) * (polyBase m n) ^ (k + 1) := by
  have h1 : 1 + m' ≤ 1 + c * (polyBase m n) ^ k :=
    Nat.add_le_add_left h 1
  have h2 : 1 + m' + n ≤ (1 + c * (polyBase m n) ^ k) + n :=
    Nat.add_le_add_right h1 n
  have h3 : 1 + c * (polyBase m n) ^ k + n =
      c * (polyBase m n) ^ k + (1 + n) := by
    omega
  have h4 : 1 + n ≤ polyBase m n := by
    unfold polyBase
    omega
  have h5 : c * (polyBase m n) ^ k + (1 + n) ≤
      c * (polyBase m n) ^ k + polyBase m n :=
    Nat.add_le_add_left h4 _
  have h6 : polyBase m n ≤ (polyBase m n) ^ (k + 1) := by
    have hpow : (polyBase m n) ^ 1 ≤ (polyBase m n) ^ (k + 1) :=
      pow_le_pow_of_le (m := m) (n := n) (k₁ := 1) (k₂ := k + 1) (by omega)
    simpa using hpow
  have h7 : (polyBase m n) ^ k ≤ (polyBase m n) ^ (k + 1) :=
    pow_le_pow_of_le (m := m) (n := n) (k₁ := k) (k₂ := k + 1) (by omega)
  have h8 : c * (polyBase m n) ^ k ≤ c * (polyBase m n) ^ (k + 1) :=
    Nat.mul_le_mul_left _ h7
  have h9 : c * (polyBase m n) ^ k + polyBase m n ≤
      c * (polyBase m n) ^ (k + 1) + (polyBase m n) ^ (k + 1) :=
    Nat.add_le_add h8 h6
  have h10 : c * (polyBase m n) ^ (k + 1) + (polyBase m n) ^ (k + 1) =
      (c + 1) * (polyBase m n) ^ (k + 1) := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  calc
    polyBase m' n = 1 + m' + n := by rfl
    _ ≤ (1 + c * (polyBase m n) ^ k) + n := h2
    _ = c * (polyBase m n) ^ k + (1 + n) := h3
    _ ≤ c * (polyBase m n) ^ k + polyBase m n := h5
    _ ≤ c * (polyBase m n) ^ (k + 1) + (polyBase m n) ^ (k + 1) := h9
    _ = (c + 1) * (polyBase m n) ^ (k + 1) := h10

theorem preprocessSolve_cost_poly (pre : FeasibilityPreprocessor)
    (solver : StronglyPolyFeasibilitySolver) :
    IsPolyCost (fun {m n} (P : InequalityForm m n) => preprocessSolve_cost pre solver P) := by
  rcases pre.poly_cost with ⟨c₁, k₁, hpre⟩
  rcases solver.poly_cost with ⟨c₂, k₂, hsol⟩
  rcases pre.out_bound with ⟨c₃, k₃, hout⟩
  refine ⟨c₁ + c₂ * (c₃ + 1) ^ k₂, max k₁ ((k₃ + 1) * k₂), ?_⟩
  intro m n P
  set base := polyBase m n
  set R := pre.run P with hR
  have hpre' : pre.cost P ≤ c₁ * base ^ k₁ := by
    simpa [base] using (hpre (P := P))
  have hm' : R.1 ≤ c₃ * base ^ k₃ := by
    simpa [base, R] using (hout (P := P))
  have hbase' : polyBase R.1 n ≤ (c₃ + 1) * base ^ (k₃ + 1) := by
    simpa [base] using (polyBase_le_of_out_bound (m := m) (n := n) (m' := R.1) (c := c₃)
      (k := k₃) hm')
  have hsol' : solver.cost R.2 ≤ c₂ * (polyBase R.1 n) ^ k₂ := by
    simpa [R] using (hsol (P := R.2))
  have hpow :
      (polyBase R.1 n) ^ k₂ ≤ ((c₃ + 1) * base ^ (k₃ + 1)) ^ k₂ :=
    pow_le_pow_left' hbase' _
  have hsol'' :
      solver.cost R.2 ≤ c₂ * ((c₃ + 1) * base ^ (k₃ + 1)) ^ k₂ :=
    Nat.le_trans hsol' (Nat.mul_le_mul_left _ hpow)
  have hsol''' :
      solver.cost R.2 ≤ (c₂ * (c₃ + 1) ^ k₂) * base ^ ((k₃ + 1) * k₂) := by
    have hmul :
        ((c₃ + 1) * base ^ (k₃ + 1)) ^ k₂ =
          (c₃ + 1) ^ k₂ * (base ^ (k₃ + 1)) ^ k₂ := by
      simp [Nat.mul_pow]
    have hpow' : (base ^ (k₃ + 1)) ^ k₂ = base ^ ((k₃ + 1) * k₂) := by
      simp [Nat.pow_mul]
    calc
      solver.cost R.2 ≤ c₂ * ((c₃ + 1) * base ^ (k₃ + 1)) ^ k₂ := hsol''
      _ = c₂ * ((c₃ + 1) ^ k₂ * (base ^ (k₃ + 1)) ^ k₂) := by
          simp [hmul]
      _ = (c₂ * (c₃ + 1) ^ k₂) * (base ^ (k₃ + 1)) ^ k₂ := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = (c₂ * (c₃ + 1) ^ k₂) * base ^ ((k₃ + 1) * k₂) := by
          simp [hpow']
  have hpow₁ : base ^ k₁ ≤ base ^ (max k₁ ((k₃ + 1) * k₂)) :=
    pow_le_pow_of_le (m := m) (n := n) (k₁ := k₁) (k₂ := max k₁ ((k₃ + 1) * k₂))
      (Nat.le_max_left _ _)
  have hpow₂ : base ^ ((k₃ + 1) * k₂) ≤ base ^ (max k₁ ((k₃ + 1) * k₂)) :=
    pow_le_pow_of_le (m := m) (n := n) (k₁ := (k₃ + 1) * k₂)
      (k₂ := max k₁ ((k₃ + 1) * k₂)) (Nat.le_max_right _ _)
  have hpre'' :
      pre.cost P ≤ c₁ * base ^ (max k₁ ((k₃ + 1) * k₂)) :=
    Nat.le_trans hpre' (Nat.mul_le_mul_left _ hpow₁)
  have hsol'''' :
      solver.cost R.2 ≤ (c₂ * (c₃ + 1) ^ k₂) * base ^ (max k₁ ((k₃ + 1) * k₂)) :=
    Nat.le_trans hsol''' (Nat.mul_le_mul_left _ hpow₂)
  have hsum :
      pre.cost P + solver.cost R.2 ≤
        c₁ * base ^ (max k₁ ((k₃ + 1) * k₂)) +
        (c₂ * (c₃ + 1) ^ k₂) * base ^ (max k₁ ((k₃ + 1) * k₂)) :=
    Nat.add_le_add hpre'' hsol''''
  calc
    preprocessSolve_cost pre solver P = pre.cost P + solver.cost R.2 := by
      simp [preprocessSolve_cost, R]
    _ ≤ c₁ * base ^ (max k₁ ((k₃ + 1) * k₂)) +
        (c₂ * (c₃ + 1) ^ k₂) * base ^ (max k₁ ((k₃ + 1) * k₂)) := hsum
    _ = (c₁ + c₂ * (c₃ + 1) ^ k₂) * base ^ (max k₁ ((k₃ + 1) * k₂)) := by
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-! ## Named Preprocessor Interfaces -/

/-- Presolve / redundancy-removal preprocessor (interface). -/
structure RedundancyRemovalPreprocessor extends FeasibilityPreprocessor

/-- Facial-reduction preprocessor (interface). -/
structure FacialReductionPreprocessor extends FeasibilityPreprocessor

/-- Phase-I strict-interior preprocessor (interface). -/
structure StrictInteriorPreprocessor extends FeasibilityPreprocessor

end LinearProgramming
