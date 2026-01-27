/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Steps 2-3: Converting Inequality and Equality Constraints

This file combines two transformation steps:
- Step 2: Converting ≥ constraints to ≤ constraints (a^T y ≥ β ↔ (-a)^T y ≤ -β)
- Step 3: Converting = constraints to ≤ constraints (a^T y = β ↔ (a^T y ≤ β) ∧ ((-a)^T y ≤ -β))
-/

import LeanLinearProgramming.Defs

noncomputable section

open scoped Matrix RealInnerProductSpace
open Finset Matrix

variable {n m₁ m₂ m₃ m : ℕ}

/-! ## Step 2: Converting ≥ to ≤ -/

/-- Convert a general LP by replacing ≥ constraints with ≤ constraints. -/
def geToLe (lp : GeneralLP n m₁ m₂ m₃) : GeneralLP n (m₁ + m₂) 0 m₃ :=
  { dir := lp.dir
    c := lp.c
    A₁ := stackMatrices lp.A₁ (-lp.A₂)
    b₁ := appendVecs lp.b₁ (-lp.b₂)
    A₂ := 0
    b₂ := 0
    A₃ := lp.A₃
    b₃ := lp.b₃
    σ := lp.σ }

theorem geToLe_feasible_iff (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (geToLe lp).IsFeasible y ↔ lp.IsFeasible y := by
  simp only [GeneralLP.IsFeasible, geToLe]
  constructor
  · intro ⟨hle, _, heq, hsign⟩
    refine ⟨?_, ?_, heq, hsign⟩
    · intro i
      have := hle ⟨i.val, by omega⟩
      simp only [mulVec, dotProduct, stackMatrices, appendVecs_apply, i.is_lt, dite_true] at this ⊢
      exact this
    · intro i
      have := hle ⟨m₁ + i.val, by omega⟩
      simp only [mulVec, dotProduct, stackMatrices, appendVecs_apply] at this
      simp only [Nat.not_lt.mpr (Nat.le_add_right m₁ i.val), dite_false] at this
      rw [ge_iff_le, ← neg_le_neg_iff]
      simp only [mulVec, dotProduct]
      have hsub : m₁ + i.val - m₁ = i.val := Nat.add_sub_cancel_left m₁ i.val
      simp only [hsub] at this
      have hsum : -∑ x, lp.A₂ i x * y x = ∑ x, (-lp.A₂ i x) * y x := by
        rw [← sum_neg_distrib]
        congr 1
        funext x
        ring
      rw [hsum]
      exact this
  · intro ⟨hle, hge, heq, hsign⟩
    refine ⟨?_, ?_, heq, hsign⟩
    · intro i
      simp only [mulVec, dotProduct, stackMatrices, appendVecs_apply]
      by_cases h : i.val < m₁
      · simp only [h, dite_true]
        have := hle ⟨i.val, h⟩
        simp only [mulVec, dotProduct] at this
        exact this
      · simp only [h, dite_false]
        have hi : i.val - m₁ < m₂ := by omega
        have := hge ⟨i.val - m₁, hi⟩
        simp only [ge_iff_le, mulVec, dotProduct] at this
        calc ∑ x, (-lp.A₂) ⟨i.val - m₁, _⟩ x * y x
            = ∑ x, -lp.A₂ ⟨i.val - m₁, hi⟩ x * y x := by rfl
          _ = -∑ x, lp.A₂ ⟨i.val - m₁, hi⟩ x * y x := by rw [← sum_neg_distrib]; ring_nf
          _ ≤ -lp.b₂ ⟨i.val - m₁, hi⟩ := by linarith
          _ = (-lp.b₂) ⟨i.val - m₁, _⟩ := by rfl
    · intro i; exact Fin.elim0 i

theorem geToLe_objective (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (geToLe lp).objective y = lp.objective y := rfl

theorem geToLe_optimal_iff (lp : GeneralLP n m₁ m₂ m₃) (y : Vec n) :
    (geToLe lp).IsOptimal y ↔ lp.IsOptimal y := by
  simp only [GeneralLP.IsOptimal]
  have hfeas_eq : (geToLe lp).IsFeasible y ↔ lp.IsFeasible y := geToLe_feasible_iff lp y
  have hfeas_all : ∀ z, (geToLe lp).IsFeasible z ↔ lp.IsFeasible z :=
    fun z => geToLe_feasible_iff lp z
  simp only [hfeas_eq, geToLe_objective]
  constructor
  · intro ⟨hfeas, hopt⟩
    refine ⟨hfeas, ?_⟩
    have hdir : (geToLe lp).dir = lp.dir := rfl
    simp only [hdir] at hopt
    cases hd : lp.dir <;> simp only [hd] at hopt ⊢
    · intro z hz; exact hopt z ((hfeas_all z).mpr hz)
    · intro z hz; exact hopt z ((hfeas_all z).mpr hz)
  · intro ⟨hfeas, hopt⟩
    refine ⟨hfeas, ?_⟩
    have hdir : (geToLe lp).dir = lp.dir := rfl
    simp only [hdir]
    cases hd : lp.dir <;> simp only [hd] at hopt ⊢
    · intro z hz; exact hopt z ((hfeas_all z).mp hz)
    · intro z hz; exact hopt z ((hfeas_all z).mp hz)

/-! ## Step 3: Converting = to ≤ -/

/-- Convert a general LP (with no ≥ constraints) by replacing = constraints with ≤. -/
def eqToLeq (lp : GeneralLP n m 0 m₃) : GeneralLP n (m + 2 * m₃) 0 0 :=
  { dir := lp.dir
    c := lp.c
    A₁ := fun i j =>
      if h : i.val < m then
        lp.A₁ ⟨i.val, h⟩ j
      else if h' : i.val < m + m₃ then
        lp.A₃ ⟨i.val - m, by omega⟩ j
      else
        -lp.A₃ ⟨i.val - m - m₃, by omega⟩ j
    b₁ := (WithLp.equiv 2 (Fin (m + 2 * m₃) → ℝ)).symm fun i =>
      if h : i.val < m then
        lp.b₁ ⟨i.val, h⟩
      else if h' : i.val < m + m₃ then
        lp.b₃ ⟨i.val - m, by omega⟩
      else
        -lp.b₃ ⟨i.val - m - m₃, by omega⟩
    A₂ := 0
    b₂ := 0
    A₃ := 0
    b₃ := 0
    σ := lp.σ }

theorem eqToLeq_feasible_iff (lp : GeneralLP n m 0 m₃) (y : Vec n) :
    (eqToLeq lp).IsFeasible y ↔ lp.IsFeasible y := by
  simp only [GeneralLP.IsFeasible, eqToLeq, mulVec, dotProduct, ge_iff_le,
    WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  constructor
  · intro ⟨hle, _, _, hsign⟩
    refine ⟨?_, ?_, ?_, hsign⟩
    · intro i
      have := hle ⟨i.val, by omega⟩
      simp only [i.is_lt, dite_true] at this
      exact this
    · intro i; exact Fin.elim0 i
    · intro i
      have h1 := hle ⟨m + i.val, by omega⟩
      have h2 := hle ⟨m + m₃ + i.val, by omega⟩
      have hlt1 : ¬(m + i.val < m) := by omega
      have hlt2 : m + i.val < m + m₃ := by omega
      have hlt3 : ¬(m + m₃ + i.val < m) := by omega
      have hlt4 : ¬(m + m₃ + i.val < m + m₃) := by omega
      simp only [hlt1, dite_false, hlt2, dite_true] at h1
      simp only [hlt3, dite_false, hlt4, dite_false, neg_mul,
        sum_neg_distrib, neg_le_neg_iff] at h2
      have hsub1 : m + i.val - m = i.val := Nat.add_sub_cancel_left m i.val
      have hsub2 : m + m₃ + i.val - m - m₃ = i.val := by omega
      have hA₃_eq1 : (⟨m + i.val - m, by omega⟩ : Fin m₃) = i := by ext; exact hsub1
      have hA₃_eq2 : (⟨m + m₃ + i.val - m - m₃, by omega⟩ : Fin m₃) = i := by ext; exact hsub2
      simp only [hA₃_eq1] at h1
      simp only [hA₃_eq2] at h2
      exact le_antisymm h1 h2
  · intro ⟨hle, _, heq, hsign⟩
    refine ⟨?_, ?_, ?_, hsign⟩
    · intro i
      by_cases h : i.val < m
      · simp only [h, dite_true]
        exact hle ⟨i.val, h⟩
      · by_cases h' : i.val < m + m₃
        · simp only [h, dite_false, h', dite_true]
          have hi : i.val - m < m₃ := by omega
          have := heq ⟨i.val - m, hi⟩
          rw [← this]
        · simp only [h, dite_false, h', dite_false, neg_mul, sum_neg_distrib]
          have hi : i.val - m - m₃ < m₃ := by omega
          have := heq ⟨i.val - m - m₃, hi⟩
          rw [← this]
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i

theorem eqToLeq_objective (lp : GeneralLP n m 0 m₃) (y : Vec n) :
    (eqToLeq lp).objective y = lp.objective y := rfl

theorem eqToLeq_optimal_iff (lp : GeneralLP n m 0 m₃) (y : Vec n) :
    (eqToLeq lp).IsOptimal y ↔ lp.IsOptimal y := by
  simp only [GeneralLP.IsOptimal]
  have hfeas_eq : (eqToLeq lp).IsFeasible y ↔ lp.IsFeasible y := eqToLeq_feasible_iff lp y
  have hfeas_all : ∀ z, (eqToLeq lp).IsFeasible z ↔ lp.IsFeasible z :=
    fun z => eqToLeq_feasible_iff lp z
  simp only [hfeas_eq, eqToLeq_objective]
  constructor
  · intro ⟨hfeas, hopt⟩
    refine ⟨hfeas, ?_⟩
    have hdir : (eqToLeq lp).dir = lp.dir := rfl
    simp only [hdir] at hopt
    cases hd : lp.dir <;> simp only [hd] at hopt ⊢
    · intro z hz; exact hopt z ((hfeas_all z).mpr hz)
    · intro z hz; exact hopt z ((hfeas_all z).mpr hz)
  · intro ⟨hfeas, hopt⟩
    refine ⟨hfeas, ?_⟩
    have hdir : (eqToLeq lp).dir = lp.dir := rfl
    simp only [hdir]
    cases hd : lp.dir <;> simp only [hd] at hopt ⊢
    · intro z hz; exact hopt z ((hfeas_all z).mp hz)
    · intro z hz; exact hopt z ((hfeas_all z).mp hz)

end
