/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Standard Form Equivalence

Full equivalence theorem: any general LP can be converted to standard form.
This file provides the complete pipeline for transforming a general LP.
-/

import LinearProgramming.Defs
import LinearProgramming.MinToMax
import LinearProgramming.SwapInequalities
import LinearProgramming.NonnegConstraint

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

/-! ## Reduction from Ax ≤ b to By = c -/

/-- The augmented matrix [A | -A | I] used in the reduction.
    For a vector y = (x⁺, x⁻, s), we have [A | -A | I] y = A(x⁺ - x⁻) + s -/
def augmentedMatrix {m n : ℕ} (A : Mat m n) : Mat m (2 * n + m) :=
  fun i j =>
    if h : j.val < n then A i ⟨j.val, h⟩
    else if h' : j.val < 2 * n then -A i ⟨j.val - n, by omega⟩
    else if j.val - 2 * n = i.val then 1 else 0

/-- Convert an LP problem to standard form with equality -/
def toStandardForm {m n : ℕ} (P : InequalityForm m n) : StandardForm m (2 * n + m) :=
  { B := augmentedMatrix P.A, c := P.b }

/-- Extract x from a standard form solution y = (x⁺, x⁻, s) as x = x⁺ - x⁻ -/
def extractX {n m : ℕ} (y : Vec (2 * n + m)) : Vec n :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => y ⟨i.val, by omega⟩ - y ⟨n + i.val, by omega⟩)

/-- Construct a standard form solution from an original solution:
    y = (max(x,0), max(-x,0), b - Ax) -/
def constructY {n m : ℕ} (P : InequalityForm m n) (x : Vec n) : Vec (2 * n + m) :=
  (WithLp.equiv 2 (Fin (2 * n + m) → ℝ)).symm (fun j =>
    if h : j.val < n then max (x ⟨j.val, h⟩) 0
    else if h' : j.val < 2 * n then max (-x ⟨j.val - n, by omega⟩) 0
    else P.b ⟨j.val - 2 * n, by omega⟩ - (P.A.mulVec x) ⟨j.val - 2 * n, by omega⟩)

@[simp]
lemma constructY_apply {m n : ℕ} (P : InequalityForm m n) (x : Vec n) (j : Fin (2 * n + m)) :
    (constructY P x).ofLp j =
      if h : j.val < n then max (x ⟨j.val, h⟩) 0
      else if h' : j.val < 2 * n then max (-x ⟨j.val - n, by omega⟩) 0
      else P.b ⟨j.val - 2 * n, by omega⟩ - (P.A.mulVec x) ⟨j.val - 2 * n, by omega⟩ := by
  rfl

@[simp]
lemma extractX_apply {n m : ℕ} (y : Vec (2 * n + m)) (j : Fin n) :
    extractX y j = y ⟨j.val, by omega⟩ - y ⟨n + j.val, by omega⟩ := by
  rfl

/-! ## Helper lemmas for sum decomposition -/

private def finSumEquiv (n m : ℕ) : Fin n ⊕ Fin m ≃ Fin (n + m) :=
  { toFun := Sum.elim (Fin.castAdd m) (Fin.natAdd n)
    invFun := fun i => Fin.addCases (fun i => Sum.inl i) (fun j => Sum.inr j) i
    left_inv := by intro x; cases x <;> simp
    right_inv := by intro i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp }

private lemma sum_fin_add {β : Type*} [AddCommMonoid β] {n m : ℕ} (f : Fin (n + m) → β) :
    (∑ i : Fin (n + m), f i) =
      (∑ i : Fin n, f (Fin.castAdd m i)) + (∑ i : Fin m, f (Fin.natAdd n i)) := by
  classical
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumEquiv n m
  calc
    ∑ i : Fin (n + m), f i
        = ∑ s : Fin n ⊕ Fin m, f (e s) := by
            simpa using (Equiv.sum_comp (e := e) (g := f)).symm
    _ = (∑ i : Fin n, f (e (Sum.inl i))) + (∑ j : Fin m, f (e (Sum.inr j))) := by
          simpa using (Fintype.sum_sum_type (f := fun s : Fin n ⊕ Fin m => f (e s)))
    _ = (∑ i : Fin n, f (Fin.castAdd m i)) + (∑ j : Fin m, f (Fin.natAdd n j)) := by
          simp [e, finSumEquiv]

private lemma mulVec_pos_neg_decomp {m n : ℕ} (A : Mat m n) (x : Vec n) (i : Fin m) :
    (A.mulVec x) i =
      (∑ j : Fin n, A i j * max (x j) 0) +
      (∑ j : Fin n, (-A i j) * max (-x j) 0) := by
  have hterm : ∀ j : Fin n,
      A i j * x j = A i j * max (x j) 0 + (-A i j) * max (-x j) 0 := by
    intro j
    have hx := max_pos_sub_max_neg (x j)
    calc
      A i j * x j = A i j * (max (x j) 0 - max (-x j) 0) := by simpa [hx]
      _ = A i j * max (x j) 0 - A i j * max (-x j) 0 := by ring
      _ = A i j * max (x j) 0 + (-A i j) * max (-x j) 0 := by ring
  calc
    (A.mulVec x) i = ∑ j : Fin n, A i j * x j := by rfl
    _ = ∑ j : Fin n, (A i j * max (x j) 0 + (-A i j) * max (-x j) 0) := by
          refine Finset.sum_congr rfl ?_; intro j _hj; exact hterm j
    _ = (∑ j : Fin n, A i j * max (x j) 0) + (∑ j : Fin n, (-A i j) * max (-x j) 0) := by
          simp [Finset.sum_add_distrib]

private lemma mulVec_extractX_decomp {m n : ℕ} (A : Mat m n) (y : Vec (2 * n + m)) (i : Fin m) :
    (A.mulVec (extractX y)) i =
      (∑ j : Fin n, A i j * y ⟨j.val, by omega⟩) +
      (∑ j : Fin n, (-A i j) * y ⟨n + j.val, by omega⟩) := by
  classical
  calc
    (A.mulVec (extractX y)) i = ∑ j : Fin n, A i j * (extractX y) j := by rfl
    _ = ∑ j : Fin n, A i j * (y ⟨j.val, by omega⟩ - y ⟨n + j.val, by omega⟩) := by
          refine Finset.sum_congr rfl ?_; intro j _hj; simp
    _ = ∑ j : Fin n, (A i j * y ⟨j.val, by omega⟩ + (-A i j) * y ⟨n + j.val, by omega⟩) := by
          refine Finset.sum_congr rfl ?_; intro j _hj; ring
    _ = (∑ j : Fin n, A i j * y ⟨j.val, by omega⟩) +
        (∑ j : Fin n, (-A i j) * y ⟨n + j.val, by omega⟩) := by
          simp [Finset.sum_add_distrib]

private lemma augmentedMatrix_mulVec_split {m n : ℕ} (A : Mat m n) (y : Vec (2 * n + m))
    (i : Fin m) :
    (augmentedMatrix A).mulVec y i =
      (∑ j : Fin n,
        A i j * y ((finCongr (by simp [two_mul, add_assoc])).symm (Fin.castAdd (n + m) j))) +
      (∑ j : Fin n,
        (-A i j) *
          y ((finCongr (by simp [two_mul, add_assoc])).symm (Fin.natAdd n (Fin.castAdd m j)))) +
      y ((finCongr (by simp [two_mul, add_assoc])).symm (Fin.natAdd n (Fin.natAdd n i))) := by
  classical
  let e : Fin (2 * n + m) ≃ Fin (n + (n + m)) := finCongr (by simp [two_mul, add_assoc])
  let f : Fin (2 * n + m) → ℝ := fun j => (augmentedMatrix A i j) * y j
  have hcast : (∑ j : Fin (2 * n + m), f j) = ∑ j : Fin (n + (n + m)), f (e.symm j) := by
    simpa [e] using (Equiv.sum_comp (e := e) (g := fun j => f (e.symm j)))
  have hsum1 : (∑ j : Fin (2 * n + m), f j) =
        (∑ j : Fin n, f (e.symm (Fin.castAdd (n + m) j))) +
        (∑ j : Fin (n + m), f (e.symm (Fin.natAdd n j))) := by
    calc ∑ j : Fin (2 * n + m), f j = ∑ j : Fin (n + (n + m)), f (e.symm j) := hcast
      _ = _ := by simpa using (sum_fin_add (n := n) (m := n + m) (f := fun j => f (e.symm j)))
  have hsum2 : (∑ j : Fin (n + m), f (e.symm (Fin.natAdd n j))) =
        (∑ j : Fin n, f (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
        (∑ j : Fin m, f (e.symm (Fin.natAdd n (Fin.natAdd n j)))) := by
    simpa using (sum_fin_add (n := n) (m := m) (f := fun j => f (e.symm (Fin.natAdd n j))))
  have hleft : (∑ j : Fin n, f (e.symm (Fin.castAdd (n + m) j))) =
        ∑ j : Fin n, A i j * y (e.symm (Fin.castAdd (n + m) j)) := by
    refine Finset.sum_congr rfl ?_; intro j _hj
    have hj : (e.symm (Fin.castAdd (n + m) j)).val < n := by simpa [e] using j.isLt
    simp [f, augmentedMatrix, hj, e]
  have hmid : (∑ j : Fin n, f (e.symm (Fin.natAdd n (Fin.castAdd m j)))) =
        ∑ j : Fin n, (-A i j) * y (e.symm (Fin.natAdd n (Fin.castAdd m j))) := by
    refine Finset.sum_congr rfl ?_; intro j _hj
    have idx_val : (e.symm (Fin.natAdd n (Fin.castAdd m j))).val = n + j.val := by simp [e]
    have h1 : ¬ n + j.val < n := by omega
    have h2 : n + j.val < 2 * n := by have hj' : j.val < n := j.isLt; omega
    have hsub : n + j.val - n = j.val := by simp [Nat.add_sub_cancel_left]
    simp [f, augmentedMatrix, idx_val, h1, h2, hsub, e]
  have hright : (∑ j : Fin m, f (e.symm (Fin.natAdd n (Fin.natAdd n j)))) =
        y (e.symm (Fin.natAdd n (Fin.natAdd n i))) := by
    classical
    have hterm : ∀ j : Fin m,
        f (e.symm (Fin.natAdd n (Fin.natAdd n j))) =
          (if j = i then y (e.symm (Fin.natAdd n (Fin.natAdd n i))) else 0) := by
      intro j
      have idx_val : (e.symm (Fin.natAdd n (Fin.natAdd n j))).val = n + (n + j.val) := by simp [e]
      have h1 : ¬ n + (n + j.val) < n := by omega
      have h2 : ¬ n + (n + j.val) < 2 * n := by omega
      have hval : n + (n + j.val) - 2 * n = j.val := by
        simp [two_mul, add_assoc, Nat.add_sub_add_left, Nat.add_sub_cancel_left]
      by_cases hji : j = i
      · subst hji; simp [f, augmentedMatrix, idx_val, h1, h2, hval, e]
      · have hji' : j.val ≠ i.val := fun hval_eq => hji (Fin.ext hval_eq)
        simp [f, augmentedMatrix, idx_val, h1, h2, hval, Fin.ext_iff, hji', hji, e]
    calc (∑ j : Fin m, f (e.symm (Fin.natAdd n (Fin.natAdd n j))))
        = ∑ j : Fin m, (if j = i then y (e.symm (Fin.natAdd n (Fin.natAdd n i))) else 0) := by
            refine Finset.sum_congr rfl ?_; intro j _hj; exact hterm j
      _ = y (e.symm (Fin.natAdd n (Fin.natAdd n i))) := by simp
  calc (augmentedMatrix A).mulVec y i = ∑ j : Fin (2 * n + m), f j := by
          simp [Matrix.mulVec, dotProduct, f]
    _ = (∑ j : Fin n, f (e.symm (Fin.castAdd (n + m) j))) +
        (∑ j : Fin (n + m), f (e.symm (Fin.natAdd n j))) := hsum1
    _ = (∑ j : Fin n, f (e.symm (Fin.castAdd (n + m) j))) +
        ((∑ j : Fin n, f (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
         (∑ j : Fin m, f (e.symm (Fin.natAdd n (Fin.natAdd n j))))) := by simp [hsum2, add_assoc]
    _ = (∑ j : Fin n, A i j * y (e.symm (Fin.castAdd (n + m) j))) +
        ((∑ j : Fin n, (-A i j) * y (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
         y (e.symm (Fin.natAdd n (Fin.natAdd n i)))) := by rw [hleft, hmid, hright]
    _ = _ := by simp [add_assoc]

/-! ## Main reduction theorems -/

/-- Forward direction: if x is feasible for Ax ≤ b, then constructY P x is feasible for By = c -/
theorem reduction_forward {m n : ℕ} (P : InequalityForm m n) (x : Vec n) :
    P.feasible x → (toStandardForm P).feasible (constructY P x) := by
  intro hx
  unfold toStandardForm StandardForm.feasible
  constructor
  · -- Show augmentedMatrix * y = b
    ext i
    have hposneg := mulVec_pos_neg_decomp (A := P.A) (x := x) i
    have hsum :
        (augmentedMatrix P.A).mulVec (constructY P x) i =
          (∑ j : Fin n, P.A i j * max (x.ofLp j) 0) +
          (∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0) +
          (P.b i - (P.A *ᵥ x.ofLp) i) := by
      classical
      let e : Fin (2 * n + m) ≃ Fin (n + (n + m)) := finCongr (by simp [two_mul, add_assoc])
      have hcast : ∀ j : Fin n,
          (constructY P x).ofLp (e.symm (Fin.castAdd (n + m) j)) = max (x.ofLp j) 0 := by
        intro j
        have idx_val : (e.symm (Fin.castAdd (n + m) j)).val = j.val := by simp [e]
        have hj : j.val < n := j.isLt
        have hfin : (⟨j.val, hj⟩ : Fin n) = j := by ext; rfl
        simp [constructY, idx_val, hj, hfin, e]
      have hnat : ∀ j : Fin n,
          (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.castAdd m j))) = max (-x.ofLp j) 0 := by
        intro j
        have idx_val : (e.symm (Fin.natAdd n (Fin.castAdd m j))).val = n + j.val := by simp [e]
        have h1 : ¬ n + j.val < n := by omega
        have h2 : n + j.val < 2 * n := by have hj' : j.val < n := j.isLt; omega
        have hsub : n + j.val - n = j.val := by simp [Nat.add_sub_cancel_left]
        have hfin : (⟨j.val, j.isLt⟩ : Fin n) = j := by ext; rfl
        simp [constructY, idx_val, h1, h2, hsub, hfin, e]
      have hslack :
          (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.natAdd n i))) =
            P.b i - (P.A *ᵥ x.ofLp) i := by
        have idx_val : (e.symm (Fin.natAdd n (Fin.natAdd n i))).val = n + (n + i.val) := by simp [e]
        have h1 : ¬ n + (n + i.val) < n := by omega
        have h2 : ¬ n + (n + i.val) < 2 * n := by omega
        have hsub : n + (n + i.val) - 2 * n = i.val := by
          simp [two_mul, add_assoc, Nat.add_sub_add_left, Nat.add_sub_cancel_left]
        have hfin : (⟨i.val, i.isLt⟩ : Fin m) = i := by ext; rfl
        simp [constructY, idx_val, h1, h2, hsub, hfin, e]
      have hsplit :
          (augmentedMatrix P.A).mulVec (constructY P x) i =
            (∑ j : Fin n, P.A i j * (constructY P x).ofLp (e.symm (Fin.castAdd (n + m) j))) +
            (∑ j : Fin n, (-P.A i j) * (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
            (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.natAdd n i))) := by
        simpa [e] using (augmentedMatrix_mulVec_split (A := P.A) (y := constructY P x) i)
      have hsum1 :
          (∑ j : Fin n, P.A i j * (constructY P x).ofLp (e.symm (Fin.castAdd (n + m) j))) =
            ∑ j : Fin n, P.A i j * max (x.ofLp j) 0 := by
        refine Finset.sum_congr rfl ?_; intro j _hj
        simpa using congrArg (fun t => P.A i j * t) (hcast j)
      have hsum2 :
          (∑ j : Fin n, (-P.A i j) * (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.castAdd m j)))) =
            ∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0 := by
        refine Finset.sum_congr rfl ?_; intro j _hj
        simpa using congrArg (fun t => (-P.A i j) * t) (hnat j)
      calc (augmentedMatrix P.A).mulVec (constructY P x) i
          = (∑ j : Fin n, P.A i j * (constructY P x).ofLp (e.symm (Fin.castAdd (n + m) j))) +
            (∑ j : Fin n, (-P.A i j) * (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
            (constructY P x).ofLp (e.symm (Fin.natAdd n (Fin.natAdd n i))) := hsplit
        _ = (∑ j : Fin n, P.A i j * max (x.ofLp j) 0) +
            (∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0) +
            (P.b i - (P.A *ᵥ x.ofLp) i) := by rw [hsum1, hsum2, hslack]
    have hsum' :
        (∑ j : Fin n, P.A i j * max (x.ofLp j) 0) +
        (∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0) = (P.A *ᵥ x.ofLp) i := by
      simpa using hposneg.symm
    calc (augmentedMatrix P.A).mulVec (constructY P x) i
        = (∑ j : Fin n, P.A i j * max (x.ofLp j) 0) +
          (∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0) +
          (P.b i - (P.A *ᵥ x.ofLp) i) := hsum
      _ = ((∑ j : Fin n, P.A i j * max (x.ofLp j) 0) +
            (∑ j : Fin n, (-P.A i j) * max (-x.ofLp j) 0)) +
            (P.b i - (P.A *ᵥ x.ofLp) i) := by simp [add_assoc]
      _ = (P.A *ᵥ x.ofLp) i + (P.b i - (P.A *ᵥ x.ofLp) i) := by rw [hsum']
      _ = P.b i := by ring
  · -- Nonnegativity of constructY
    intro j
    by_cases h1 : j.val < n
    · have hpos : 0 ≤ max (x ⟨j.val, h1⟩) 0 := le_max_right _ _
      simpa [h1] using hpos
    · by_cases h2 : j.val < 2 * n
      · have hpos : 0 ≤ max (-x ⟨j.val - n, by omega⟩) 0 := le_max_right _ _
        simpa [h1, h2] using hpos
      · have hslack : 0 ≤ P.b ⟨j.val - 2 * n, by omega⟩ -
            (P.A.mulVec x) ⟨j.val - 2 * n, by omega⟩ := by
          have hxj := hx ⟨j.val - 2 * n, by omega⟩
          linarith
        simpa [h1, h2] using hslack

/-- Backward direction: if y is feasible for By = c, then extractX y is feasible for Ax ≤ b -/
theorem reduction_backward {m n : ℕ} (P : InequalityForm m n) (y : Vec (2 * n + m)) :
    (toStandardForm P).feasible y → P.feasible (extractX y) := by
  intro hy i
  have hmul : (augmentedMatrix P.A).mulVec y = P.b := hy.1
  have hnonneg : y ∈ nonnegOrthant (2 * n + m) := hy.2
  have hslack : y ⟨2 * n + i.val, by omega⟩ = P.b i - (P.A.mulVec (extractX y)) i := by
    classical
    have hrow := congrArg (fun v => v i) hmul
    let e : Fin (2 * n + m) ≃ Fin (n + (n + m)) := finCongr (by simp [two_mul, add_assoc])
    have hsplit' :
        (augmentedMatrix P.A).mulVec y i =
          (∑ j : Fin n, P.A i j * y (e.symm (Fin.castAdd (n + m) j))) +
          (∑ j : Fin n, (-P.A i j) * y (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
          y (e.symm (Fin.natAdd n (Fin.natAdd n i))) := by
      simpa [e] using (augmentedMatrix_mulVec_split (A := P.A) (y := y) i)
    have hleft :
        (∑ j : Fin n, P.A i j * y (e.symm (Fin.castAdd (n + m) j))) =
          ∑ j : Fin n, P.A i j * y ⟨j.val, by omega⟩ := by
      refine Finset.sum_congr rfl ?_; intro j _hj
      have idx_val : (e.symm (Fin.castAdd (n + m) j)).val = j.val := by simp [e]
      have hfin : e.symm (Fin.castAdd (n + m) j) = ⟨j.val, by omega⟩ := by
        apply Fin.ext; simpa [idx_val]
      simp [hfin]
    have hmid :
        (∑ j : Fin n, (-P.A i j) * y (e.symm (Fin.natAdd n (Fin.castAdd m j)))) =
          ∑ j : Fin n, (-P.A i j) * y ⟨n + j.val, by omega⟩ := by
      refine Finset.sum_congr rfl ?_; intro j _hj
      have idx_val : (e.symm (Fin.natAdd n (Fin.castAdd m j))).val = n + j.val := by simp [e]
      have hfin : e.symm (Fin.natAdd n (Fin.castAdd m j)) = ⟨n + j.val, by omega⟩ := by
        apply Fin.ext; simpa [idx_val]
      simp [hfin]
    have hright :
        y (e.symm (Fin.natAdd n (Fin.natAdd n i))) = y ⟨2 * n + i.val, by omega⟩ := by
      have idx_val : (e.symm (Fin.natAdd n (Fin.natAdd n i))).val = n + (n + i.val) := by simp [e]
      have hfin : e.symm (Fin.natAdd n (Fin.natAdd n i)) = ⟨2 * n + i.val, by omega⟩ := by
        apply Fin.ext; simp [idx_val, two_mul, add_assoc]
      simp [hfin]
    have hsplit :
        (augmentedMatrix P.A).mulVec y i =
          (∑ j : Fin n, P.A i j * y ⟨j.val, by omega⟩) +
          (∑ j : Fin n, (-P.A i j) * y ⟨n + j.val, by omega⟩) +
          y ⟨2 * n + i.val, by omega⟩ := by
      calc (augmentedMatrix P.A).mulVec y i =
            (∑ j : Fin n, P.A i j * y (e.symm (Fin.castAdd (n + m) j))) +
            (∑ j : Fin n, (-P.A i j) * y (e.symm (Fin.natAdd n (Fin.castAdd m j)))) +
            y (e.symm (Fin.natAdd n (Fin.natAdd n i))) := hsplit'
        _ = _ := by rw [hleft, hmid, hright]
    have hmul_extract :
        (∑ j : Fin n, P.A i j * y ⟨j.val, by omega⟩) +
        (∑ j : Fin n, (-P.A i j) * y ⟨n + j.val, by omega⟩) =
          (P.A.mulVec (extractX y)) i := by
      simpa using (mulVec_extractX_decomp (A := P.A) (y := y) i).symm
    have hrow' :
        (∑ j : Fin n, P.A i j * y ⟨j.val, by omega⟩) +
        (∑ j : Fin n, (-P.A i j) * y ⟨n + j.val, by omega⟩) +
        y ⟨2 * n + i.val, by omega⟩ = P.b i := by
      calc _ = (augmentedMatrix P.A).mulVec y i := by symm; exact hsplit
        _ = P.b i := hrow
    have hrow'' : (P.A.mulVec (extractX y)) i + y ⟨2 * n + i.val, by omega⟩ = P.b i := by
      have hrow'' := hrow'; rw [hmul_extract] at hrow''; exact hrow''
    linarith [hrow'']
  have hslack_nonneg : 0 ≤ y ⟨2 * n + i.val, by omega⟩ := hnonneg _
  linarith [hslack, hslack_nonneg]

/-- Main correctness theorem: Ax ≤ b is feasible iff By = c, y ≥ 0 is feasible -/
theorem reduction_correct {m n : ℕ} (P : InequalityForm m n) :
    P.isFeasible ↔ (toStandardForm P).isFeasible :=
  ⟨fun ⟨x, hx⟩ => ⟨constructY P x, reduction_forward P x hx⟩,
   fun ⟨y, hy⟩ => ⟨extractX y, reduction_backward P y hy⟩⟩

end
