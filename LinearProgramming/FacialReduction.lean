/-
Facial reduction for cone feasibility (orthant intersection) with
dimension reduction via active coordinates.
-/

import LinearProgramming.Defs
import LinearProgramming.Preprocess
import LinearAlgebraHelpers.CoordSelect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Matrix
open LinearAlgebraHelpers

namespace LinearProgramming

/-! ## Cone feasibility system -/

/-- Feasibility for the cone `ker B ∩ R^p_+`. -/
abbrev ConeFeasible {q p : ℕ} (B : Mat q p) (y : Vec p) : Prop :=
  B.mulVec y = 0 ∧ y ∈ nonnegOrthant p

structure ConeSystem (q p : ℕ) where
  B : Mat q p

namespace ConeSystem

variable {q p : ℕ}

def feasible (C : ConeSystem q p) (y : Vec p) : Prop :=
  ConeFeasible C.B y

def hasNonzero (C : ConeSystem q p) : Prop :=
  ∃ y, C.feasible y ∧ y ≠ 0

end ConeSystem

/-! ## Inequality-form encoding -/

def stackIneq {m₁ m₂ n : ℕ} (P₁ : InequalityForm m₁ n) (P₂ : InequalityForm m₂ n) :
    InequalityForm (m₁ + m₂) n :=
  { A := stackMatrices P₁.A P₂.A, b := appendVecs P₁.b P₂.b }

lemma stackMatrices_mulVec_left {m₁ m₂ n : ℕ} (A₁ : Mat m₁ n) (A₂ : Mat m₂ n) (x : Vec n)
    (i : Fin m₁) :
    (stackMatrices A₁ A₂).mulVec x ⟨i.1, by omega⟩ = (A₁.mulVec x) i := by
  simp [Matrix.mulVec, dotProduct, stackMatrices, i.isLt]

lemma stackMatrices_mulVec_right {m₁ m₂ n : ℕ} (A₁ : Mat m₁ n) (A₂ : Mat m₂ n) (x : Vec n)
    (i : Fin m₂) :
    (stackMatrices A₁ A₂).mulVec x ⟨i.1 + m₁, by omega⟩ = (A₂.mulVec x) i := by
  have hi : ¬ (i.1 + m₁ < m₁) := by omega
  simp [Matrix.mulVec, dotProduct, stackMatrices, hi]

lemma stackIneq_feasible_iff {m₁ m₂ n : ℕ} (P₁ : InequalityForm m₁ n)
    (P₂ : InequalityForm m₂ n) (x : Vec n) :
    (stackIneq P₁ P₂).feasible x ↔ P₁.feasible x ∧ P₂.feasible x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have h' := h ⟨i.1, by omega⟩
      have hA : (stackMatrices P₁.A P₂.A).mulVec x ⟨i.1, by omega⟩ = (P₁.A.mulVec x) i :=
        stackMatrices_mulVec_left (A₁ := P₁.A) (A₂ := P₂.A) (x := x) i
      simpa [stackIneq, hA, appendVecs_apply, i.isLt] using h'
    · intro i
      have h' := h ⟨i.1 + m₁, by omega⟩
      have hA : (stackMatrices P₁.A P₂.A).mulVec x ⟨i.1 + m₁, by omega⟩ = (P₂.A.mulVec x) i :=
        stackMatrices_mulVec_right (A₁ := P₁.A) (A₂ := P₂.A) (x := x) i
      have hi : ¬ (i.1 + m₁ < m₁) := by omega
      simpa [stackIneq, hA, appendVecs_apply, hi, Nat.add_sub_cancel] using h'
  · rintro ⟨h₁, h₂⟩
    intro i
    by_cases hi : i.1 < m₁
    · have : (P₁.A.mulVec x) ⟨i.1, hi⟩ ≤ P₁.b ⟨i.1, hi⟩ := h₁ ⟨i.1, hi⟩
      have hA : (stackMatrices P₁.A P₂.A).mulVec x i = (P₁.A.mulVec x) ⟨i.1, hi⟩ := by
        -- `i` already has `i.1 < m₁`, so use the left lemma
        simpa using (stackMatrices_mulVec_left (A₁ := P₁.A) (A₂ := P₂.A) (x := x) ⟨i.1, hi⟩)
      simpa [stackIneq, hA, appendVecs_apply, hi] using this
    · have hi' : m₁ ≤ i.1 := Nat.le_of_not_lt hi
      have hidx : i.1 - m₁ < m₂ := by omega
      have : (P₂.A.mulVec x) ⟨i.1 - m₁, hidx⟩ ≤ P₂.b ⟨i.1 - m₁, hidx⟩ :=
        h₂ ⟨i.1 - m₁, hidx⟩
      have hA : (stackMatrices P₁.A P₂.A).mulVec x i = (P₂.A.mulVec x) ⟨i.1 - m₁, hidx⟩ := by
        -- rewrite `i` as the right-side index
        have hi0 : ¬ (i.1 < m₁) := hi
        -- compute with `stackMatrices` directly
        simp [Matrix.mulVec, dotProduct, stackMatrices, hi0]  -- yields desired equality
      simpa [stackIneq, hA, appendVecs_apply, hi, hi'] using this

def vecOfFun {p : ℕ} (f : Fin p → ℝ) : Vec p :=
  WithLp.toLp 2 f

@[simp]
lemma vecOfFun_apply {p : ℕ} (f : Fin p → ℝ) (i : Fin p) :
    vecOfFun f i = f i := by
  simp [vecOfFun, PiLp.toLp_apply]

def rowVec {p : ℕ} (v : Vec p) : Mat 1 p :=
  fun _ j => v j

def singleVec (c : ℝ) : Vec 1 :=
  vecOfFun (fun _ => c)

def coneIneq {q p : ℕ} (B : Mat q p) : InequalityForm (q + q + p) p :=
  { A := stackMatrices (stackMatrices B (-B)) (-(1 : Mat p p)),
    b := appendVecs (appendVecs (0 : Vec q) (0 : Vec q)) (0 : Vec p) }

def lowerBoundIneq {p : ℕ} (i : Fin p) : InequalityForm 1 p :=
  { A := rowVec (vecOfFun (Pi.single i (-1))), b := singleVec (-1) }

def coneIneqWithLowerBound {q p : ℕ} (B : Mat q p) (i : Fin p) :
    InequalityForm (q + q + p + 1) p :=
  stackIneq (coneIneq B) (lowerBoundIneq i)

lemma coneIneq_feasible_iff {q p : ℕ} (B : Mat q p) (y : Vec p) :
    (coneIneq B).feasible y ↔ ConeFeasible B y := by
  constructor
  · intro h
    have hsplit :
        (stackIneq
          (stackIneq { A := B, b := (0 : Vec q) } { A := -B, b := (0 : Vec q) })
          { A := -(1 : Mat p p), b := (0 : Vec p) }).feasible y := by
      simpa [coneIneq, stackIneq] using h
    rcases
        (stackIneq_feasible_iff
          (P₁ := stackIneq { A := B, b := (0 : Vec q) } { A := -B, b := (0 : Vec q) })
          (P₂ := { A := -(1 : Mat p p), b := (0 : Vec p) }) y).1 hsplit with
      ⟨hB, hnonneg⟩
    rcases
        (stackIneq_feasible_iff
          (P₁ := { A := B, b := (0 : Vec q) })
          (P₂ := { A := -B, b := (0 : Vec q) }) y).1 hB with
      ⟨hBpos, hBneg⟩
    have hzero : B.mulVec y = 0 := by
      ext i
      have hpos : (B.mulVec y) i ≤ 0 := hBpos i
      have hneg : ((-B).mulVec y) i ≤ 0 := hBneg i
      have hneg' : -(B.mulVec y) i ≤ 0 := by
        simpa [Matrix.neg_mulVec] using hneg
      have hge : 0 ≤ (B.mulVec y) i := by
        linarith
      exact le_antisymm hpos hge
    have hnn : y ∈ nonnegOrthant p := by
      intro i
      have hle : ((-(1 : Mat p p)).mulVec y) i ≤ 0 := hnonneg i
      have hle' : -(y i) ≤ 0 := by
        simpa [Matrix.neg_mulVec, Matrix.one_mulVec] using hle
      linarith
    exact ⟨hzero, hnn⟩
  · rintro ⟨hB, hnn⟩
    have hBpos : (InequalityForm.feasible { A := B, b := (0 : Vec q) } y) := by
      intro i
      have h0 : (B.mulVec y) i = 0 := by
        simpa using congrArg (fun v => v i) hB
      exact le_of_eq h0
    have hBneg : (InequalityForm.feasible { A := -B, b := (0 : Vec q) } y) := by
      intro i
      have h0 : (B.mulVec y) i = 0 := by
        simpa using congrArg (fun v => v i) hB
      have hneg : (-B).mulVec y = -(B.mulVec y) := by
        simpa using (Matrix.neg_mulVec (v := y) (A := B))
      have h0' : ((-B).mulVec y) i = 0 := by
        have hneg' := congrArg (fun v => v i) hneg
        simpa [h0] using hneg'
      exact le_of_eq h0'
    have hnonneg : (InequalityForm.feasible { A := -(1 : Mat p p), b := (0 : Vec p) } y) := by
      intro i
      have hy : 0 ≤ y i := hnn i
      have hle : -(y i) ≤ 0 := by linarith
      simpa [Matrix.neg_mulVec, Matrix.one_mulVec] using hle
    have hstack :
        (stackIneq
          (stackIneq { A := B, b := (0 : Vec q) } { A := -B, b := (0 : Vec q) })
          { A := -(1 : Mat p p), b := (0 : Vec p) }).feasible y := by
      exact
        (stackIneq_feasible_iff _ _ _).2
          ⟨(stackIneq_feasible_iff _ _ _).2 ⟨hBpos, hBneg⟩, hnonneg⟩
    simpa [coneIneq, stackIneq] using hstack

lemma lowerBoundIneq_feasible_iff {p : ℕ} (i : Fin p) (y : Vec p) :
    (lowerBoundIneq i).feasible y ↔ y i ≥ 1 := by
  constructor
  · intro h
    have h' := h ⟨0, by decide⟩
    have hrow :
        ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ = (-1 : ℝ) * y i := by
      classical
      have hrow' :
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ =
            (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp := by
        simp [rowVec, vecOfFun, Matrix.mulVec]
      have hdot : (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp = (-1 : ℝ) * y.ofLp i := by
        classical
        unfold dotProduct
        have hsum :=
          Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin p)))
            (f := fun j => (if j = i then -1 else 0) * y.ofLp j) i
            (by exact Finset.mem_univ i)
            (fun j _ hij => by
              simp [if_neg hij])
        simpa using hsum
      -- combine the dotProduct computation with the row-vector equality
      have hrow'' :
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ =
            (-1 : ℝ) * y.ofLp i := by
        calc
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩
              = (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp := hrow'
          _ = (-1 : ℝ) * y.ofLp i := hdot
      simpa using hrow''
    have hb : singleVec (-1) ⟨0, by decide⟩ = (-1 : ℝ) := by
      simp [singleVec, vecOfFun, PiLp.toLp_apply]
    have h'' := h'
    rw [lowerBoundIneq, hrow, hb] at h''
    linarith
  · intro hy
    intro i'
    have hi' : i' = ⟨0, by decide⟩ := by
      apply Fin.ext
      simp
    subst hi'
    have h' : (-1 : ℝ) * y i ≤ -1 := by linarith
    have hrow :
        ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ = (-1 : ℝ) * y i := by
      classical
      have hrow' :
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ =
            (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp := by
        simp [rowVec, vecOfFun, Matrix.mulVec]
      have hdot : (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp = (-1 : ℝ) * y.ofLp i := by
        classical
        unfold dotProduct
        have hsum :=
          Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin p)))
            (f := fun j => (if j = i then -1 else 0) * y.ofLp j) i
            (by exact Finset.mem_univ i)
            (fun j _ hij => by
              simp [if_neg hij])
        simpa using hsum
      have hrow'' :
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩ =
            (-1 : ℝ) * y.ofLp i := by
        calc
          ((rowVec (vecOfFun (Pi.single i (-1)))).mulVec y) ⟨0, by decide⟩
              = (fun j => if j = i then -1 else 0) ⬝ᵥ y.ofLp := hrow'
          _ = (-1 : ℝ) * y.ofLp i := hdot
      simpa using hrow''
    have hb : singleVec (-1) ⟨0, by decide⟩ = (-1 : ℝ) := by
      simp [singleVec, vecOfFun, PiLp.toLp_apply]
    -- rewrite the goal using `hrow` and `hb`, then close with `h'`
    rw [lowerBoundIneq, hrow, hb]
    exact h'

lemma coneIneqWithLowerBound_feasible_iff {q p : ℕ} (B : Mat q p) (i : Fin p) (y : Vec p) :
    (coneIneqWithLowerBound B i).feasible y ↔
      ConeFeasible B y ∧ y i ≥ 1 := by
  have h := stackIneq_feasible_iff (P₁ := coneIneq B) (P₂ := lowerBoundIneq i) y
  constructor
  · intro hfeas
    rcases h.1 hfeas with ⟨hcone, hlow⟩
    exact ⟨(coneIneq_feasible_iff B y).1 hcone, (lowerBoundIneq_feasible_iff i y).1 hlow⟩
  · rintro ⟨hcone, hlow⟩
    exact h.2 ⟨(coneIneq_feasible_iff B y).2 hcone, (lowerBoundIneq_feasible_iff i y).2 hlow⟩

/-! ## Active coordinates via a feasibility solver -/

def activeWitness {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p) (i : Fin p) :
    Option (Vec p) :=
  solver.solve (coneIneqWithLowerBound B i)

def isActive {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p) (i : Fin p) : Prop :=
  (activeWitness solver B i).isSome

noncomputable def activeCoords {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p) :
    Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun i => isActive solver B i)

def witnessVec {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p) (i : Fin p) :
    Vec p :=
  match activeWitness solver B i with
  | some y => y
  | none => 0

lemma activeWitness_sound {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p)
    (i : Fin p) {y : Vec p} :
    activeWitness solver B i = some y →
      ConeFeasible B y ∧ y i ≥ 1 := by
  intro h
  have h' : (coneIneqWithLowerBound B i).feasible y :=
    solver.sound (P := coneIneqWithLowerBound B i) h
  exact (coneIneqWithLowerBound_feasible_iff B i y).1 h'

lemma activeCoords_mem_iff {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p)
    (i : Fin p) :
    i ∈ activeCoords solver B ↔ isActive solver B i := by
  classical
  simp [activeCoords, isActive]

lemma isActive_iff_exists {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p)
    (i : Fin p) :
    isActive solver B i ↔ ∃ y, ConeFeasible B y ∧ y i ≥ 1 := by
  constructor
  · intro hact
    rcases (Option.isSome_iff_exists).1 hact with ⟨y, hy⟩
    exact ⟨y, activeWitness_sound solver B i hy⟩
  · rintro ⟨y, hy, hyi⟩
    have hfeas : (coneIneqWithLowerBound B i).feasible y :=
      (coneIneqWithLowerBound_feasible_iff B i y).2 ⟨hy, hyi⟩
    obtain ⟨x, hx⟩ := solver.complete (P := coneIneqWithLowerBound B i) ⟨y, hfeas⟩
    exact (Option.isSome_iff_exists).2 ⟨x, hx⟩

lemma inactive_implies_zero {q p : ℕ} (solver : StronglyPolyFeasibilitySolver) (B : Mat q p)
    (i : Fin p) :
    i ∉ activeCoords solver B →
      ∀ y, ConeFeasible B y → y i = 0 := by
  intro hnot y hy
  by_contra hpos
  have hyi_nonneg : 0 ≤ y i := hy.2 i
  have hyi_pos : 0 < y i := lt_of_le_of_ne hyi_nonneg (Ne.symm hpos)
  let c : ℝ := 1 / y i
  have cpos : 0 < c := one_div_pos.mpr hyi_pos
  have hy' : ConeFeasible B (c • y) := by
    have hmul : B.mulVec (c • y) = c • B.mulVec y := by
      simpa using (Matrix.mulVec_smul (M := B) (b := c) (v := y))
    have hB' : B.mulVec (c • y) = 0 := by
      calc
        B.mulVec (c • y) = c • B.mulVec y := hmul
        _ = 0 := by simp [hy.1]
    have hnn' : (c • y) ∈ nonnegOrthant p := by
      intro j
      have : 0 ≤ y j := hy.2 j
      exact mul_nonneg (le_of_lt cpos) this
    exact ⟨hB', hnn'⟩
  have hyi' : (c • y) i ≥ 1 := by
    have hne : y i ≠ 0 := ne_of_gt hyi_pos
    have hcalc : (c • y) i = 1 := by
      simp [c, Pi.smul_apply, hne]
    exact le_of_eq hcalc.symm
  have hact : isActive solver B i := (isActive_iff_exists solver B i).2 ⟨c • y, hy', hyi'⟩
  have hmem : i ∈ activeCoords solver B := (activeCoords_mem_iff solver B i).2 hact
  exact hnot hmem

/-! ## Reduced dimension system -/

def reduceMatrix {q p : ℕ} (B : Mat q p) (S : Finset (Fin p)) : Mat q S.card :=
  fun i j => B i (coordEmb S j)

def projectConeVec {p : ℕ} (S : Finset (Fin p)) (y : Vec p) : Vec S.card :=
  projectVec S y

def expandConeVec {p : ℕ} (S : Finset (Fin p)) (x : Vec S.card) : Vec p :=
  expandVec S x

lemma sum_coordEmb_eq_sum {p : ℕ} (S : Finset (Fin p)) (f : Fin p → ℝ) :
    (∑ j : Fin S.card, f (coordEmb S j)) = Finset.sum S f := by
  classical
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin S.card)) (fun j => f (coordEmb S j)) =
        Finset.sum S f := by
    refine Finset.sum_bij
      (s := (Finset.univ : Finset (Fin S.card))) (t := S)
      (f := fun j => f (coordEmb S j)) (g := f)
      (i := fun j _ => coordEmb S j) ?_ ?_ ?_ ?_
    · intro j hj
      exact coordEmb_mem (S := S) j
    · intro j₁ hj₁ j₂ hj₂ h
      exact (coordEmb S).inj' h
    · intro k hk
      have himage : Finset.image (coordEmb S) Finset.univ = S := by
        simpa [coordEmb] using (Finset.image_orderEmbOfFin_univ (s := S) (h := rfl))
      have hk' : k ∈ Finset.image (coordEmb S) Finset.univ := by
        simpa [himage] using hk
      rcases Finset.mem_image.mp hk' with ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · intro j hj
      rfl
  simpa using hsum

lemma reduceMatrix_mulVec {q p : ℕ} (B : Mat q p) (S : Finset (Fin p)) (x : Vec S.card) :
    (reduceMatrix B S).mulVec x = B.mulVec (expandConeVec S x) := by
  classical
  ext i
  have hproj : ∀ j, expandConeVec S x (coordEmb S j) = x j := by
    intro j
    have h := project_expand (S := S) (x := x)
    have h' := congrArg (fun v => v j) h
    simpa [projectVec, expandConeVec] using h'
  have hsum1 :
      (∑ j : Fin S.card, B i (coordEmb S j) * x j) =
        ∑ j : Fin S.card, B i (coordEmb S j) * expandConeVec S x (coordEmb S j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [hproj j]
  have hsum2 :
      (∑ j : Fin S.card, B i (coordEmb S j) * expandConeVec S x (coordEmb S j)) =
        Finset.sum S (fun k => B i k * expandConeVec S x k) := by
    simpa using (sum_coordEmb_eq_sum (S := S) (f := fun k => B i k * expandConeVec S x k))
  have hsum3 :
      Finset.sum S (fun k => B i k * expandConeVec S x k) =
        ∑ k, B i k * expandConeVec S x k := by
    classical
    let f : Fin p → ℝ := fun k => B i k * expandConeVec S x k
    have hsubset : S ⊆ (Finset.univ : Finset (Fin p)) := by
      intro k hk
      exact Finset.mem_univ k
    have hzero :
        ∀ k ∈ (Finset.univ : Finset (Fin p)), k ∉ S → f k = 0 := by
      intro k hk hknot
      simp [f, expandConeVec, expandVec, hknot]
    have hsum := (Finset.sum_subset (s₁ := S) (s₂ := (Finset.univ : Finset (Fin p))) hsubset hzero)
    simpa [f] using hsum
  calc
    (reduceMatrix B S).mulVec x i
        = ∑ j : Fin S.card, B i (coordEmb S j) * x j := by
            simp [reduceMatrix, Matrix.mulVec, dotProduct]
    _ = ∑ j : Fin S.card, B i (coordEmb S j) * expandConeVec S x (coordEmb S j) := hsum1
    _ = Finset.sum S (fun k => B i k * expandConeVec S x k) := hsum2
    _ = ∑ k, B i k * expandConeVec S x k := hsum3
    _ = (B.mulVec (expandConeVec S x)) i := by
          simp [Matrix.mulVec, dotProduct]

lemma project_feasible_of_zeroOutside {q p : ℕ} (B : Mat q p) (S : Finset (Fin p))
    {y : Vec p} (hy : ConeFeasible B y) (hz : zeroOutside S y) :
    (reduceMatrix B S).mulVec (projectConeVec S y) = 0 ∧
      projectConeVec S y ∈ nonnegOrthant S.card := by
  have hproj : expandConeVec S (projectConeVec S y) = y :=
    expand_project_of_zeroOutside (S := S) (x := y) hz
  have hker : (reduceMatrix B S).mulVec (projectConeVec S y) = 0 := by
    calc
      (reduceMatrix B S).mulVec (projectConeVec S y)
          = B.mulVec (expandConeVec S (projectConeVec S y)) :=
            reduceMatrix_mulVec (B := B) (S := S) (x := projectConeVec S y)
      _ = B.mulVec y := by simpa [hproj]
      _ = 0 := hy.1
  have hnn : projectConeVec S y ∈ nonnegOrthant S.card := by
    intro j
    have : 0 ≤ y (coordEmb S j) := hy.2 (coordEmb S j)
    simpa [projectConeVec, projectVec] using this
  exact ⟨hker, hnn⟩

lemma expand_feasible {q p : ℕ} (B : Mat q p) (S : Finset (Fin p))
    {x : Vec S.card} (hx : (reduceMatrix B S).mulVec x = 0 ∧ x ∈ nonnegOrthant S.card) :
    ConeFeasible B (expandConeVec S x) := by
  have hker : B.mulVec (expandConeVec S x) = 0 := by
    have hmul := reduceMatrix_mulVec (B := B) (S := S) (x := x)
    calc
      B.mulVec (expandConeVec S x) = (reduceMatrix B S).mulVec x := by
        simpa using hmul.symm
      _ = 0 := hx.1
  have hnn : expandConeVec S x ∈ nonnegOrthant p := by
    intro i
    by_cases hi : i ∈ S
    · have hi' : (expandConeVec S x) i = x ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) := by
        simp [expandConeVec, expandVec, hi]
      have hx' : 0 ≤ x ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) := hx.2 _
      simpa [hi'] using hx'
    · simp [expandConeVec, expandVec, hi]
  exact ⟨hker, hnn⟩

/-! ## Strict interior after facial reduction -/

theorem exists_strict_interior_of_active {q p : ℕ} (solver : StronglyPolyFeasibilitySolver)
    (B : Mat q p) :
    ∃ x : Vec (activeCoords solver B).card,
      (reduceMatrix B (activeCoords solver B)).mulVec x = 0 ∧
      (∀ j, 0 < x j) := by
  classical
  let S := activeCoords solver B
  by_cases hS : S = ∅
  · refine ⟨0, ?_, ?_⟩
    · simp [reduceMatrix, S, hS]
    ·
      have : ∀ j : Fin 0, 0 < (0 : Vec 0) j := by
        intro j
        exact (Fin.elim0 j)
      simpa [S, hS] using this
  ·
    have hmem : ∀ i ∈ S, ∃ y, activeWitness solver B i = some y := by
      intro i hi
      have hact : isActive solver B i := (activeCoords_mem_iff solver B i).1 hi
      exact (Option.isSome_iff_exists).1 hact
    classical
    let y : Fin p → Vec p := fun i =>
      if h : i ∈ S then Classical.choose (hmem i h) else 0
    have hy : ∀ i (hi : i ∈ S), activeWitness solver B i = some (y i) := by
      intro i hi
      have hchoose := Classical.choose_spec (hmem i hi)
      have hyi : y i = Classical.choose (hmem i hi) := by
        simp [y, hi]
      simpa [hyi] using hchoose
    let xsum : Vec S.card := Finset.sum S (fun i => projectConeVec S (y i))
    have hker_i : ∀ i ∈ S, (reduceMatrix B S).mulVec (projectConeVec S (y i)) = 0 := by
      intro i hi
      have hyi := activeWitness_sound solver B i (hy i hi)
      have hzero : zeroOutside S (y i) := by
        intro k hk
        have hk' : k ∉ activeCoords solver B := by
          simpa [S] using hk
        exact inactive_implies_zero solver B k hk' (y i) hyi.1
      exact (project_feasible_of_zeroOutside (B := B) (S := S) (y := y i) hyi.1 hzero).1
    have hsum : (reduceMatrix B S).mulVec xsum =
        Finset.sum S (fun i => (reduceMatrix B S).mulVec (projectConeVec S (y i))) := by
      -- use linearity of `mulVec` to pull out the sum
      classical
      dsimp [xsum]
      have hxsum :
          (∑ i ∈ S, projectConeVec S (y i)).ofLp =
            ∑ i ∈ S, (projectConeVec S (y i)).ofLp := by
        simp
      -- rewrite the argument to `mulVec` using `hxsum`
      rw [hxsum]
      calc
        reduceMatrix B S *ᵥ ∑ i ∈ S, (projectConeVec S (y i)).ofLp
            = (Matrix.mulVecLin (reduceMatrix B S)) (∑ i ∈ S, (projectConeVec S (y i)).ofLp) := by
                simpa using
                  (Matrix.mulVecLin_apply (M := reduceMatrix B S)
                    (v := ∑ i ∈ S, (projectConeVec S (y i)).ofLp)).symm
        _ = ∑ i ∈ S, (Matrix.mulVecLin (reduceMatrix B S)) ((projectConeVec S (y i)).ofLp) := by
                simpa using
                  (_root_.map_sum (Matrix.mulVecLin (reduceMatrix B S))
                    (fun i => (projectConeVec S (y i)).ofLp) S)
        _ = ∑ i ∈ S, reduceMatrix B S *ᵥ (projectConeVec S (y i)).ofLp := by
                simp [Matrix.mulVecLin_apply]
    have hker : (reduceMatrix B S).mulVec xsum = 0 := by
      calc
        (reduceMatrix B S).mulVec xsum
            = Finset.sum S (fun i => (reduceMatrix B S).mulVec (projectConeVec S (y i))) := hsum
        _ = Finset.sum S (fun _ => 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hker_i i hi]
        _ = 0 := by simp
    have hpos : ∀ j, 0 < xsum j := by
      intro j
      have hj_mem : coordEmb S j ∈ S := coordEmb_mem (S := S) j
      have hyj := activeWitness_sound solver B (coordEmb S j) (hy (coordEmb S j) hj_mem)
      have hterm_pos : 0 < (projectConeVec S (y (coordEmb S j))) j := by
        have hge : (y (coordEmb S j)) (coordEmb S j) ≥ 1 := hyj.2
        have hpos' : 0 < (y (coordEmb S j)) (coordEmb S j) := by linarith
        simpa [projectConeVec, projectVec] using hpos'
      have hnonneg : ∀ i ∈ S, 0 ≤ (projectConeVec S (y i)) j := by
        intro i hi
        have hyi := activeWitness_sound solver B i (hy i hi)
        have hnn : y i ∈ nonnegOrthant p := hyi.1.2
        exact hnn (coordEmb S j)
      have hle : (projectConeVec S (y (coordEmb S j))) j ≤ xsum j := by
        have hle' :=
          Finset.single_le_sum (s := S) (f := fun i => (projectConeVec S (y i)) j)
            (by intro i hi; exact hnonneg i hi) hj_mem
        simpa [xsum] using hle'
      exact lt_of_lt_of_le hterm_pos hle
    exact ⟨xsum, hker, hpos⟩

end LinearProgramming
