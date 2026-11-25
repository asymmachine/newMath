/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.SymmDiff

/-!
# Zero-Bloat Gaussian Elimination in the F2-Linear Basis (XOR-SAT)

This module formalizes the zero-bloat renormalization theorem for XOR-SAT (linear systems over
`GF(2)`), establishing that variable-elimination renormalizability depends on the algebraic basis
(Base-Dependent Renormalizability).

Whereas variable elimination (Davis-Putnam resolution) in the conjunctive normal form (CNF) basis
can suffer quadratic clause blowup per elimination step, variable elimination in the `GF(2)`-linear
basis via pivot Gaussian elimination (`gaussElimVar`) is strictly non-expanding: eliminating a
variable that appears in the system strictly decreases the number of equations while preserving
exact equisatisfiability.

## Main definitions

* `Assign n`: A Boolean assignment `Fin n → Bool` to `n` variables.
* `LinEq n`: A single `GF(2)`-linear equation specified by a finite set of variables
  `vars : Finset (Fin n)` and a constant term `rhs : Bool`.
* `evalXor σ s`: The parity (XOR fold) of `σ` over a finite set of variables `s`.
* `SatEq σ eq`, `SatSys σ sys`, `Satisfiable sys`: Satisfaction semantics for equations and
  systems of equations.
* `addEq e₁ e₂`: Addition of two `GF(2)`-linear equations via symmetric difference of variable sets
  and XOR of right-hand sides.
* `gaussElimVar v sys`: Pivot Gaussian elimination of a single variable `v` from `sys`.
* `gaussElimList vs sys`: Iterated Gaussian elimination along a list of variables `vs`.

## Main results

* `evalXor_symmDiff`: `evalXor σ (symmDiff s₁ s₂) = xor (evalXor σ s₁) (evalXor σ s₂)`.
* `not_mem_addEq_vars`: Adding two equations that both contain `v` cancels `v`.
* `gaussElimVar_elim`: The variable `v` does not appear in any equation of `gaussElimVar v sys`.
* `gaussElimVar_length_le`: `(gaussElimVar v sys).length ≤ sys.length`.
* `gaussElimVar_length_lt`: If `v` appears in `sys`, then
  `(gaussElimVar v sys).length < sys.length`.
* `gaussElimVar_equisatisfiable`: `Satisfiable (gaussElimVar v sys) ↔ Satisfiable sys`.
* `gaussElimList_length_le` and `gaussElimList_equisatisfiable`: Zero-bloat size monotonicity and
  equisatisfiability along any elimination sequence.
-/

namespace Mathmatica.XORSATBasis

/-! ## Boolean XOR Algebra and F2-Linear Equations -/

local instance : Std.Commutative xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative xor := ⟨Bool.xor_assoc⟩

/-- A Boolean assignment to `n` variables. -/
abbrev Assign (n : ℕ) := Fin n → Bool

/-- A single `GF(2)`-linear equation `⨁_{i ∈ vars} σ(i) = rhs`. -/
structure LinEq (n : ℕ) where
  /-- The set of variables appearing with coefficient `1` on the left-hand side. -/
  vars : Finset (Fin n)
  /-- The constant parity on the right-hand side. -/
  rhs : Bool
  deriving DecidableEq

/-- A system of `GF(2)`-linear equations (an XOR-SAT instance). -/
abbrev LinSys (n : ℕ) := List (LinEq n)

/-- Evaluate the XOR sum of an assignment `σ` over a finite set of variables `s`. -/
def evalXor {n : ℕ} (σ : Assign n) (s : Finset (Fin n)) : Bool :=
  s.fold xor false σ

/-- An assignment `σ` satisfies a linear equation `eq` if its XOR sum over `eq.vars` equals
`eq.rhs`. -/
def SatEq {n : ℕ} (σ : Assign n) (eq : LinEq n) : Prop :=
  evalXor σ eq.vars = eq.rhs

/-- An assignment `σ` satisfies a linear system `sys` if it satisfies every equation in `sys`. -/
def SatSys {n : ℕ} (σ : Assign n) (sys : LinSys n) : Prop :=
  ∀ eq ∈ sys, SatEq σ eq

/-- A linear system is satisfiable if there exists an assignment satisfying all its equations. -/
def Satisfiable {n : ℕ} (sys : LinSys n) : Prop :=
  ∃ σ : Assign n, SatSys σ sys

/-- Update an assignment `σ` at variable `v` to take the Boolean value `b`. -/
def updateAssign {n : ℕ} (σ : Assign n) (v : Fin n) (b : Bool) : Assign n :=
  fun i => if i = v then b else σ i

/-! ## Algebraic Properties of `evalXor` and Symmetric Difference -/

@[simp]
theorem evalXor_empty {n : ℕ} (σ : Assign n) : evalXor σ ∅ = false := by
  simp [evalXor]

theorem evalXor_insert {n : ℕ} (σ : Assign n) {v : Fin n} {s : Finset (Fin n)} (hv : v ∉ s) :
    evalXor σ (insert v s) = xor (σ v) (evalXor σ s) := by
  simp [evalXor, Finset.fold_insert hv]

theorem evalXor_erase {n : ℕ} (σ : Assign n) {v : Fin n} {s : Finset (Fin n)} (hv : v ∈ s) :
    evalXor σ s = xor (σ v) (evalXor σ (s.erase v)) := by
  have h := evalXor_insert σ (Finset.notMem_erase v s)
  rwa [Finset.insert_erase hv] at h

theorem evalXor_union_disjoint {n : ℕ} (σ : Assign n) {s₁ s₂ : Finset (Fin n)}
    (h : Disjoint s₁ s₂) :
    evalXor σ (s₁ ∪ s₂) = xor (evalXor σ s₁) (evalXor σ s₂) := by
  induction s₁ using Finset.induction_on with
  | empty => simp [evalXor_empty]
  | @insert a s ha ih =>
    have hdisj : Disjoint s s₂ := Disjoint.mono_left (Finset.subset_insert a s) h
    have ha₂ : a ∉ s₂ := Finset.disjoint_left.mp h (Finset.mem_insert_self a s)
    have haU : a ∉ s ∪ s₂ := by simp [ha, ha₂]
    rw [Finset.insert_union, evalXor_insert σ haU, evalXor_insert σ ha, ih hdisj, Bool.xor_assoc]

/-- `evalXor` is a group homomorphism from `(Finset (Fin n), symmDiff)` to `(Bool, xor)`. -/
theorem evalXor_symmDiff {n : ℕ} (σ : Assign n) (s₁ s₂ : Finset (Fin n)) :
    evalXor σ (symmDiff s₁ s₂) = xor (evalXor σ s₁) (evalXor σ s₂) := by
  have he1 : evalXor σ s₁ = xor (evalXor σ (s₁ \ s₂)) (evalXor σ (s₁ ∩ s₂)) := by
    rw [← evalXor_union_disjoint σ (Finset.disjoint_sdiff_inter s₁ s₂), Finset.sdiff_union_inter]
  have he2 : evalXor σ s₂ = xor (evalXor σ (s₂ \ s₁)) (evalXor σ (s₁ ∩ s₂)) := by
    have hd : Disjoint (s₂ \ s₁) (s₁ ∩ s₂) := by
      rw [Finset.inter_comm]
      exact Finset.disjoint_sdiff_inter s₂ s₁
    rw [← evalXor_union_disjoint σ hd, Finset.inter_comm, Finset.sdiff_union_inter]
  have hds : Disjoint (s₁ \ s₂) (s₂ \ s₁) :=
    Finset.disjoint_left.mpr fun _ hx₁ hx₂ =>
      (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_sdiff.mp hx₂).1
  rw [Finset.symmDiff_def, evalXor_union_disjoint σ hds, he1, he2]
  generalize evalXor σ (s₁ \ s₂) = a
  generalize evalXor σ (s₂ \ s₁) = b
  generalize evalXor σ (s₁ ∩ s₂) = c
  cases a <;> cases b <;> cases c <;> rfl

theorem evalXor_congr {n : ℕ} {σ₁ σ₂ : Assign n} {s : Finset (Fin n)}
    (h : ∀ x ∈ s, σ₁ x = σ₂ x) : evalXor σ₁ s = evalXor σ₂ s := by
  induction s using Finset.induction_on with
  | empty => simp [evalXor_empty]
  | @insert a s ha ih =>
    rw [evalXor_insert σ₁ ha, evalXor_insert σ₂ ha]
    rw [h a (Finset.mem_insert_self a s)]
    rw [ih (fun x hx => h x (Finset.mem_insert_of_mem hx))]

theorem evalXor_update_not_mem {n : ℕ} (σ : Assign n) {v : Fin n} (b : Bool)
    {s : Finset (Fin n)} (hv : v ∉ s) :
    evalXor (updateAssign σ v b) s = evalXor σ s := by
  apply evalXor_congr
  intro x hx
  have hne : x ≠ v := fun h => hv (h ▸ hx)
  simp [updateAssign, hne]

theorem evalXor_update_mem {n : ℕ} (σ : Assign n) {v : Fin n} (b : Bool)
    {s : Finset (Fin n)} (hv : v ∈ s) :
    evalXor (updateAssign σ v b) s = xor b (evalXor σ (s.erase v)) := by
  rw [evalXor_erase (updateAssign σ v b) hv]
  simp only [updateAssign, ↓reduceIte]
  rw [evalXor_update_not_mem σ b (Finset.notMem_erase v s)]

/-! ## Equation Addition over GF(2) -/

/-- Add two `GF(2)`-linear equations by taking the symmetric difference of their variable sets and
the XOR of their right-hand sides. -/
def addEq {n : ℕ} (e₁ e₂ : LinEq n) : LinEq n :=
  ⟨symmDiff e₁.vars e₂.vars, xor e₁.rhs e₂.rhs⟩

/-- If an assignment satisfies both `e₁` and `e₂`, then it satisfies `addEq e₁ e₂`. -/
theorem satEq_addEq {n : ℕ} {σ : Assign n} {e₁ e₂ : LinEq n}
    (h₁ : SatEq σ e₁) (h₂ : SatEq σ e₂) : SatEq σ (addEq e₁ e₂) := by
  unfold SatEq at h₁ h₂ ⊢
  simp only [addEq, evalXor_symmDiff, h₁, h₂]

/-- Assuming `σ` satisfies `e₁`, `σ` satisfies `e₂` if and only if it satisfies `addEq e₁ e₂`. -/
theorem satEq_of_satEq_addEq {n : ℕ} {σ : Assign n} {e₁ e₂ : LinEq n}
    (h₁ : SatEq σ e₁) (hadd : SatEq σ (addEq e₁ e₂)) : SatEq σ e₂ := by
  unfold SatEq at h₁ hadd ⊢
  simp only [addEq, evalXor_symmDiff, h₁] at hadd
  generalize evalXor σ e₂.vars = x at hadd ⊢
  generalize e₁.rhs = r₁ at hadd
  generalize e₂.rhs = r₂ at hadd ⊢
  cases r₁ <;> cases x <;> cases r₂ <;> simp at hadd ⊢

/-- Adding two equations that both contain `v` eliminates `v` from the resulting variable set. -/
theorem not_mem_addEq_vars {n : ℕ} {v : Fin n} {e₁ e₂ : LinEq n}
    (h₁ : v ∈ e₁.vars) (h₂ : v ∈ e₂.vars) : v ∉ (addEq e₁ e₂).vars := by
  simp [addEq, Finset.mem_symmDiff, h₁, h₂]

/-! ## Pivot Gaussian Elimination Renormalization Operator -/

/-- Eliminate variable `v` from a `GF(2)`-linear system `sys` by choosing the first equation
containing `v` as a pivot, adding it to all other equations containing `v`, and discarding the
pivot. -/
def gaussElimVar {n : ℕ} (v : Fin n) (sys : LinSys n) : LinSys n :=
  let withV := sys.filter (fun eq => decide (v ∈ eq.vars))
  let withoutV := sys.filter (fun eq => !decide (v ∈ eq.vars))
  match withV with
  | [] => withoutV
  | pivot :: rest => withoutV ++ rest.map (addEq pivot)

/-- After `gaussElimVar v sys`, the variable `v` no longer appears in any equation. -/
theorem gaussElimVar_elim {n : ℕ} (v : Fin n) (sys : LinSys n) :
    ∀ eq ∈ gaussElimVar v sys, v ∉ eq.vars := by
  unfold gaussElimVar
  dsimp only
  generalize hwith : sys.filter (fun eq => decide (v ∈ eq.vars)) = withV
  cases withV with
  | nil =>
    intro eq heq
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at heq
    exact heq.2
  | cons pivot rest =>
    intro eq heq
    rw [List.mem_append] at heq
    rcases heq with heq | heq
    · simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at heq
      exact heq.2
    · rw [List.mem_map] at heq
      rcases heq with ⟨e, he, rfl⟩
      have hpivot : pivot ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
        rw [hwith]
        exact List.mem_cons_self
      have he' : e ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
        rw [hwith]
        exact List.mem_cons_of_mem pivot he
      simp only [List.mem_filter, decide_eq_true_eq] at hpivot he'
      exact not_mem_addEq_vars hpivot.2 he'.2

private theorem length_filter_add_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : p a <;> simp [h] <;> omega

/-- **Zero-Bloat Size Monotonicity Theorem**: Pivot Gaussian elimination in the `GF(2)`-linear
basis never increases the number of equations. -/
theorem gaussElimVar_length_le {n : ℕ} (v : Fin n) (sys : LinSys n) :
    (gaussElimVar v sys).length ≤ sys.length := by
  unfold gaussElimVar
  dsimp only
  have hsum :
      (sys.filter (fun eq => decide (v ∈ eq.vars))).length +
      (sys.filter (fun eq => !decide (v ∈ eq.vars))).length = sys.length :=
    length_filter_add_not (fun eq => decide (v ∈ eq.vars)) sys
  generalize hwith : sys.filter (fun eq => decide (v ∈ eq.vars)) = withV
  rw [hwith] at hsum
  cases withV with
  | nil =>
    simp only [List.length_nil, Nat.zero_add] at hsum
    exact hsum.le
  | cons pivot rest =>
    simp only [List.length_append, List.length_map]
    simp only [List.length_cons] at hsum
    omega

/-- **Strict Size Decrease Theorem**: Whenever variable `v` appears in at least one equation of
`sys`, pivot Gaussian elimination strictly decreases the number of equations. -/
theorem gaussElimVar_length_lt {n : ℕ} (v : Fin n) (sys : LinSys n)
    (h : ∃ eq ∈ sys, v ∈ eq.vars) :
    (gaussElimVar v sys).length < sys.length := by
  unfold gaussElimVar
  dsimp only
  have hsum :
      (sys.filter (fun eq => decide (v ∈ eq.vars))).length +
      (sys.filter (fun eq => !decide (v ∈ eq.vars))).length = sys.length :=
    length_filter_add_not (fun eq => decide (v ∈ eq.vars)) sys
  have hne : sys.filter (fun eq => decide (v ∈ eq.vars)) ≠ [] := by
    rcases h with ⟨eq, heq, hv⟩
    intro hemp
    have hmem : eq ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
      simp [List.mem_filter, heq, hv]
    rw [hemp] at hmem
    exact List.not_mem_nil hmem
  generalize hwith : sys.filter (fun eq => decide (v ∈ eq.vars)) = withV
  rw [hwith] at hsum hne
  cases withV with
  | nil => exact absurd rfl hne
  | cons pivot rest =>
    simp only [List.length_append, List.length_map]
    simp only [List.length_cons] at hsum
    omega

/-- **Equisatisfiability Theorem**: Pivot Gaussian elimination of a variable `v` preserves exact
satisfiability of `GF(2)`-linear systems. -/
theorem gaussElimVar_equisatisfiable {n : ℕ} (v : Fin n) (sys : LinSys n) :
    Satisfiable (gaussElimVar v sys) ↔ Satisfiable sys := by
  constructor
  · -- Completeness: lift a satisfying assignment of the reduced system to the original system.
    rintro ⟨σ, hσ⟩
    unfold gaussElimVar at hσ
    dsimp only at hσ
    generalize hwith : sys.filter (fun eq => decide (v ∈ eq.vars)) = withV at hσ
    cases withV with
    | nil =>
      refine ⟨σ, fun eq heq => ?_⟩
      have hv : v ∉ eq.vars := by
        intro hv
        have hmem : eq ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
          simp [List.mem_filter, heq, hv]
        rw [hwith] at hmem
        exact List.not_mem_nil hmem
      apply hσ eq
      simp [List.mem_filter, heq, hv]
    | cons pivot rest =>
      have hpivot_mem : pivot ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
        rw [hwith]
        exact List.mem_cons_self
      simp only [List.mem_filter, decide_eq_true_eq] at hpivot_mem
      have hv_pivot : v ∈ pivot.vars := hpivot_mem.2
      let b : Bool := xor pivot.rhs (evalXor σ (pivot.vars.erase v))
      let σ' : Assign n := updateAssign σ v b
      have hsat_pivot : SatEq σ' pivot := by
        unfold SatEq
        simp only [σ', evalXor_update_mem σ b hv_pivot, b]
        cases pivot.rhs <;> cases evalXor σ (pivot.vars.erase v) <;> rfl
      refine ⟨σ', fun eq heq => ?_⟩
      by_cases hv : v ∈ eq.vars
      · have hmem : eq ∈ pivot :: rest := by
          rw [← hwith]
          simp [List.mem_filter, heq, hv]
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact hsat_pivot
        · have hadd_mem : addEq pivot eq ∈
              sys.filter (fun eq => !decide (v ∈ eq.vars)) ++ rest.map (addEq pivot) :=
            List.mem_append_right _ (List.mem_map_of_mem hrest)
          have hsat_add_σ : SatEq σ (addEq pivot eq) := hσ (addEq pivot eq) hadd_mem
          have hnot_mem : v ∉ (addEq pivot eq).vars := not_mem_addEq_vars hv_pivot hv
          have hsat_add_σ' : SatEq σ' (addEq pivot eq) := by
            unfold SatEq at hsat_add_σ ⊢
            simpa only [σ', evalXor_update_not_mem σ b hnot_mem] using hsat_add_σ
          exact satEq_of_satEq_addEq hsat_pivot hsat_add_σ'
      · have hwithout : eq ∈
            sys.filter (fun eq => !decide (v ∈ eq.vars)) ++ rest.map (addEq pivot) := by
          apply List.mem_append_left
          simp [List.mem_filter, heq, hv]
        have hsat_σ : SatEq σ eq := hσ eq hwithout
        unfold SatEq at hsat_σ ⊢
        simpa only [σ', evalXor_update_not_mem σ b hv] using hsat_σ
  · -- Soundness: any satisfying assignment of `sys` also satisfies `gaussElimVar v sys`.
    rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    unfold gaussElimVar
    dsimp only
    generalize hwith : sys.filter (fun eq => decide (v ∈ eq.vars)) = withV
    cases withV with
    | nil =>
      intro eq heq
      simp only [List.mem_filter] at heq
      exact hσ eq heq.1
    | cons pivot rest =>
      intro eq heq
      rw [List.mem_append] at heq
      rcases heq with heq | heq
      · simp only [List.mem_filter] at heq
        exact hσ eq heq.1
      · rw [List.mem_map] at heq
        rcases heq with ⟨e, he, rfl⟩
        have hpivot : pivot ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
          rw [hwith]
          exact List.mem_cons_self
        have he' : e ∈ sys.filter (fun eq => decide (v ∈ eq.vars)) := by
          rw [hwith]
          exact List.mem_cons_of_mem pivot he
        simp only [List.mem_filter] at hpivot he'
        exact satEq_addEq (hσ pivot hpivot.1) (hσ e he'.1)

/-! ## Iterated Gaussian Elimination Along a Variable Sequence -/

/-- Iteratively eliminate a list of variables `vs` from a `GF(2)`-linear system via pivot
Gaussian elimination. -/
def gaussElimList {n : ℕ} (vs : List (Fin n)) (sys : LinSys n) : LinSys n :=
  vs.foldl (fun s v => gaussElimVar v s) sys

/-- Iterated Gaussian elimination along any variable order never increases the number of
equations. -/
theorem gaussElimList_length_le {n : ℕ} (vs : List (Fin n)) (sys : LinSys n) :
    (gaussElimList vs sys).length ≤ sys.length := by
  induction vs generalizing sys with
  | nil => exact Nat.le_refl _
  | cons v vs ih =>
    simp only [gaussElimList, List.foldl_cons]
    exact (ih (gaussElimVar v sys)).trans (gaussElimVar_length_le v sys)

/-- Iterated Gaussian elimination along any variable order preserves exact satisfiability. -/
theorem gaussElimList_equisatisfiable {n : ℕ} (vs : List (Fin n)) (sys : LinSys n) :
    Satisfiable (gaussElimList vs sys) ↔ Satisfiable sys := by
  induction vs generalizing sys with
  | nil => rfl
  | cons v vs ih =>
    simp only [gaussElimList, List.foldl_cons]
    exact (ih (gaussElimVar v sys)).trans (gaussElimVar_equisatisfiable v sys)

end Mathmatica.XORSATBasis
