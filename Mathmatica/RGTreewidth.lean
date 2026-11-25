/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.TwoSATPoly
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Option

/-!
# Bounded Elimination Width and Polynomial State Space for Real-Space RG

This module generalizes the 2-SAT polynomial closure of `Mathmatica.TwoSATPoly` to arbitrary
`k`-SAT formulas equipped with a variable-elimination order of bounded elimination width
(renormalizable real-space RG flow).

When a variable-elimination sequence `vs` keeps every intermediate effective formula within
clause width at most `w` (a condition closely tied to bounded treewidth / bounded elimination
width of the primal interaction graph), the entire real-space RG trajectory stays inside the
bounded-width clause space `allWClauses n w`, whose cardinality is bounded by `(2 * n + 1) ^ w`.

## Main definitions

* `IsWSAT w φ`: Every clause in the deduplicated CNF formula `φ` has width at most `w`.
* `allWClauses n w`: The finite set of all clauses of width at most `w` over `n` variables.
* `HasElimWidthBounded w vs φ`: Every intermediate effective formula along the real-space RG
  elimination sequence `vs` starting from `φ` is a `w`-SAT formula.
* `rgTrace vs φ t`: The effective CNF formula at step `t` along the RG trajectory of `vs`.

## Main results

* `card_allWClauses_le`: `(allWClauses n w).card ≤ (2 * n + 1) ^ w`.
* `rg_bounded_elimWidth_poly`: If `HasElimWidthBounded w vs φ`, then `decimateList vs φ` is
  equisatisfiable with `φ` and every step `rgTrace vs φ t` has width at most `w` and at most
  `(2 * n + 1) ^ w` clauses.
* `twoSAT_hasElimWidthBounded_two`: Every 2-SAT formula satisfies `HasElimWidthBounded 2 vs φ`
  along every elimination order `vs`, recovering `Mathmatica.TwoSATPoly` as the `w = 2` case.
-/

namespace Mathmatica.RGTreewidth

open Mathmatica.TwoSATPoly

/-! ## Bounded-Width Clause Space and Polynomial Upper Bound -/

/-- A deduplicated CNF formula is a `w`-SAT formula if every clause has cardinality at most `w`. -/
def IsWSAT {n : ℕ} (w : ℕ) (φ : FCNF n) : Prop :=
  ∀ c ∈ φ, c.card ≤ w

/-- Monotonicity of `IsWSAT` in the width bound `w`. -/
theorem IsWSAT.mono {n w₁ w₂ : ℕ} {φ : FCNF n} (h : IsWSAT w₁ φ) (hle : w₁ ≤ w₂) :
    IsWSAT w₂ φ :=
  fun c hc => (h c hc).trans hle

/-- The finite set of all clauses of width at most `w` over `n` variables. -/
def allWClauses (n w : ℕ) : Finset (FClause n) :=
  (Finset.range (w + 1)).biUnion (fun j => (Finset.univ : Finset (Lit n)).powersetCard j)

/-- Membership characterization: a clause lies in `allWClauses n w` iff its width is at most `w`. -/
theorem mem_allWClauses_iff {n w : ℕ} (c : FClause n) :
    c ∈ allWClauses n w ↔ c.card ≤ w := by
  simp only [allWClauses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro hcard
    exact ⟨c.card, by omega, rfl⟩

/-- **Theorem 1 (Polynomial State-Space Bound for Bounded-Width Clauses)**:
the number of distinct clauses of width at most `w` over `n` variables is at most
`(2 * n + 1) ^ w`. -/
theorem card_allWClauses_le (n w : ℕ) :
    (allWClauses n w).card ≤ (2 * n + 1) ^ w := by
  induction w with
  | zero =>
    have h0 : allWClauses n 0 = {∅} := by
      ext c
      simp [mem_allWClauses_iff]
    rw [h0, Finset.card_singleton, pow_zero]
  | succ w ih =>
    let step : FClause n × Option (Lit n) → FClause n := fun p =>
      match p.2 with
      | none => p.1
      | some l => insert l p.1
    let S : Finset (FClause n × Option (Lit n)) :=
      allWClauses n w ×ˢ (Finset.univ : Finset (Option (Lit n)))
    have hsub : allWClauses n (w + 1) ⊆ S.image step := by
      intro c hc
      rw [mem_allWClauses_iff] at hc
      rw [Finset.mem_image]
      by_cases hle : c.card ≤ w
      · refine ⟨(c, none), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
        exact (mem_allWClauses_iff c).mpr hle
      · have hpos : 0 < c.card := by omega
        rcases Finset.card_pos.mp hpos with ⟨l, hl⟩
        refine ⟨(c.erase l, some l), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · rw [mem_allWClauses_iff, Finset.card_erase_of_mem hl]
          omega
        · exact Finset.insert_erase hl
    calc
      (allWClauses n (w + 1)).card
          ≤ (S.image step).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
      _ = (allWClauses n w).card * (Finset.univ : Finset (Option (Lit n))).card :=
          Finset.card_product _ _
      _ = (allWClauses n w).card * (2 * n + 1) := by
          rw [Finset.card_univ, Fintype.card_option, card_lit]
      _ ≤ (2 * n + 1) ^ w * (2 * n + 1) := Nat.mul_le_mul_right _ ih
      _ = (2 * n + 1) ^ (w + 1) := by rw [pow_succ]

/-- Any `w`-SAT formula is a subset of `allWClauses n w`. -/
theorem isWSAT_subset_allWClauses {n w : ℕ} {φ : FCNF n} (hw : IsWSAT w φ) :
    φ ⊆ allWClauses n w :=
  fun c hc => (mem_allWClauses_iff c).mpr (hw c hc)

/-- Any `w`-SAT formula over `n` variables has at most `(2 * n + 1) ^ w` clauses. -/
theorem isWSAT_card_le {n w : ℕ} {φ : FCNF n} (hw : IsWSAT w φ) :
    φ.card ≤ (2 * n + 1) ^ w :=
  (Finset.card_le_card (isWSAT_subset_allWClauses hw)).trans (card_allWClauses_le n w)

/-! ## Bounded Elimination Width along Real-Space RG Trajectories -/

/-- A variable-elimination order `vs` has elimination width bounded by `w` on `φ` if every
intermediate effective formula along the real-space RG trajectory is a `w`-SAT formula. -/
def HasElimWidthBounded {n : ℕ} (w : ℕ) : List (Fin n) → FCNF n → Prop
  | [], φ => IsWSAT w φ
  | v :: vs, φ => IsWSAT w φ ∧ HasElimWidthBounded w vs (decimateVar v φ)

/-- Monotonicity of `HasElimWidthBounded` in the width bound `w`. -/
theorem HasElimWidthBounded.mono {n w₁ w₂ : ℕ} {vs : List (Fin n)} {φ : FCNF n}
    (h : HasElimWidthBounded w₁ vs φ) (hle : w₁ ≤ w₂) :
    HasElimWidthBounded w₂ vs φ := by
  induction vs generalizing φ with
  | nil => exact IsWSAT.mono h hle
  | cons v vs ih => exact ⟨IsWSAT.mono h.1 hle, ih h.2⟩

/-- The effective CNF formula at step `t` along the real-space RG trajectory induced by `vs`
starting from `φ`. For `t ≥ vs.length`, the trajectory stays at `decimateList vs φ`. -/
def rgTrace {n : ℕ} : List (Fin n) → FCNF n → ℕ → FCNF n
  | _, φ, 0 => φ
  | [], φ, _ + 1 => φ
  | v :: vs, φ, t + 1 => rgTrace vs (decimateVar v φ) t

/-- At step `0`, the RG trajectory is the initial formula `φ`. -/
@[simp]
theorem rgTrace_zero {n : ℕ} (vs : List (Fin n)) (φ : FCNF n) :
    rgTrace vs φ 0 = φ := by
  cases vs <;> rfl

/-- At step `vs.length`, the RG trajectory reaches `decimateList vs φ`. -/
theorem rgTrace_length {n : ℕ} (vs : List (Fin n)) (φ : FCNF n) :
    rgTrace vs φ vs.length = decimateList vs φ := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons, rgTrace, decimateList]
    exact ih (decimateVar v φ)

/-- For any `t ≥ vs.length`, the RG trajectory remains at `decimateList vs φ`. -/
theorem rgTrace_eq_decimateList_of_le {n : ℕ} (vs : List (Fin n)) (φ : FCNF n) {t : ℕ}
    (ht : vs.length ≤ t) :
    rgTrace vs φ t = decimateList vs φ := by
  induction vs generalizing φ t with
  | nil =>
    cases t <;> rfl
  | cons v vs ih =>
    cases t with
    | zero => simp at ht
    | succ t =>
      simp only [rgTrace, decimateList]
      exact ih (decimateVar v φ) (Nat.le_of_succ_le_succ ht)

/-- Every intermediate formula along an RG trajectory is equisatisfiable with `φ`. -/
theorem rgTrace_equisatisfiable {n : ℕ} (vs : List (Fin n)) (φ : FCNF n) (t : ℕ) :
    Satisfiable (rgTrace vs φ t) ↔ Satisfiable φ := by
  induction vs generalizing φ t with
  | nil =>
    cases t <;> rfl
  | cons v vs ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [rgTrace]
      rw [ih (decimateVar v φ) t, decimateVar_equisatisfiable v φ]

/-- Bounded elimination width guarantees that every step along `rgTrace` is a `w`-SAT formula. -/
theorem hasElimWidthBounded_isWSAT_rgTrace {n w : ℕ} {vs : List (Fin n)} {φ : FCNF n}
    (h : HasElimWidthBounded w vs φ) (t : ℕ) :
    IsWSAT w (rgTrace vs φ t) := by
  induction vs generalizing φ t with
  | nil =>
    cases t <;> exact h
  | cons v vs ih =>
    cases t with
    | zero => exact h.1
    | succ t => exact ih h.2 t

/-- **Theorem 2 (Bounded Elimination Width Implies Polynomial RG State Space)**:
if `vs` has elimination width bounded by `w` on `φ`, then the final decimated formula
`decimateList vs φ` is equisatisfiable with `φ`, and every intermediate effective formula
`rgTrace vs φ t` has clause width at most `w` and at most `(2 * n + 1) ^ w` clauses. -/
theorem rg_bounded_elimWidth_poly {n w : ℕ} {vs : List (Fin n)} {φ : FCNF n}
    (h : HasElimWidthBounded w vs φ) :
    (Satisfiable (decimateList vs φ) ↔ Satisfiable φ) ∧
    ∀ t : ℕ, IsWSAT w (rgTrace vs φ t) ∧ (rgTrace vs φ t).card ≤ (2 * n + 1) ^ w := by
  refine ⟨decimateList_equisatisfiable vs φ, fun t => ?_⟩
  have hw : IsWSAT w (rgTrace vs φ t) := hasElimWidthBounded_isWSAT_rgTrace h t
  exact ⟨hw, isWSAT_card_le hw⟩

/-- The final decimated formula of a width-`w` RG trajectory has at most `(2 * n + 1) ^ w`
clauses. -/
theorem decimateList_card_le_of_hasElimWidthBounded {n w : ℕ} {vs : List (Fin n)} {φ : FCNF n}
    (h : HasElimWidthBounded w vs φ) :
    (decimateList vs φ).card ≤ (2 * n + 1) ^ w := by
  rw [← rgTrace_length]
  exact ((rg_bounded_elimWidth_poly h).2 vs.length).2

/-! ## Specialization to 2-SAT -/

/-- `IsWSAT 2` coincides definitionally with `Is2SAT`. -/
theorem isWSAT_two_iff_is2SAT {n : ℕ} (φ : FCNF n) :
    IsWSAT 2 φ ↔ Is2SAT φ :=
  Iff.rfl

/-- Every 2-SAT formula automatically has elimination width bounded by `2` along any
variable-elimination order `vs`, embedding `Mathmatica.TwoSATPoly` as the `w = 2` special case. -/
theorem twoSAT_hasElimWidthBounded_two {n : ℕ} (vs : List (Fin n)) {φ : FCNF n}
    (h2 : Is2SAT φ) :
    HasElimWidthBounded 2 vs φ := by
  induction vs generalizing φ with
  | nil => exact h2
  | cons v vs ih => exact ⟨h2, ih (decimateVar_is2SAT v h2)⟩

/-- Every step along any 2-SAT real-space RG trajectory has at most `(2 * n + 1) ^ 2` clauses. -/
theorem twoSAT_rgTrace_card_le {n : ℕ} (vs : List (Fin n)) {φ : FCNF n} (h2 : Is2SAT φ) (t : ℕ) :
    (rgTrace vs φ t).card ≤ (2 * n + 1) ^ 2 :=
  ((rg_bounded_elimWidth_poly (twoSAT_hasElimWidthBounded_two vs h2)).2 t).2

end Mathmatica.RGTreewidth
