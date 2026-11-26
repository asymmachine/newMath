/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Find

/-!
# Exact Black Pebbling Space on the Pyramid Graph (Cook 1974)

This module formalizes the black pebbling game (with leaf placement, internal placement,
left/right sliding moves, pebble removal for recomputation, and idle steps) on the height-`h`
pyramid DAG `Π_h` (which has `N = (h + 1)(h + 2) / 2` vertices), and proves Cook's exact space
bound `S(Π_h) = h + 1` for all `h : ℕ` (Cook 1974).

## Proof Architecture

* **Lower bound (non-inductive sibling-ray blocking argument)**: Define a root-to-leaf path
  `γ : PyrPath h` and say a configuration `C` is *blocking* (`IsBlocking C`) if every path hits
  `C`. Any valid pebbling starts non-blocking (`∅`) and ends blocking (`apex h ∈ C`), so there
  exists a first transition `C₁ → C₂` from non-blocking to blocking. Choosing a pebble-free path
  `γ` in `C₁`, the transition must place a leaf pebble at the bottom of `γ` (`C₂ = insert v C₁`),
  because every internal placement or slide on `γ` requires both children in `C₁`, one of which
  lies on `γ`. For each row `r < h`, branching off `γ` into the sibling not taken by `γ` and
  continuing straight down (constant column for a left sibling, constant diagonal `row - col`
  for a right sibling) produces `h` pairwise vertex-disjoint sibling rays below their branch
  points, all disjoint from the leaf `γ.node h`. Since `C₂` blocks every ray, `C₁` already holds
  at least `h` distinct pebbles, yielding `h + 1 ≤ C₂.card ≤ P.peakSpace`.
* **Upper bound (row-by-row left-sliding)**: Place all `h + 1` leaves on row `h`, then advance
  from row `r + 1` to row `r` by sliding each pebble `(r + 1, j)` left to `(r, j)` for
  `j = 0, ..., r` and removing `(r + 1, r + 1)`. Every configuration has at most `h + 1` pebbles,
  the final configuration is `{apex h}`, and no vertex is ever recomputed.

## Epistemic Discipline (Four-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file — including the non-inductive
  Cook lower bound `h + 1 ≤ P.peakSpace`, the constructive row-by-row left-sliding upper bound
  `∃ P, P.peakSpace ≤ h + 1`, and the exact space formula `minPyrPebbleSpace h = h + 1`
  (corresponding to RG space exponent `d_s = 1/2` in `N = (h + 1)(h + 2) / 2`) — are formally
  verified in Lean 4 with zero `sorry`s and no extra axioms.
* **Model-Restricted**: The lower and upper bounds apply strictly to the black pebbling game on
  the pyramid DAG (`PyrStep` / `ValidPyrPebbling`). Under the sliding rules (`slideLeft` /
  `slideRight`), the pyramid is pebbled in optimal space `S = h + 1` with **zero recomputation
  and linear time** `O(N)`. Consequently, this module does **not** claim that the pyramid itself
  exhibits a recomputation time-space tradeoff.
* **Conditional**: Obtaining super-linear recomputation time-space tradeoffs requires either
  disallowing sliding moves (where `h + 1` pebbles force super-linear time, or `h + 2` pebbles
  recover linear time) or using higher-connectivity DAG families (such as Paul-Tarjan-Celoni or
  Lengauer-Tarjan superconcentrator graphs); transferring pebbling bounds to RAM or Turing
  machines requires obliviousness or white-box straight-line execution assumptions.
* **Conjectural**: General algorithm time-space lower bounds, circuit or Turing-machine
  separations, and `P ≠ NP` are **NOT** claimed or implied by this module.

## Main definitions

* `PyrNode`, `apex`, `isLeaf`, `leftChild`, `rightChild`: Height-`h` pyramid DAG `Π_h`.
* `PyrConfig`, `PyrStep`, `ValidPyrPebbling`, `ValidPyrPebbling.peakSpace`: Black pebbling game
  with sliding, removal, and idle moves.
* `PyrPath`, `PyrPath.node`, `IsBlocking`, `siblingPath`: Root-to-leaf paths, blocking
  configurations, and pairwise disjoint sibling rays.
* `minPyrPebbleSpace`: Minimum achievable peak pebble count on `Π_h`.

## Main results

* `step_to_blocking_eq_insert_leaf`: Any transition from a configuration avoiding a path `γ` to
  a blocking configuration must be a `placeLeaf` at the leaf of `γ`.
* `pyramid_pebbling_lower_bound`: For every `P : ValidPyrPebbling h`, `h + 1 ≤ P.peakSpace`.
* `exists_clean_pyr_pebbling`, `pyramid_pebbling_upper_bound`: Constructive row-by-row
  left-sliding pebbling of `Π_h` with peak space `≤ h + 1` and final configuration `{apex h}`.
* `pyramid_min_pebbleSpace_eq`, `minPyrPebbleSpace_eq`, `minPyrPebbleSpace_succ`: Exact space
  characterization `minPyrPebbleSpace h = h + 1`.
-/

namespace Mathmatica.PyramidPebbling

/-! ### Pyramid Graph and Black Pebbling Transition Rules -/

/-- Vertices of the height-`h` pyramid DAG `Π_h`, indexed by `(row, col)` with
`0 ≤ col ≤ row ≤ h`. Row `0` contains only the apex `(0, 0)`, and row `h` contains the `h + 1`
input leaves `(h, 0), ..., (h, h)`. -/
@[ext]
structure PyrNode (h : ℕ) where
  row : ℕ
  col : ℕ
  col_le_row : col ≤ row
  row_le_h : row ≤ h
  deriving DecidableEq

/-- The unique apex (sink) `(0, 0)` of the height-`h` pyramid. -/
def apex (h : ℕ) : PyrNode h := ⟨0, 0, le_rfl, Nat.zero_le h⟩

/-- Predicate identifying input leaves (vertices on the bottom row `h`). -/
def isLeaf {h : ℕ} (v : PyrNode h) : Prop := v.row = h

/-- Left child `(row + 1, col)` of an internal pyramid vertex `v`. -/
def leftChild {h : ℕ} (v : PyrNode h) (hv : v.row < h) : PyrNode h :=
  ⟨v.row + 1, v.col, Nat.le_succ_of_le v.col_le_row, hv⟩

/-- Right child `(row + 1, col + 1)` of an internal pyramid vertex `v`. -/
def rightChild {h : ℕ} (v : PyrNode h) (hv : v.row < h) : PyrNode h :=
  ⟨v.row + 1, v.col + 1, Nat.succ_le_succ v.col_le_row, hv⟩

/-- A pebble configuration on the height-`h` pyramid is a finite set of pebbled vertices. -/
abbrev PyrConfig (h : ℕ) := Finset (PyrNode h)

/-- Single-step transitions of the black pebbling game on `Π_h` (with sliding, removal,
and idle moves). -/
inductive PyrStep {h : ℕ} : PyrConfig h → PyrConfig h → Prop where
  | placeLeaf (C : PyrConfig h) (v : PyrNode h) (hv : isLeaf v) :
      PyrStep C (insert v C)
  | placeInternal (C : PyrConfig h) (v : PyrNode h) (hv : v.row < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PyrStep C (insert v C)
  | slideLeft (C : PyrConfig h) (v : PyrNode h) (hv : v.row < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PyrStep C (insert v (C.erase (leftChild v hv)))
  | slideRight (C : PyrConfig h) (v : PyrNode h) (hv : v.row < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PyrStep C (insert v (C.erase (rightChild v hv)))
  | remove (C : PyrConfig h) (v : PyrNode h) :
      PyrStep C (C.erase v)
  | idle (C : PyrConfig h) :
      PyrStep C C

/-- A valid black pebbling strategy on `Π_h` starts empty, takes valid `PyrStep`s, and places
a pebble on `apex h` at the final step. -/
structure ValidPyrPebbling (h : ℕ) where
  steps : ℕ
  trace : Fin (steps + 1) → PyrConfig h
  init_empty : trace 0 = ∅
  valid_step : ∀ i : Fin steps,
    PyrStep (trace ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (trace ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
  reaches_apex : apex h ∈ trace ⟨steps, Nat.lt_succ_self steps⟩

/-- Peak pebble space used by a valid pyramid pebbling strategy `P`. -/
def ValidPyrPebbling.peakSpace {h : ℕ} (P : ValidPyrPebbling h) : ℕ :=
  Finset.univ.sup fun t : Fin (P.steps + 1) => (P.trace t).card

lemma card_le_peakSpace {h : ℕ} (P : ValidPyrPebbling h) (t : Fin (P.steps + 1)) :
    (P.trace t).card ≤ P.peakSpace :=
  Finset.le_sup (f := fun t => (P.trace t).card) (Finset.mem_univ t)

lemma peakSpace_le_iff {h : ℕ} (P : ValidPyrPebbling h) (k : ℕ) :
    P.peakSpace ≤ k ↔ ∀ t : Fin (P.steps + 1), (P.trace t).card ≤ k := by
  simp [ValidPyrPebbling.peakSpace]

/-! ### Root-to-Leaf Paths and Blocking Configurations -/

/-- A root-to-leaf path in `Π_h`, starting at `(0, 0)` and stepping at each row either left
(keeping `col`) or right (incrementing `col` by 1). -/
structure PyrPath (h : ℕ) where
  col : Fin (h + 1) → ℕ
  col_zero : col 0 = 0
  step : ∀ r : Fin h,
    col ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ = col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ ∨
    col ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ = col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ + 1

lemma PyrPath.col_le {h : ℕ} (γ : PyrPath h) (r : Fin (h + 1)) : γ.col r ≤ r.val := by
  rcases r with ⟨r, hr⟩
  induction r with
  | zero =>
    change γ.col 0 ≤ 0
    rw [γ.col_zero]
  | succ k ih =>
    have hk : k < h := Nat.lt_of_succ_lt_succ hr
    have hprev := ih (Nat.lt_succ_of_lt hk)
    dsimp only at hprev ⊢
    rcases γ.step ⟨k, hk⟩ with hL | hR
    · dsimp only at hL; omega
    · dsimp only at hR; omega

lemma PyrPath.col_mono {h : ℕ} (γ : PyrPath h) {a b : Fin (h + 1)} (hab : a.val ≤ b.val) :
    γ.col a ≤ γ.col b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  dsimp only at hab
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.le_zero.mp hab
    subst ha0
    exact le_rfl
  | succ k ih =>
    by_cases hEq : a = k + 1
    · subst hEq; exact le_rfl
    · have hak : a ≤ k := by omega
      have hk : k < h := Nat.lt_of_succ_lt_succ hb
      have hprev := ih (Nat.lt_succ_of_lt hk) hak
      rcases γ.step ⟨k, hk⟩ with hL | hR
      · dsimp only at hL; omega
      · dsimp only at hR; omega

lemma PyrPath.diag_mono {h : ℕ} (γ : PyrPath h) {a b : Fin (h + 1)} (hab : a.val ≤ b.val) :
    a.val - γ.col a ≤ b.val - γ.col b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  dsimp only at hab ⊢
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.le_zero.mp hab
    subst ha0
    exact le_rfl
  | succ k ih =>
    by_cases hEq : a = k + 1
    · subst hEq; exact le_rfl
    · have hak : a ≤ k := by omega
      have hk : k < h := Nat.lt_of_succ_lt_succ hb
      have hprev := ih (Nat.lt_succ_of_lt hk) hak
      have hck := γ.col_le ⟨k, Nat.lt_succ_of_lt hk⟩
      dsimp only at hck
      rcases γ.step ⟨k, hk⟩ with hL | hR
      · dsimp only at hL; omega
      · dsimp only at hR; omega

/-- The vertex of `Π_h` visited by path `γ` at row `r`. -/
def PyrPath.node {h : ℕ} (γ : PyrPath h) (r : Fin (h + 1)) : PyrNode h :=
  ⟨r.val, γ.col r, γ.col_le r, Nat.le_of_lt_succ r.isLt⟩

lemma PyrPath.node_zero {h : ℕ} (γ : PyrPath h) :
    γ.node ⟨0, Nat.zero_lt_succ h⟩ = apex h := by
  ext
  · rfl
  · exact γ.col_zero

lemma PyrPath.node_succ {h : ℕ} (γ : PyrPath h) (r : Fin h) :
    γ.node ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
      leftChild (γ.node ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) r.isLt ∨
    γ.node ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
      rightChild (γ.node ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩) r.isLt := by
  rcases γ.step r with hL | hR
  · left
    ext
    · rfl
    · exact hL
  · right
    ext
    · rfl
    · exact hR

/-- A configuration `C` is *blocking* if every root-to-leaf path contains at least one
pebbled vertex in `C`. -/
def IsBlocking {h : ℕ} (C : PyrConfig h) : Prop :=
  ∀ γ : PyrPath h, ∃ r : Fin (h + 1), γ.node r ∈ C

/-- The leftmost spine path `(0, 0), (1, 0), ..., (h, 0)`. -/
def leftSpinePath (h : ℕ) : PyrPath h where
  col := fun _ => 0
  col_zero := rfl
  step := fun _ => Or.inl rfl

lemma not_isBlocking_empty (h : ℕ) : ¬ IsBlocking (∅ : PyrConfig h) := by
  intro hblk
  rcases hblk (leftSpinePath h) with ⟨r, hr⟩
  exact Finset.notMem_empty _ hr

lemma isBlocking_of_apex_mem {h : ℕ} {C : PyrConfig h} (hA : apex h ∈ C) : IsBlocking C := by
  intro γ
  refine ⟨⟨0, Nat.zero_lt_succ h⟩, ?_⟩
  rw [γ.node_zero]
  exact hA

/-- **Key Transition Lemma**: If a single step `PyrStep C₁ C₂` turns a configuration `C₁` that
completely avoids a path `γ` into a blocking configuration `C₂`, then the step must be a
`placeLeaf` at the leaf vertex `γ.node ⟨h, _⟩`. -/
lemma step_to_blocking_eq_insert_leaf {h : ℕ} {C₁ C₂ : PyrConfig h}
    (hstep : PyrStep C₁ C₂) (γ : PyrPath h)
    (hfree : ∀ r : Fin (h + 1), γ.node r ∉ C₁)
    (hblk : IsBlocking C₂) :
    C₂ = insert (γ.node ⟨h, Nat.lt_succ_self h⟩) C₁ := by
  rcases hblk γ with ⟨r, hr⟩
  cases hstep with
  | placeLeaf v hv =>
    rcases Finset.mem_insert.mp hr with hEq | hC₁
    · subst hEq
      have hrEq : r = ⟨h, Nat.lt_succ_self h⟩ := Fin.ext hv
      subst hrEq
      rfl
    · exact absurd hC₁ (hfree r)
  | placeInternal v hv hL hR =>
    rcases Finset.mem_insert.mp hr with hEq | hC₁
    · subst hEq
      rcases γ.node_succ ⟨r.val, hv⟩ with hS | hS
      · exact absurd (hS ▸ hL) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
      · exact absurd (hS ▸ hR) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
    · exact absurd hC₁ (hfree r)
  | slideLeft v hv hL hR =>
    rcases Finset.mem_insert.mp hr with hEq | hC₁
    · subst hEq
      rcases γ.node_succ ⟨r.val, hv⟩ with hS | hS
      · exact absurd (hS ▸ hL) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
      · exact absurd (hS ▸ hR) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
    · exact absurd (Finset.mem_of_mem_erase hC₁) (hfree r)
  | slideRight v hv hL hR =>
    rcases Finset.mem_insert.mp hr with hEq | hC₁
    · subst hEq
      rcases γ.node_succ ⟨r.val, hv⟩ with hS | hS
      · exact absurd (hS ▸ hL) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
      · exact absurd (hS ▸ hR) (hfree ⟨r.val + 1, Nat.succ_lt_succ hv⟩)
    · exact absurd (Finset.mem_of_mem_erase hC₁) (hfree r)
  | remove _ =>
    exact absurd (Finset.mem_of_mem_erase hr) (hfree r)
  | idle =>
    exact absurd hr (hfree r)

/-! ### Pairwise Disjoint Sibling Rays and Cook's Lower Bound -/

/-- For a path `γ` and row `r < h`, the sibling ray `siblingPath γ r` follows `γ` through
row `r`, branches into the sibling not taken by `γ` at row `r + 1`, and then continues straight
down (constant column if branching left, constant diagonal `row - col` if branching right). -/
def siblingPath {h : ℕ} (γ : PyrPath h) (r : Fin h) : PyrPath h where
  col := fun k =>
    if k.val ≤ r.val then γ.col k
    else if γ.col ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
        γ.col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ then
      γ.col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ + (k.val - r.val)
    else
      γ.col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩
  col_zero := by
    have h0 : (0 : ℕ) ≤ r.val := Nat.zero_le _
    simp [h0, γ.col_zero]
  step := fun j => by
    by_cases h1 : j.val + 1 ≤ r.val
    · have h0 : j.val ≤ r.val := by omega
      simp only [h1, h0, ↓reduceIte]
      exact γ.step j
    · by_cases h0 : j.val ≤ r.val
      · have hEq : j.val = r.val := by omega
        have hfin : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (h + 1)) =
            ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ := Fin.ext hEq
        simp only [h1, h0, ↓reduceIte, hfin]
        split_ifs
        · right; omega
        · left; rfl
      · simp only [h1, h0, ↓reduceIte]
        split_ifs
        · right; omega
        · left; rfl

lemma siblingPath_node_of_le {h : ℕ} (γ : PyrPath h) (r : Fin h)
    {k : Fin (h + 1)} (hk : k.val ≤ r.val) :
    (siblingPath γ r).node k = γ.node k := by
  ext
  · rfl
  · simp [PyrPath.node, siblingPath, hk]

lemma siblingPath_ne_leaf {h : ℕ} (γ : PyrPath h) (r : Fin h)
    {k : Fin (h + 1)} (hk : r.val < k.val) :
    (siblingPath γ r).node k ≠ γ.node ⟨h, Nat.lt_succ_self h⟩ := by
  intro hEq
  have hrow : k.val = h := congrArg PyrNode.row hEq
  have hcol : (siblingPath γ r).col k = γ.col ⟨h, Nat.lt_succ_self h⟩ :=
    congrArg PyrNode.col hEq
  have hnotle : ¬ k.val ≤ r.val := by omega
  simp only [siblingPath, hnotle, ↓reduceIte] at hcol
  have hr1 : r.val + 1 ≤ h := r.isLt
  have hcr := γ.col_le ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩
  dsimp only at hcr
  split_ifs at hcol with hstep
  · have hdiag := γ.diag_mono (a := ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
      (b := ⟨h, Nat.lt_succ_self h⟩) hr1
    dsimp only at hdiag
    omega
  · have hstepR : γ.col ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
        γ.col ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ + 1 := by
      rcases γ.step r with hL | hR
      · exact absurd hL hstep
      · exact hR
    have hmono := γ.col_mono (a := ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
      (b := ⟨h, Nat.lt_succ_self h⟩) hr1
    omega

lemma siblingPath_disjoint_of_lt {h : ℕ} (γ : PyrPath h) {r₁ r₂ : Fin h}
    (hr : r₁.val < r₂.val) {k₁ k₂ : Fin (h + 1)}
    (hk₁ : r₁.val < k₁.val) (hk₂ : r₂.val < k₂.val) :
    (siblingPath γ r₁).node k₁ ≠ (siblingPath γ r₂).node k₂ := by
  intro hEq
  have hrow : k₁.val = k₂.val := congrArg PyrNode.row hEq
  have hcol : (siblingPath γ r₁).col k₁ = (siblingPath γ r₂).col k₂ :=
    congrArg PyrNode.col hEq
  have hn1 : ¬ k₁.val ≤ r₁.val := by omega
  have hn2 : ¬ k₂.val ≤ r₂.val := by omega
  simp only [siblingPath, hn1, hn2, ↓reduceIte] at hcol
  have hr12 : r₁.val + 1 ≤ r₂.val := hr
  have hrle : r₁.val ≤ r₂.val := Nat.le_of_lt hr
  have hcr1 := γ.col_le ⟨r₁.val, Nat.lt_succ_of_lt r₁.isLt⟩
  have hcr2 := γ.col_le ⟨r₂.val, Nat.lt_succ_of_lt r₂.isLt⟩
  dsimp only at hcr1 hcr2
  split_ifs at hcol with hs1 hs2 hs2
  · -- Both r₁ and r₂ branch right (γ stepped left at r₁)
    have hdiag := γ.diag_mono (a := ⟨r₁.val + 1, Nat.succ_lt_succ r₁.isLt⟩)
      (b := ⟨r₂.val, Nat.lt_succ_of_lt r₂.isLt⟩) hr12
    dsimp only at hdiag
    omega
  · -- r₁ branches right, r₂ branches left
    have hdiag := γ.diag_mono (a := ⟨r₁.val, Nat.lt_succ_of_lt r₁.isLt⟩)
      (b := ⟨r₂.val, Nat.lt_succ_of_lt r₂.isLt⟩) hrle
    dsimp only at hdiag
    omega
  · -- r₁ branches left, r₂ branches right
    have hmono := γ.col_mono (a := ⟨r₁.val, Nat.lt_succ_of_lt r₁.isLt⟩)
      (b := ⟨r₂.val, Nat.lt_succ_of_lt r₂.isLt⟩) hrle
    omega
  · -- Both r₁ and r₂ branch left (γ stepped right at r₁)
    have hstepR : γ.col ⟨r₁.val + 1, Nat.succ_lt_succ r₁.isLt⟩ =
        γ.col ⟨r₁.val, Nat.lt_succ_of_lt r₁.isLt⟩ + 1 := by
      rcases γ.step r₁ with hL | hR
      · exact absurd hL hs1
      · exact hR
    have hmono := γ.col_mono (a := ⟨r₁.val + 1, Nat.succ_lt_succ r₁.isLt⟩)
      (b := ⟨r₂.val, Nat.lt_succ_of_lt r₂.isLt⟩) hr12
    omega

private lemma exists_transition {P : ℕ → Prop} {n : ℕ} (h0 : ¬ P 0) (hn : P n) :
    ∃ t < n, ¬ P t ∧ P (t + 1) := by
  induction n with
  | zero => exact absurd hn h0
  | succ k ih =>
    by_cases hk : P k
    · rcases ih hk with ⟨t, ht, hnt, hpt⟩
      exact ⟨t, Nat.lt_succ_of_lt ht, hnt, hpt⟩
    · exact ⟨k, Nat.lt_succ_self k, hk, hn⟩

/-- **Cook's Lower Bound (1974)**: Every valid black pebbling strategy on the height-`h` pyramid
`Π_h` uses at least `h + 1` pebbles at some time step. -/
theorem pyramid_pebbling_lower_bound (h : ℕ) (P : ValidPyrPebbling h) :
    h + 1 ≤ P.peakSpace := by
  classical
  have h0 : ¬ IsBlocking (P.trace ⟨0, Nat.zero_lt_succ P.steps⟩) := by
    have hinit : P.trace ⟨0, Nat.zero_lt_succ P.steps⟩ = ∅ := P.init_empty
    rw [hinit]
    exact not_isBlocking_empty h
  have hn : IsBlocking (P.trace ⟨P.steps, Nat.lt_succ_self P.steps⟩) :=
    isBlocking_of_apex_mem P.reaches_apex
  let Q : ℕ → Prop := fun t =>
    ∃ ht : t ≤ P.steps, IsBlocking (P.trace ⟨t, Nat.lt_succ_of_le ht⟩)
  have hQ0 : ¬ Q 0 := by
    rintro ⟨_, hblk⟩
    exact h0 hblk
  have hQn : Q P.steps := ⟨le_rfl, hn⟩
  rcases exists_transition hQ0 hQn with ⟨t, ht, hnt, hpt⟩
  rcases hpt with ⟨_, hblk2⟩
  have hnotblk1 : ¬ IsBlocking (P.trace ⟨t, Nat.lt_succ_of_lt ht⟩) := by
    intro hblk1
    exact hnt ⟨Nat.le_of_lt ht, hblk1⟩
  set C₁ := P.trace ⟨t, Nat.lt_succ_of_lt ht⟩
  set C₂ := P.trace ⟨t + 1, Nat.succ_lt_succ ht⟩
  have hstep : PyrStep C₁ C₂ := P.valid_step ⟨t, ht⟩
  simp only [IsBlocking, not_forall, not_exists] at hnotblk1
  rcases hnotblk1 with ⟨γ, hfree⟩
  have hC₂ : C₂ = insert (γ.node ⟨h, Nat.lt_succ_self h⟩) C₁ :=
    step_to_blocking_eq_insert_leaf hstep γ hfree hblk2
  have hray : ∀ r : Fin h,
      ∃ k : Fin (h + 1), r.val < k.val ∧ (siblingPath γ r).node k ∈ C₁ := by
    intro r
    rcases hblk2 (siblingPath γ r) with ⟨k, hk⟩
    have hne_leaf : r.val < k.val := by
      by_contra hle
      have hkr : k.val ≤ r.val := Nat.le_of_not_lt hle
      rw [siblingPath_node_of_le γ r hkr, hC₂] at hk
      rcases Finset.mem_insert.mp hk with hEq | hmem
      · have hrow : k.val = h := congrArg PyrNode.row hEq
        omega
      · exact hfree k hmem
    have hmemC₁ : (siblingPath γ r).node k ∈ C₁ := by
      rw [hC₂] at hk
      rcases Finset.mem_insert.mp hk with hEq | hmem
      · exact absurd hEq (siblingPath_ne_leaf γ r hne_leaf)
      · exact hmem
    exact ⟨k, hne_leaf, hmemC₁⟩
  choose rayIdx hray_gt hray_mem using hray
  let pebbleOfRay : Fin h → PyrNode h := fun r => (siblingPath γ r).node (rayIdx r)
  have hinj : Function.Injective pebbleOfRay := by
    intro r₁ r₂ hEq
    by_contra hne
    have hvalne : r₁.val ≠ r₂.val := fun hv => hne (Fin.ext hv)
    rcases Nat.lt_or_gt_of_ne hvalne with hlt | hgt
    · exact siblingPath_disjoint_of_lt γ hlt (hray_gt r₁) (hray_gt r₂) hEq
    · exact siblingPath_disjoint_of_lt γ hgt (hray_gt r₂) (hray_gt r₁) hEq.symm
  have hsub : (Finset.univ : Finset (Fin h)).image pebbleOfRay ⊆ C₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩
    exact hray_mem r
  have hcard1 : h ≤ C₁.card := by
    have hcard_img : ((Finset.univ : Finset (Fin h)).image pebbleOfRay).card = h := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    exact le_trans (le_of_eq hcard_img.symm) (Finset.card_le_card hsub)
  have hcard2 : h + 1 ≤ C₂.card := by
    rw [hC₂, Finset.card_insert_of_notMem (hfree ⟨h, Nat.lt_succ_self h⟩)]
    omega
  exact hcard2.trans (card_le_peakSpace P ⟨t + 1, Nat.succ_lt_succ ht⟩)

/-! ### Constructive Row-by-Row Left-Sliding Upper Bound -/

/-- A bounded-space pebbling segment transitioning from `C_start` to `C_end` while maintaining
at most `B` pebbles at every step. -/
private structure PyrSegment (h B : ℕ) (C_start C_end : PyrConfig h) where
  steps : ℕ
  trace : Fin (steps + 1) → PyrConfig h
  init_eq : trace 0 = C_start
  final_eq : trace ⟨steps, Nat.lt_succ_self steps⟩ = C_end
  valid_step : ∀ i : Fin steps,
    PyrStep (trace ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (trace ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
  card_le : ∀ t : Fin (steps + 1), (trace t).card ≤ B

private def PyrSegment.refl {h B : ℕ} (C : PyrConfig h) (hC : C.card ≤ B) :
    PyrSegment h B C C where
  steps := 0
  trace := fun _ => C
  init_eq := rfl
  final_eq := rfl
  valid_step := fun i => Fin.elim0 i
  card_le := fun _ => hC

private def PyrSegment.single {h B : ℕ} {C₁ C₂ : PyrConfig h}
    (hstep : PyrStep C₁ C₂) (h1 : C₁.card ≤ B) (h2 : C₂.card ≤ B) :
    PyrSegment h B C₁ C₂ where
  steps := 1
  trace := fun t => if t.val = 0 then C₁ else C₂
  init_eq := rfl
  final_eq := rfl
  valid_step := fun i => by
    have hi : i.val = 0 := by omega
    simpa [hi] using hstep
  card_le := fun t => by
    by_cases ht : t.val = 0
    · simpa [ht] using h1
    · simpa [ht] using h2

private def PyrSegment.trans {h B : ℕ} {C₁ C₂ C₃ : PyrConfig h}
    (S₁ : PyrSegment h B C₁ C₂) (S₂ : PyrSegment h B C₂ C₃) :
    PyrSegment h B C₁ C₃ where
  steps := S₁.steps + S₂.steps
  trace := fun t =>
    if ht : t.val ≤ S₁.steps then
      S₁.trace ⟨t.val, Nat.lt_succ_of_le ht⟩
    else
      S₂.trace ⟨t.val - S₁.steps, by omega⟩
  init_eq := by
    simp [Nat.zero_le, S₁.init_eq]
  final_eq := by
    by_cases h2 : S₂.steps = 0
    · have hle : S₁.steps + S₂.steps ≤ S₁.steps := by omega
      simp only [hle, ↓reduceDIte]
      have hfin : (⟨S₁.steps + S₂.steps, Nat.lt_succ_of_le hle⟩ : Fin (S₁.steps + 1)) =
          ⟨S₁.steps, Nat.lt_succ_self S₁.steps⟩ := Fin.ext (by dsimp only; omega)
      rw [hfin, S₁.final_eq]
      have h0 : (0 : Fin (S₂.steps + 1)) =
          ⟨S₂.steps, Nat.lt_succ_self S₂.steps⟩ := Fin.ext (by change 0 = S₂.steps; omega)
      exact S₂.init_eq.symm.trans ((congrArg S₂.trace h0).trans S₂.final_eq)
    · have hnle : ¬ S₁.steps + S₂.steps ≤ S₁.steps := by omega
      simp only [hnle, ↓reduceDIte]
      have hfin : (⟨S₁.steps + S₂.steps - S₁.steps, by omega⟩ : Fin (S₂.steps + 1)) =
          ⟨S₂.steps, Nat.lt_succ_self S₂.steps⟩ := Fin.ext (by dsimp only; omega)
      rw [hfin, S₂.final_eq]
  valid_step := fun i => by
    by_cases h1 : i.val + 1 ≤ S₁.steps
    · have h0 : i.val ≤ S₁.steps := by omega
      simp only [h1, h0, ↓reduceDIte]
      exact S₁.valid_step ⟨i.val, by omega⟩
    · by_cases h0 : i.val ≤ S₁.steps
      · have hEq : i.val = S₁.steps := by omega
        simp only [h1, h0, ↓reduceDIte]
        have hfin1 : (⟨i.val, Nat.lt_succ_of_le h0⟩ : Fin (S₁.steps + 1)) =
            ⟨S₁.steps, Nat.lt_succ_self S₁.steps⟩ := Fin.ext hEq
        have hidx1 : (⟨i.val + 1 - S₁.steps, by omega⟩ : Fin (S₂.steps + 1)) =
            ⟨1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hstep0 := S₂.valid_step ⟨0, by omega⟩
        change PyrStep (S₂.trace 0) (S₂.trace ⟨1, by omega⟩) at hstep0
        rw [S₂.init_eq] at hstep0
        rw [hfin1, S₁.final_eq, hidx1]
        exact hstep0
      · simp only [h1, h0, ↓reduceDIte]
        have hj : i.val - S₁.steps < S₂.steps := by omega
        have hnext : (⟨i.val + 1 - S₁.steps, by omega⟩ : Fin (S₂.steps + 1)) =
            ⟨(i.val - S₁.steps) + 1, Nat.succ_lt_succ hj⟩ := Fin.ext (by dsimp only; omega)
        rw [hnext]
        exact S₂.valid_step ⟨i.val - S₁.steps, hj⟩
  card_le := fun t => by
    by_cases ht : t.val ≤ S₁.steps
    · simp only [ht, ↓reduceDIte]
      exact S₁.card_le _
    · simp only [ht, ↓reduceDIte]
      exact S₂.card_le _

/-- Prefix of the first `k` vertices `(r, 0), ..., (r, k - 1)` on row `r` of `Π_h`. -/
private def rowPrefix (h r : ℕ) (hr : r ≤ h) (k : ℕ) (hk : k ≤ r + 1) : PyrConfig h :=
  (Finset.univ : Finset (Fin k)).image fun j => ⟨r, j.val, by omega, hr⟩

private lemma mem_rowPrefix {h r : ℕ} {hr : r ≤ h} {k : ℕ} {hk : k ≤ r + 1} {v : PyrNode h} :
    v ∈ rowPrefix h r hr k hk ↔ v.row = r ∧ v.col < k := by
  simp only [rowPrefix, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨rfl, j.isLt⟩
  · rintro ⟨hrow, hcol⟩
    refine ⟨⟨v.col, hcol⟩, ?_⟩
    ext
    · exact hrow.symm
    · rfl

private lemma card_rowPrefix (h r : ℕ) (hr : r ≤ h) (k : ℕ) (hk : k ≤ r + 1) :
    (rowPrefix h r hr k hk).card = k := by
  rw [rowPrefix, Finset.card_image_of_injective, Finset.card_fin]
  intro a b hEq
  exact Fin.ext (congrArg PyrNode.col hEq)

private lemma rowPrefix_zero (h r : ℕ) (hr : r ≤ h) :
    rowPrefix h r hr 0 (Nat.zero_le _) = ∅ := by
  ext v
  simp [mem_rowPrefix]

private lemma rowPrefix_succ (h r : ℕ) (hr : r ≤ h) (k : ℕ) (hk : k + 1 ≤ r + 1) :
    rowPrefix h r hr (k + 1) hk =
      insert ⟨r, k, by omega, hr⟩ (rowPrefix h r hr k (by omega)) := by
  ext v
  simp only [mem_rowPrefix, Finset.mem_insert, PyrNode.ext_iff]
  constructor
  · rintro ⟨hrow, hcol⟩
    by_cases hEq : v.col = k
    · exact Or.inl ⟨hrow, hEq⟩
    · exact Or.inr ⟨hrow, by omega⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩)
    · exact ⟨hrow, by omega⟩
    · exact ⟨hrow, by omega⟩

/-- The complete row `r` of `Π_h`, consisting of all `r + 1` vertices `(r, 0), ..., (r, r)`. -/
private def fullRow (h r : ℕ) (hr : r ≤ h) : PyrConfig h :=
  rowPrefix h r hr (r + 1) le_rfl

private lemma fullRow_zero (h : ℕ) : fullRow h 0 (Nat.zero_le h) = {apex h} := by
  ext v
  simp only [fullRow, mem_rowPrefix, Finset.mem_singleton, PyrNode.ext_iff, apex]
  constructor
  · rintro ⟨hrow, hcol⟩
    exact ⟨hrow, by omega⟩
  · rintro ⟨hrow, hcol⟩
    exact ⟨hrow, by omega⟩

/-- Suffix of vertices `(r, c)` on row `r` with `j ≤ c ≤ r`. -/
private def rowSuffix (h r : ℕ) (hr : r ≤ h) (j : ℕ) (hj : j ≤ r + 1) : PyrConfig h :=
  (Finset.univ : Finset (Fin (r + 1 - j))).image fun i => ⟨r, j + i.val, by omega, hr⟩

private lemma mem_rowSuffix {h r : ℕ} {hr : r ≤ h} {j : ℕ} {hj : j ≤ r + 1} {v : PyrNode h} :
    v ∈ rowSuffix h r hr j hj ↔ v.row = r ∧ j ≤ v.col := by
  simp only [rowSuffix, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rfl, Nat.le_add_right j i.val⟩
  · rintro ⟨hrow, hcol⟩
    have hvr : v.col ≤ r := hrow ▸ v.col_le_row
    refine ⟨⟨v.col - j, by omega⟩, ?_⟩
    ext
    · exact hrow.symm
    · dsimp only; omega

private lemma card_rowSuffix (h r : ℕ) (hr : r ≤ h) (j : ℕ) (hj : j ≤ r + 1) :
    (rowSuffix h r hr j hj).card = r + 1 - j := by
  rw [rowSuffix, Finset.card_image_of_injective, Finset.card_fin]
  intro a b hEq
  have hc : j + a.val = j + b.val := congrArg PyrNode.col hEq
  exact Fin.ext (by omega)

private lemma rowSuffix_zero (h r : ℕ) (hr : r ≤ h) :
    rowSuffix h r hr 0 (Nat.zero_le _) = fullRow h r hr := by
  ext v
  simp only [mem_rowSuffix, fullRow, mem_rowPrefix]
  constructor
  · rintro ⟨hrow, _⟩
    have hvr : v.col ≤ r := hrow ▸ v.col_le_row
    exact ⟨hrow, by omega⟩
  · rintro ⟨hrow, _⟩
    exact ⟨hrow, Nat.zero_le _⟩

/-- Intermediate configuration during the row-`(r + 1)` to row-`r` left-sliding sweep:
`j` pebbles on row `r` (`0 ≤ c < j`) and `r + 2 - j` pebbles on row `r + 1` (`j ≤ c ≤ r + 1`). -/
private def midConfig (h r : ℕ) (hr : r + 1 ≤ h) (j : ℕ) (hj : j ≤ r + 1) : PyrConfig h :=
  rowPrefix h r (by omega) j hj ∪ rowSuffix h (r + 1) hr j (by omega)

private lemma card_midConfig (h r : ℕ) (hr : r + 1 ≤ h) (j : ℕ) (hj : j ≤ r + 1) :
    (midConfig h r hr j hj).card = r + 2 := by
  have hdisj : Disjoint (rowPrefix h r (by omega) j hj)
      (rowSuffix h (r + 1) hr j (by omega)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have h1 := (mem_rowPrefix.mp hv1).1
    have h2 := (mem_rowSuffix.mp hv2).1
    omega
  rw [midConfig, Finset.card_union_of_disjoint hdisj, card_rowPrefix, card_rowSuffix]
  omega

private lemma midConfig_zero (h r : ℕ) (hr : r + 1 ≤ h) :
    midConfig h r hr 0 (Nat.zero_le _) = fullRow h (r + 1) hr := by
  rw [midConfig, rowPrefix_zero, Finset.empty_union, rowSuffix_zero]

private lemma midConfig_slide_step (h r : ℕ) (hr : r + 1 ≤ h) (j : ℕ) (hj : j < r + 1) :
    PyrStep (midConfig h r hr j (by omega)) (midConfig h r hr (j + 1) (by omega)) := by
  let v : PyrNode h := ⟨r, j, by omega, by omega⟩
  have hv : v.row < h := by change r < h; omega
  have hL : leftChild v hv ∈ midConfig h r hr j (by omega) := by
    apply Finset.mem_union_right
    rw [mem_rowSuffix]
    exact ⟨rfl, le_rfl⟩
  have hR : rightChild v hv ∈ midConfig h r hr j (by omega) := by
    apply Finset.mem_union_right
    rw [mem_rowSuffix]
    exact ⟨rfl, Nat.le_succ j⟩
  have hEq : insert v ((midConfig h r hr j (by omega)).erase (leftChild v hv)) =
      midConfig h r hr (j + 1) (by omega) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase, midConfig, Finset.mem_union,
      mem_rowPrefix, mem_rowSuffix]
    constructor
    · rintro (rfl | ⟨hne, ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩⟩)
      · exact Or.inl ⟨rfl, Nat.lt_succ_self j⟩
      · exact Or.inl ⟨hrow, by omega⟩
      · right
        refine ⟨hrow, ?_⟩
        by_contra hlt
        exact hne (PyrNode.ext hrow (by change x.col = j; omega))
    · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩)
      · by_cases hEqc : x.col = j
        · exact Or.inl (PyrNode.ext hrow hEqc)
        · refine Or.inr ⟨fun hEq' => ?_, Or.inl ⟨hrow, by omega⟩⟩
          have := congrArg PyrNode.row hEq'
          change x.row = r + 1 at this
          omega
      · refine Or.inr ⟨fun hEq' => ?_, Or.inr ⟨hrow, by omega⟩⟩
        have := congrArg PyrNode.col hEq'
        change x.col = j at this
        omega
  rw [← hEq]
  exact PyrStep.slideLeft _ v hv hL hR

private lemma midConfig_remove_last (h r : ℕ) (hr : r + 1 ≤ h) :
    PyrStep (midConfig h r hr (r + 1) le_rfl) (fullRow h r (by omega)) := by
  let last : PyrNode h := ⟨r + 1, r + 1, le_rfl, hr⟩
  have hEq : (midConfig h r hr (r + 1) le_rfl).erase last = fullRow h r (by omega) := by
    ext x
    simp only [Finset.mem_erase, midConfig, Finset.mem_union, fullRow,
      mem_rowPrefix, mem_rowSuffix]
    constructor
    · rintro ⟨hne, ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩⟩
      · exact ⟨hrow, hcol⟩
      · have hxr : x.col ≤ r + 1 := hrow ▸ x.col_le_row
        exact absurd (PyrNode.ext hrow (by change x.col = r + 1; omega)) hne
    · rintro ⟨hrow, hcol⟩
      refine ⟨fun hEq' => ?_, Or.inl ⟨hrow, hcol⟩⟩
      have := congrArg PyrNode.row hEq'
      change x.row = r + 1 at this
      omega
  rw [← hEq]
  exact PyrStep.remove _ last

/-- Phase 1: Place the first `k` leaves on row `h` starting from `∅`. -/
private def placeLeavesSegment (h : ℕ) (k : ℕ) (hk : k ≤ h + 1) :
    PyrSegment h (h + 1) ∅ (rowPrefix h h le_rfl k hk) := by
  induction k with
  | zero =>
    rw [rowPrefix_zero]
    exact PyrSegment.refl ∅ (by simp)
  | succ k ih =>
    have prev := ih (by omega)
    let v : PyrNode h := ⟨h, k, by omega, le_rfl⟩
    have hstep : PyrStep (rowPrefix h h le_rfl k (by omega))
        (rowPrefix h h le_rfl (k + 1) hk) := by
      rw [rowPrefix_succ]
      exact PyrStep.placeLeaf _ v rfl
    exact prev.trans (PyrSegment.single hstep
      (by rw [card_rowPrefix]; omega)
      (by rw [card_rowPrefix]; omega))

/-- Phase 2a: Sweep `j` left-slides from row `r + 1` to row `r`. -/
private def slideSweepSegment (h r : ℕ) (hr : r + 1 ≤ h) (j : ℕ) (hj : j ≤ r + 1) :
    PyrSegment h (h + 1) (fullRow h (r + 1) hr) (midConfig h r hr j hj) := by
  induction j with
  | zero =>
    rw [midConfig_zero]
    exact PyrSegment.refl _ (by rw [fullRow, card_rowPrefix]; omega)
  | succ j ih =>
    have prev := ih (by omega)
    exact prev.trans (PyrSegment.single (midConfig_slide_step h r hr j (by omega))
      (by rw [card_midConfig]; omega)
      (by rw [card_midConfig]; omega))

/-- Phase 2: Advance a full row of pebbles from row `r + 1` up to row `r`. -/
private def advanceRowSegment (h r : ℕ) (hr : r + 1 ≤ h) :
    PyrSegment h (h + 1) (fullRow h (r + 1) hr) (fullRow h r (by omega)) :=
  (slideSweepSegment h r hr (r + 1) le_rfl).trans
    (PyrSegment.single (midConfig_remove_last h r hr)
      (by rw [card_midConfig]; omega)
      (by rw [fullRow, card_rowPrefix]; omega))

/-- Phase 3: Advance a full row of pebbles from row `r` all the way up to `{apex h}`. -/
private def climbToApexSegment (h r : ℕ) (hr : r ≤ h) :
    PyrSegment h (h + 1) (fullRow h r hr) {apex h} := by
  induction r with
  | zero =>
    rw [fullRow_zero]
    exact PyrSegment.refl {apex h} (by simp)
  | succ r ih =>
    exact (advanceRowSegment h r hr).trans (ih (by omega))

/-- **Clean Constructive Upper Bound**: For every `h : ℕ`, there exists a valid black pebbling
of `Π_h` with peak space at most `h + 1` and final configuration `{apex h}`. -/
theorem exists_clean_pyr_pebbling (h : ℕ) :
    ∃ P : ValidPyrPebbling h,
      P.peakSpace ≤ h + 1 ∧ P.trace ⟨P.steps, Nat.lt_succ_self P.steps⟩ = {apex h} := by
  let S : PyrSegment h (h + 1) ∅ {apex h} :=
    (placeLeavesSegment h (h + 1) le_rfl).trans (climbToApexSegment h h le_rfl)
  let P : ValidPyrPebbling h := {
    steps := S.steps
    trace := S.trace
    init_empty := S.init_eq
    valid_step := S.valid_step
    reaches_apex := by
      rw [S.final_eq]
      exact Finset.mem_singleton_self _
  }
  refine ⟨P, ?_, S.final_eq⟩
  rw [peakSpace_le_iff]
  exact S.card_le

/-- **Constructive Upper Bound (Row-by-Row Left-Sliding)**: For every `h : ℕ`, there exists a
valid black pebbling of the height-`h` pyramid `Π_h` using at most `h + 1` pebbles. -/
theorem pyramid_pebbling_upper_bound (h : ℕ) :
    ∃ P : ValidPyrPebbling h, P.peakSpace ≤ h + 1 :=
  let ⟨P, hP, _⟩ := exists_clean_pyr_pebbling h
  ⟨P, hP⟩

/-! ### Exact Space Characterization -/

/-- **Exact Cook (1974) Characterization**: Every valid pebbling of `Π_h` uses at least `h + 1`
pebbles, and this bound is attained with equality. -/
theorem pyramid_min_pebbleSpace_eq (h : ℕ) :
    (∀ P : ValidPyrPebbling h, h + 1 ≤ P.peakSpace) ∧
      (∃ P : ValidPyrPebbling h, P.peakSpace = h + 1) := by
  refine ⟨pyramid_pebbling_lower_bound h, ?_⟩
  rcases pyramid_pebbling_upper_bound h with ⟨P, hle⟩
  exact ⟨P, le_antisymm hle (pyramid_pebbling_lower_bound h P)⟩

/-- Minimum black pebbling space of the height-`h` pyramid `Π_h`. -/
noncomputable def minPyrPebbleSpace (h : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ s : ℕ, ∃ P : ValidPyrPebbling h, P.peakSpace ≤ s from
    ⟨h + 1, pyramid_pebbling_upper_bound h⟩)

/-- Exact closed form: `minPyrPebbleSpace h = h + 1` (corresponding to RG space exponent
`d_s = 1/2` in `N = (h + 1)(h + 2) / 2`). -/
theorem minPyrPebbleSpace_eq (h : ℕ) : minPyrPebbleSpace h = h + 1 := by
  classical
  have hle : minPyrPebbleSpace h ≤ h + 1 :=
    Nat.find_min' _ (pyramid_pebbling_upper_bound h)
  rcases Nat.find_spec (show ∃ s : ℕ, ∃ P : ValidPyrPebbling h, P.peakSpace ≤ s from
    ⟨h + 1, pyramid_pebbling_upper_bound h⟩) with ⟨P, hP⟩
  have hge : h + 1 ≤ minPyrPebbleSpace h :=
    (pyramid_pebbling_lower_bound h P).trans hP
  exact le_antisymm hle hge

/-- Exact RG recursion: increasing pyramid height by 1 adds exactly 1 pebble. -/
theorem minPyrPebbleSpace_succ (h : ℕ) :
    minPyrPebbleSpace (h + 1) = minPyrPebbleSpace h + 1 := by
  rw [minPyrPebbleSpace_eq, minPyrPebbleSpace_eq]

end Mathmatica.PyramidPebbling
