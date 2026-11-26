/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Find

/-!
# Deterministic Separator Recovery Lower Bounds and `K_{m, m}` Recomputation Tradeoffs

This module formalizes an abstract, idle-invariant separator/capacity recovery lower bound
(`recomputationLowerBound_of_separator`) and instantiates it on the complete bipartite multi-output
DAG `K_{m, m}` to prove a genuine recomputation time-space tradeoff in the black pebbling game
with sliding moves.

## Proof Architecture

1. **Part 1 (Abstract Idle-Invariant Separator Recovery Lower Bound)**:
   Given a `SeparatorSystem Q` with legal transitions `Step : Q → Q → Prop` and a potential
   `ψ : Q → ℕ` increasing by at most `1` per step (`step_inc_le_one`), define `recoverySteps`
   as the number of steps where `ψ` strictly increases. Idle transitions contribute `0`, making
   `recoverySteps` strictly invariant under idle padding.
   * On any interval `[a, b)`, `recoverySteps_ge_potential_diff` shows by induction that the number
     of recovery steps in `[a, b)` is at least `ψ(tr b) - ψ(tr a)`.
   * If a trace starts at `ψ(tr 0) = 0` and has `k ≥ 1` strictly ordered crossing steps
     `cross : Fin k → Fin T` where `ψ(tr (cross j)) ≥ m` and
     `ψ(tr (cross j + 1)) ≤ m - drop`, summing over the `k` pairwise disjoint intervals
     `[0, cross 0)` and `[cross j + 1, cross (j + 1))` yields
     `m + (k - 1) * drop ≤ recoverySteps Sys tr`. Moreover, none of the `k` crossing steps is
     itself a recovery step, yielding `m + k + (k - 1) * drop ≤ T`.

2. **Part 2 (Genuine Recomputation Time-Space Tradeoff on `MultiOutput K_{m, m}`)**:
   The bipartite DAG `K_{m, m}` has `m` inputs `Sum.inl i` and `m` outputs `Sum.inr j`, where
   pebbling any output requires all `m` inputs to be simultaneously pebbled (`placeOutput` or
   `slideOutput`).
   * **Forced recomputation at `S = m`** (`k_mm_recomputation_lower_bound`): Every output `j` has a
     first placement step `firstOutStep P j`. Since each `KmmStep` introduces at most one new
     output, these `m` steps are pairwise distinct; sorting them yields `m` crossings with
     `drop = 1`. Applying `recomputationLowerBound_of_separator` gives
     `2 * m - 1 ≤ inputPlacements P` (at least `m - 1` forced input recomputations) and
     `3 * m - 1 ≤ P.steps`.
   * **Zero-recomputation upper bounds**:
     - At `S = m + 1` (`k_mm_zero_recomp_at_m_plus_one`), `inputPlacements P = m` (zero
       recomputation) is achieved in `3 * m` steps.
     - At `S = 2 * m` (`k_mm_zero_recomp_at_two_m`), `inputPlacements P = m` and `P.steps = 2 * m`
       (zero recomputation and optimal time).

## Epistemic Discipline (Six-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file — including
  `recoverySteps_ge_potential_diff`, `recomputationLowerBound_of_separator`,
  `k_mm_recomputation_lower_bound`, `k_mm_zero_recomp_at_m_plus_one`, and
  `k_mm_zero_recomp_at_two_m` — are formally verified in Lean 4 with zero `sorry`s and no extra
  axioms.
* **Model-Restricted**: The `K_{m, m}` lower and upper bounds apply strictly to the black pebbling
  game (`KmmStep` / `ValidKmmPebbling`) with unit-capacity vertices and explicit predecessor
  requirements. They do not rule out algebraic cancellation, compression, or non-pebbling
  algorithms for specific functions computed on `K_{m, m}`.
* **Numerically Observed**: External exhaustive BFS at `m = 3, S = 3` independently found exact
  minima `Recomp = 2` (`inputPlacements = 5`, total placements `8`), matching the symbolic lower
  bound `2 * m - 1 = 5` and `3 * m - 1 = 8` proved here. No numerical data is assumed by any proof.
* **Conditional**: Transferring separator-recovery bounds to general straight-line programs, RAMs,
  or Turing machines requires white-box dataflow / obliviousness assumptions linking machine state
  to a unit-increment separator potential `ψ`.
* **Heuristic / Structural Analogy**: The potential-drop-and-recovery mechanism is structurally
  analogous to capacity-bottleneck arguments in superconcentrator pebbling and streaming
  recomputation, but no equivalence with circuit depth or general space complexity is claimed here.
* **Conjectural / Explicitly Not Claimed**: General algorithm time-space lower bounds, Turing
  machine or circuit lower bounds, and `P ≠ NP` are **NOT** claimed or implied by this module.

## Main definitions

* `SeparatorSystem`, `recoverySet`, `recoverySteps`: Abstract unit-increment separator potential
  and idle-invariant count of strict recovery steps.
* `KmmNode`, `KmmConfig`, `inputNodes`, `inputCount`, `KmmStep`, `ValidKmmPebbling`,
  `inputPlacements`: Black pebbling game (with sliding, removal, and idle moves) on `K_{m, m}`.

## Main results

* `not_mem_recoverySet_of_eq`: Idle steps never contribute to `recoverySteps`.
* `recoverySteps_ge_potential_diff`: Interval recovery lower bound `ψ(tr b) - ψ(tr a)`.
* `recomputationLowerBound_of_separator`: Abstract separator recovery and total-step lower bounds
  `m + (k - 1) * drop ≤ recoverySteps Sys tr ∧ m + k + (k - 1) * drop ≤ T`.
* `k_mm_recomputation_lower_bound`: Forced recomputation `2 * m - 1 ≤ inputPlacements P` and
  `3 * m - 1 ≤ P.steps` at space `S = m` for `1 ≤ m`.
* `k_mm_zero_recomp_at_m_plus_one`: Constructive zero-recomputation pebbling at `S = m + 1`.
* `k_mm_zero_recomp_at_two_m`: Constructive zero-recomputation, optimal-time pebbling at
  `S = 2 * m`.
-/

namespace Mathmatica.SeparatorRecomputation

/-! ### Part 1: Abstract Idle-Invariant Separator Recovery Lower Bound -/

/-- A deterministic transition system equipped with a separator/capacity potential `ψ` that
increases by at most `1` on every legal transition. -/
structure SeparatorSystem (Q : Type*) where
  /-- Legal one-step transition relation on states. -/
  Step : Q → Q → Prop
  /-- Separator potential measuring accumulated progress toward a full separator state. -/
  ψ : Q → ℕ
  /-- Every legal transition increases `ψ` by at most `1`. -/
  step_inc_le_one : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ψ q₂ ≤ ψ q₁ + 1

/-- The set of step indices `t : Fin T` along `tr` at which the separator potential `ψ` strictly
increases. -/
def recoverySet {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T => Sys.ψ (tr t.castSucc) < Sys.ψ (tr t.succ))

/-- The number of strict potential-recovery steps along a trace `tr`. -/
def recoverySteps {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : ℕ :=
  (recoverySet Sys tr).card

/-- An idle step (`tr t.succ = tr t.castSucc`) is never a recovery step. -/
theorem not_mem_recoverySet_of_eq {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) (t : Fin T) (hidle : tr t.succ = tr t.castSucc) :
    t ∉ recoverySet Sys tr := by
  simp [recoverySet, hidle]

/-- A trace consisting entirely of idle steps has zero recovery steps. -/
theorem recoverySteps_eq_zero_of_idle {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) (hidle : ∀ t : Fin T, tr t.succ = tr t.castSucc) :
    recoverySteps Sys tr = 0 := by
  unfold recoverySteps
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  exact not_mem_recoverySet_of_eq Sys tr t (hidle t) ht

/-- Step indices in the half-open interval `[a, b)` inside `Fin T`. -/
def stepInterval (T a b : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T => a ≤ t.1 ∧ t.1 < b)

private theorem stepInterval_succ {T a b : ℕ} (hab : a ≤ b) (hb : b < T) :
    stepInterval T a (b + 1) = insert ⟨b, hb⟩ (stepInterval T a b) := by
  ext t
  simp only [stepInterval, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

private theorem not_mem_stepInterval_self {T a b : ℕ} (hb : b < T) :
    (⟨b, hb⟩ : Fin T) ∉ stepInterval T a b := by
  simp [stepInterval]

/-- On any legal trace segment `[a, b)`, the number of strict potential-recovery steps is at least
the net potential gain `ψ (tr b) - ψ (tr a)`. -/
theorem recoverySteps_ge_potential_diff {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, Sys.Step (tr t.castSucc) (tr t.succ))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    Sys.ψ (tr ⟨b, Nat.lt_succ_of_le hb⟩) -
      Sys.ψ (tr ⟨a, Nat.lt_succ_of_le (hab.trans hb)⟩) ≤
      (recoverySet Sys tr ∩ stepInterval T a b).card := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hb' : a + d < T := by omega
    have ih' := ih (Nat.le_add_right a d) (Nat.le_of_lt hb')
    let t : Fin T := ⟨a + d, hb'⟩
    have hstep_t := Sys.step_inc_le_one (hstep t)
    have hcast : t.castSucc = ⟨a + d, Nat.lt_succ_of_le (Nat.le_of_lt hb')⟩ := rfl
    have hsucc : t.succ = ⟨a + (d + 1), Nat.lt_succ_of_le hb⟩ := by
      ext
      simp [t]
      omega
    rw [← hsucc]
    rw [← hcast] at ih'
    have hsub : stepInterval T a (a + d) ⊆ stepInterval T a (a + (d + 1)) := by
      intro x hx
      simp only [stepInterval, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    by_cases hinc : Sys.ψ (tr t.castSucc) < Sys.ψ (tr t.succ)
    · have ht_rec : t ∈ recoverySet Sys tr := by
        simp [recoverySet, hinc]
      have ht_not : t ∉ recoverySet Sys tr ∩ stepInterval T a (a + d) := by
        intro hmem
        exact not_mem_stepInterval_self hb' (Finset.mem_inter.mp hmem).2
      have hins :
          recoverySet Sys tr ∩ stepInterval T a (a + (d + 1)) =
            insert t (recoverySet Sys tr ∩ stepInterval T a (a + d)) := by
        have hstep_eq : stepInterval T a (a + (d + 1)) = insert t (stepInterval T a (a + d)) := by
          simpa [Nat.add_assoc, t] using stepInterval_succ (Nat.le_add_right a d) hb'
        rw [hstep_eq, Finset.inter_insert_of_mem ht_rec]
      rw [hins, Finset.card_insert_of_notMem ht_not]
      omega
    · have hcard_le :
          (recoverySet Sys tr ∩ stepInterval T a (a + d)).card ≤
            (recoverySet Sys tr ∩ stepInterval T a (a + (d + 1))).card :=
        Finset.card_le_card (Finset.inter_subset_inter_left hsub)
      omega

/-- **Abstract Separator Recovery Lower Bound**:
If a legal trace starts at `ψ (tr 0) = 0` and passes through `k ≥ 1` strictly ordered crossing
steps `cross : Fin k → Fin T` where `ψ (tr (cross j)) ≥ m` before the step and
`ψ (tr (cross j + 1)) ≤ m - drop` after the step (with `drop ≤ m`), then:
1. The trace executes at least `m + (k - 1) * drop` strict recovery steps; and
2. The trace length satisfies `m + k + (k - 1) * drop ≤ T`, because the `k` crossing steps are
   disjoint from all recovery steps. -/
theorem recomputationLowerBound_of_separator {Q : Type*} (Sys : SeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, Sys.Step (tr t.castSucc) (tr t.succ))
    {k m drop : ℕ} (hk : 1 ≤ k) (hdrop : drop ≤ m)
    (hinit : Sys.ψ (tr 0) = 0)
    (cross : Fin k → Fin T) (hmono : StrictMono cross)
    (hfull : ∀ j : Fin k, m ≤ Sys.ψ (tr (cross j).castSucc))
    (hdrop_after : ∀ j : Fin k, Sys.ψ (tr (cross j).succ) ≤ m - drop) :
    m + (k - 1) * drop ≤ recoverySteps Sys tr ∧ m + k + (k - 1) * drop ≤ T := by
  let seg : Fin k → Finset (Fin T) := fun j =>
    if h0 : j.1 = 0 then
      recoverySet Sys tr ∩ stepInterval T 0 (cross j).1
    else
      recoverySet Sys tr ∩
        stepInterval T ((cross ⟨j.1 - 1, by omega⟩).1 + 1) (cross j).1
  have hseg_sub : ∀ j : Fin k, seg j ⊆ recoverySet Sys tr := by
    intro j
    dsimp only [seg]
    split_ifs <;> exact Finset.inter_subset_left
  have hseg_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) seg := by
    intro j₁ _ j₂ _ hne
    change Disjoint (seg j₁) (seg j₂)
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    have hlt_or : j₁ < j₂ ∨ j₂ < j₁ := lt_or_gt_of_ne hne
    rcases hlt_or with hlt | hlt
    · have ht₁_lt : t.1 < (cross j₁).1 := by
        dsimp only [seg] at ht₁
        split_ifs at ht₁ <;>
          exact ((Finset.mem_filter.mp (Finset.mem_inter.mp ht₁).2).2).2
      have hj₂_ne : j₂.1 ≠ 0 := by
        have : j₁.1 < j₂.1 := hlt
        omega
      have ht₂_ge : (cross ⟨j₂.1 - 1, by omega⟩).1 + 1 ≤ t.1 := by
        dsimp only [seg] at ht₂
        simp only [hj₂_ne, ↓reduceDIte] at ht₂
        exact ((Finset.mem_filter.mp (Finset.mem_inter.mp ht₂).2).2).1
      have hj_le : j₁ ≤ ⟨j₂.1 - 1, by omega⟩ := by
        show j₁.1 ≤ j₂.1 - 1
        have : j₁.1 < j₂.1 := hlt
        omega
      have hcross_le : (cross j₁).1 ≤ (cross ⟨j₂.1 - 1, by omega⟩).1 :=
        hmono.monotone hj_le
      omega
    · have ht₂_lt : t.1 < (cross j₂).1 := by
        dsimp only [seg] at ht₂
        split_ifs at ht₂ <;>
          exact ((Finset.mem_filter.mp (Finset.mem_inter.mp ht₂).2).2).2
      have hj₁_ne : j₁.1 ≠ 0 := by
        have : j₂.1 < j₁.1 := hlt
        omega
      have ht₁_ge : (cross ⟨j₁.1 - 1, by omega⟩).1 + 1 ≤ t.1 := by
        dsimp only [seg] at ht₁
        simp only [hj₁_ne, ↓reduceDIte] at ht₁
        exact ((Finset.mem_filter.mp (Finset.mem_inter.mp ht₁).2).2).1
      have hj_le : j₂ ≤ ⟨j₁.1 - 1, by omega⟩ := by
        show j₂.1 ≤ j₁.1 - 1
        have : j₂.1 < j₁.1 := hlt
        omega
      have hcross_le : (cross j₂).1 ≤ (cross ⟨j₁.1 - 1, by omega⟩).1 :=
        hmono.monotone hj_le
      omega
  have hseg_zero : m ≤ (seg ⟨0, hk⟩).card := by
    dsimp only [seg]
    simp only [↓reduceDIte]
    have hdiff := recoverySteps_ge_potential_diff Sys tr hstep
      (Nat.zero_le (cross ⟨0, hk⟩).1) (Nat.le_of_lt (cross ⟨0, hk⟩).2)
    have hfull0 := hfull ⟨0, hk⟩
    have htr0 : tr ⟨0, Nat.lt_succ_of_le ((Nat.zero_le _).trans
        (Nat.le_of_lt (cross ⟨0, hk⟩).2))⟩ = tr 0 := rfl
    have htrc :
        tr ⟨(cross ⟨0, hk⟩).1, Nat.lt_succ_of_le (Nat.le_of_lt (cross ⟨0, hk⟩).2)⟩ =
          tr (cross ⟨0, hk⟩).castSucc := rfl
    rw [htr0, htrc, hinit] at hdiff
    omega
  have hseg_pos : ∀ j : Fin k, j.1 ≠ 0 → drop ≤ (seg j).card := by
    intro j hj
    dsimp only [seg]
    simp only [hj, ↓reduceDIte]
    let jprev : Fin k := ⟨j.1 - 1, by omega⟩
    have hlt : jprev < j := by
      show j.1 - 1 < j.1
      omega
    have hcross_lt : (cross jprev).1 < (cross j).1 := hmono hlt
    have hdiff := recoverySteps_ge_potential_diff Sys tr hstep
      (Nat.succ_le_of_lt hcross_lt) (Nat.le_of_lt (cross j).2)
    have hfull_j := hfull j
    have hdrop_prev := hdrop_after jprev
    have htr_prev : tr ⟨(cross jprev).1 + 1,
        Nat.lt_succ_of_le ((Nat.succ_le_of_lt hcross_lt).trans (Nat.le_of_lt (cross j).2))⟩ =
        tr (cross jprev).succ := rfl
    have htr_j : tr ⟨(cross j).1, Nat.lt_succ_of_le (Nat.le_of_lt (cross j).2)⟩ =
        tr (cross j).castSucc := rfl
    rw [htr_prev, htr_j] at hdiff
    change Sys.ψ (tr (cross j).castSucc) - Sys.ψ (tr (cross jprev).succ) ≤
      (recoverySet Sys tr ∩
        stepInterval T ((cross ⟨j.1 - 1, by omega⟩).1 + 1) (cross j).1).card at hdiff
    omega
  have hrec_lb : m + (k - 1) * drop ≤ recoverySteps Sys tr := by
    have hunion_sub : Finset.univ.biUnion seg ⊆ recoverySet Sys tr := by
      intro t ht
      rcases Finset.mem_biUnion.mp ht with ⟨j, _, htj⟩
      exact hseg_sub j htj
    have hcard_union : (Finset.univ.biUnion seg).card = ∑ j : Fin k, (seg j).card :=
      Finset.card_biUnion (by simpa using hseg_disj)
    have hsum_split :
        ∑ j : Fin k, (seg j).card =
          (seg ⟨0, hk⟩).card +
            ∑ j ∈ Finset.univ.erase (⟨0, hk⟩ : Fin k), (seg j).card :=
      (Finset.add_sum_erase Finset.univ (fun j => (seg j).card) (Finset.mem_univ _)).symm
    have herase_lb :
        (k - 1) * drop ≤ ∑ j ∈ Finset.univ.erase (⟨0, hk⟩ : Fin k), (seg j).card := by
      calc (k - 1) * drop
          = (Finset.univ.erase (⟨0, hk⟩ : Fin k)).card * drop := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        _ = ∑ _j ∈ Finset.univ.erase (⟨0, hk⟩ : Fin k), drop := by
              rw [Finset.sum_const, Nat.nsmul_eq_mul]
        _ ≤ ∑ j ∈ Finset.univ.erase (⟨0, hk⟩ : Fin k), (seg j).card := by
              refine Finset.sum_le_sum ?_
              intro j hj
              have hne : j ≠ ⟨0, hk⟩ := (Finset.mem_erase.mp hj).1
              exact hseg_pos j (fun h0 => hne (Fin.ext h0))
    have hle_rec : (Finset.univ.biUnion seg).card ≤ recoverySteps Sys tr :=
      Finset.card_le_card hunion_sub
    rw [hcard_union, hsum_split] at hle_rec
    omega
  refine ⟨hrec_lb, ?_⟩
  let C : Finset (Fin T) := Finset.univ.image cross
  have hC_card : C.card = k := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (recoverySet Sys tr) C := by
    rw [Finset.disjoint_left]
    intro t ht_rec ht_C
    rcases Finset.mem_image.mp ht_C with ⟨j, _, rfl⟩
    have hinc : Sys.ψ (tr (cross j).castSucc) < Sys.ψ (tr (cross j).succ) :=
      (Finset.mem_filter.mp ht_rec).2
    have hfull_j := hfull j
    have hdrop_j := hdrop_after j
    omega
  have htotal : recoverySteps Sys tr + k ≤ T := by
    calc recoverySteps Sys tr + k
        = (recoverySet Sys tr).card + C.card := by rw [recoverySteps, hC_card]
      _ = (recoverySet Sys tr ∪ C).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = T := by rw [Finset.card_univ, Fintype.card_fin]
  omega

/-! ### Part 2: Genuine Recomputation Time-Space Tradeoff on `MultiOutput K_{m, m}` -/

/-- Vertices of the complete bipartite multi-output DAG `K_{m, m}`:
`Sum.inl i` is input `u_i` and `Sum.inr j` is output `v_j`. -/
abbrev KmmNode (m : ℕ) := Fin m ⊕ Fin m

/-- A pebble configuration on `K_{m, m}` is a finite set of pebbled vertices. -/
abbrev KmmConfig (m : ℕ) := Finset (KmmNode m)

/-- The set of all `m` input vertices `{u_0, ..., u_{m-1}}` of `K_{m, m}`. -/
def inputNodes (m : ℕ) : KmmConfig m :=
  Finset.univ.image Sum.inl

/-- Number of pebbles currently placed on input vertices of `K_{m, m}`. -/
def inputCount {m : ℕ} (C : KmmConfig m) : ℕ :=
  (C.filter (fun v : KmmNode m => v.isLeft = true)).card

theorem card_inputNodes (m : ℕ) : (inputNodes m).card = m := by
  rw [inputNodes, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ, Fintype.card_fin]

theorem inputCount_empty (m : ℕ) : inputCount (∅ : KmmConfig m) = 0 := by
  simp [inputCount]

theorem inputCount_ge_of_inputNodes_subset {m : ℕ} {C : KmmConfig m}
    (hin : inputNodes m ⊆ C) : m ≤ inputCount C := by
  have hsub : inputNodes m ⊆ C.filter (fun v : KmmNode m => v.isLeft = true) := by
    intro v hv
    rw [Finset.mem_filter]
    refine ⟨hin hv, ?_⟩
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    rfl
  calc m = (inputNodes m).card := (card_inputNodes m).symm
    _ ≤ (C.filter (fun v : KmmNode m => v.isLeft = true)).card := Finset.card_le_card hsub

theorem inputCount_le_sub_one_of_inr_mem {m : ℕ} {C : KmmConfig m} {j : Fin m}
    (hmem : Sum.inr j ∈ C) (hcard : C.card ≤ m) : inputCount C ≤ m - 1 := by
  have hnot : Sum.inr j ∉ C.filter (fun v : KmmNode m => v.isLeft = true) := by
    simp
  have hsub : insert (Sum.inr j) (C.filter (fun v : KmmNode m => v.isLeft = true)) ⊆ C := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact hmem
    · exact (Finset.mem_filter.mp hv').1
  have hle : inputCount C + 1 ≤ C.card := by
    rw [inputCount, ← Finset.card_insert_of_notMem hnot]
    exact Finset.card_le_card hsub
  omega

theorem inputCount_insert_inl_le {m : ℕ} (i : Fin m) (C : KmmConfig m) :
    inputCount (insert (Sum.inl i) C) ≤ inputCount C + 1 := by
  unfold inputCount
  rw [Finset.filter_insert]
  simp only [Sum.isLeft_inl, ↓reduceIte]
  exact Finset.card_insert_le _ _

theorem inputCount_insert_inr {m : ℕ} (j : Fin m) (C : KmmConfig m) :
    inputCount (insert (Sum.inr j) C) = inputCount C := by
  unfold inputCount
  rw [Finset.filter_insert]
  simp

theorem inputCount_erase_le {m : ℕ} (v : KmmNode m) (C : KmmConfig m) :
    inputCount (C.erase v) ≤ inputCount C :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v C))

/-- Legal black pebbling transitions on `K_{m, m}` with space budget `S` pebbles, allowing input
placement, output placement, input-to-output sliding, pebble removal, and idle steps. -/
inductive KmmStep (m S : ℕ) : KmmConfig m → KmmConfig m → Prop where
  /-- Place a pebble on input `u_i` when fewer than `S` pebbles are currently on the graph. -/
  | placeInput {C : KmmConfig m} (i : Fin m) (hcard : C.card < S) :
      KmmStep m S C (insert (Sum.inl i) C)
  /-- Place a pebble on output `v_j` when all `m` inputs are pebbled and `< S` pebbles are used. -/
  | placeOutput {C : KmmConfig m} (j : Fin m) (hin : inputNodes m ⊆ C) (hcard : C.card < S) :
      KmmStep m S C (insert (Sum.inr j) C)
  /-- Slide a pebble from input `u_i` to output `v_j` when all `m` inputs are pebbled. -/
  | slideOutput {C : KmmConfig m} (i j : Fin m) (hin : inputNodes m ⊆ C) (hcard : C.card ≤ S) :
      KmmStep m S C (insert (Sum.inr j) (C.erase (Sum.inl i)))
  /-- Remove any pebble `v` from the configuration. -/
  | remove {C : KmmConfig m} (v : KmmNode m) (hcard : C.card ≤ S) :
      KmmStep m S C (C.erase v)
  /-- Idle transition leaving the configuration unchanged. -/
  | idle {C : KmmConfig m} (hcard : C.card ≤ S) :
      KmmStep m S C C

theorem kmmStep_card_left_le {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (h : KmmStep m S C₁ C₂) : C₁.card ≤ S := by
  cases h with
  | placeInput _ hcard => omega
  | placeOutput _ _ hcard => omega
  | slideOutput _ _ _ hcard => exact hcard
  | remove _ hcard => exact hcard
  | idle hcard => exact hcard

theorem kmmStep_card_right_le {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (h : KmmStep m S C₁ C₂) : C₂.card ≤ S := by
  cases h with
  | placeInput i hcard =>
    exact le_trans (Finset.card_insert_le _ _) (by omega)
  | placeOutput j _ hcard =>
    exact le_trans (Finset.card_insert_le _ _) (by omega)
  | slideOutput i j hin hcard =>
    have hmem : Sum.inl i ∈ C₁ := hin (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have herase : (C₁.erase (Sum.inl i)).card + 1 = C₁.card := Finset.card_erase_add_one hmem
    have hins := Finset.card_insert_le (Sum.inr j) (C₁.erase (Sum.inl i))
    omega
  | remove v hcard =>
    exact le_trans (Finset.card_erase_le) hcard
  | idle hcard =>
    exact hcard

theorem kmmStep_inputCount_le_succ {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (h : KmmStep m S C₁ C₂) : inputCount C₂ ≤ inputCount C₁ + 1 := by
  cases h with
  | placeInput i _ =>
    exact inputCount_insert_inl_le i _
  | placeOutput j _ _ =>
    rw [inputCount_insert_inr]
    omega
  | slideOutput i j _ _ =>
    rw [inputCount_insert_inr]
    exact le_trans (inputCount_erase_le _ _) (Nat.le_succ _)
  | remove v _ =>
    exact le_trans (inputCount_erase_le _ _) (Nat.le_succ _)
  | idle _ =>
    omega

/-- The `SeparatorSystem` induced by `KmmStep m S` and the input-pebble potential `inputCount`. -/
def kmmSeparatorSystem (m S : ℕ) : SeparatorSystem (KmmConfig m) where
  Step := KmmStep m S
  ψ := inputCount
  step_inc_le_one := kmmStep_inputCount_le_succ

/-- Any `KmmStep` that introduces a newly pebbled output `Sum.inr j` must start from a
configuration containing all `m` inputs, and can introduce no other newly pebbled output. -/
theorem kmmStep_new_output {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (h : KmmStep m S C₁ C₂) {j : Fin m}
    (hnot : Sum.inr j ∉ C₁) (hin : Sum.inr j ∈ C₂) :
    inputNodes m ⊆ C₁ ∧
      ∀ j' : Fin m, Sum.inr j' ∉ C₁ → Sum.inr j' ∈ C₂ → j' = j := by
  cases h with
  | placeInput i _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
    · exact absurd hmem hnot
  | placeOutput j₀ hinputs _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
      refine ⟨hinputs, fun j' hnot' hin' => ?_⟩
      rcases Finset.mem_insert.mp hin' with hEq' | hmem'
      · exact Sum.inr.inj hEq'
      · exact absurd hmem' hnot'
    · exact absurd hmem hnot
  | slideOutput i j₀ hinputs _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
      refine ⟨hinputs, fun j' hnot' hin' => ?_⟩
      rcases Finset.mem_insert.mp hin' with hEq' | hmem'
      · exact Sum.inr.inj hEq'
      · exact absurd (Finset.mem_of_mem_erase hmem') hnot'
    · exact absurd (Finset.mem_of_mem_erase hmem) hnot
  | remove v _ =>
    exact absurd (Finset.mem_of_mem_erase hin) hnot
  | idle _ =>
    exact absurd hin hnot

/-- A valid black pebbling of `K_{m, m}` using at most `S` pebbles: starts at `∅`, respects the
space bound `S` and `KmmStep` rules at every step, and pebbles every output vertex `Sum.inr j` at
some time. -/
structure ValidKmmPebbling (m S : ℕ) where
  /-- Total number of transition steps. -/
  steps : ℕ
  /-- Sequence of configurations of length `steps + 1`. -/
  trace : Fin (steps + 1) → KmmConfig m
  /-- The pebbling starts with the empty configuration. -/
  init_empty : trace 0 = ∅
  /-- Every configuration uses at most `S` pebbles. -/
  space_le : ∀ t : Fin (steps + 1), (trace t).card ≤ S
  /-- Every consecutive transition is a legal `KmmStep`. -/
  valid_step : ∀ t : Fin steps, KmmStep m S (trace t.castSucc) (trace t.succ)
  /-- Every output `v_j` is pebbled at least once along the trace. -/
  outputs_computed : ∀ j : Fin m, ∃ t : Fin (steps + 1), Sum.inr j ∈ trace t

/-- Number of input-pebble placement steps along a valid pebbling `P` of `K_{m, m}`, defined as the
number of steps at which `inputCount` strictly increases (equivalently, `recoverySteps` of
`kmmSeparatorSystem`). -/
def inputPlacements {m S : ℕ} (P : ValidKmmPebbling m S) : ℕ :=
  recoverySteps (kmmSeparatorSystem m S) P.trace

private theorem exists_first_output_time {m S : ℕ} (P : ValidKmmPebbling m S) (j : Fin m) :
    ∃ n : ℕ, ∃ hn : n < P.steps + 1, Sum.inr j ∈ P.trace ⟨n, hn⟩ := by
  rcases P.outputs_computed j with ⟨t, ht⟩
  exact ⟨t.1, t.2, ht⟩

/-- The step index `t : Fin P.steps` at which output `j` is pebbled for the very first time
(transitioning from `t.castSucc` to `t.succ`). -/
noncomputable def firstOutStep {m S : ℕ} (P : ValidKmmPebbling m S) (j : Fin m) : Fin P.steps :=
  let n := Nat.find (exists_first_output_time P j)
  have hspec : ∃ hn : n < P.steps + 1, Sum.inr j ∈ P.trace ⟨n, hn⟩ :=
    Nat.find_spec (exists_first_output_time P j)
  have hn_pos : 0 < n := by
    rcases hspec with ⟨hn, hmem⟩
    by_contra h0
    have hn0 : n = 0 := by omega
    have h0_eq : (⟨n, hn⟩ : Fin (P.steps + 1)) = 0 := Fin.ext hn0
    rw [h0_eq, P.init_empty] at hmem
    simp at hmem
  ⟨n - 1, by rcases hspec with ⟨hn, _⟩; omega⟩

private theorem firstOutStep_spec {m S : ℕ} (P : ValidKmmPebbling m S) (j : Fin m) :
    Sum.inr j ∉ P.trace (firstOutStep P j).castSucc ∧
      Sum.inr j ∈ P.trace (firstOutStep P j).succ := by
  classical
  dsimp only [firstOutStep]
  set n := Nat.find (exists_first_output_time P j)
  have hspec : ∃ hn : n < P.steps + 1, Sum.inr j ∈ P.trace ⟨n, hn⟩ :=
    Nat.find_spec (exists_first_output_time P j)
  rcases hspec with ⟨hn, hmem⟩
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    have h0_eq : (⟨n, hn⟩ : Fin (P.steps + 1)) = 0 := Fin.ext hn0
    rw [h0_eq, P.init_empty] at hmem
    simp at hmem
  have hlt : n - 1 < n := by omega
  have hnot_prev : Sum.inr j ∉ P.trace ⟨n - 1, by omega⟩ := by
    intro hprev
    exact Nat.find_min (exists_first_output_time P j) hlt ⟨by omega, hprev⟩
  refine ⟨hnot_prev, ?_⟩
  convert hmem using 2
  ext
  simp only [Fin.val_succ]
  omega

private theorem firstOutStep_injective {m S : ℕ} (P : ValidKmmPebbling m S) :
    Function.Injective (firstOutStep P) := by
  intro j₁ j₂ heq
  have h1 := firstOutStep_spec P j₁
  have h2 := firstOutStep_spec P j₂
  rw [heq] at h1
  have hnew := kmmStep_new_output (P.valid_step (firstOutStep P j₂)) h2.1 h2.2
  exact hnew.2 j₁ h1.1 h1.2

/-- **Main Lower Bound (`S = m` Forced Recomputation on `K_{m, m}`)**:
For every `m ≥ 1` and every valid black pebbling `P` of `K_{m, m}` using at most `m` pebbles,
`P` must perform at least `2 * m - 1` input placements (forcing at least `m - 1` input
recomputations) and at least `3 * m - 1` total steps. -/
theorem k_mm_recomputation_lower_bound {m : ℕ} (hm : 1 ≤ m)
    (P : ValidKmmPebbling m m) :
    2 * m - 1 ≤ inputPlacements P ∧ 3 * m - 1 ≤ P.steps := by
  classical
  let S_cross : Finset (Fin P.steps) := Finset.univ.image (firstOutStep P)
  have hcard : S_cross.card = m := by
    rw [Finset.card_image_of_injective _ (firstOutStep_injective P),
      Finset.card_univ, Fintype.card_fin]
  let cross : Fin m → Fin P.steps := S_cross.orderEmbOfFin hcard
  have hmono : StrictMono cross := (S_cross.orderEmbOfFin hcard).strictMono
  have hfull : ∀ r : Fin m, m ≤ inputCount (P.trace (cross r).castSucc) := by
    intro r
    have hmem : cross r ∈ S_cross := Finset.orderEmbOfFin_mem S_cross hcard r
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    rw [← hj]
    have hspec := firstOutStep_spec P j
    have hnew := kmmStep_new_output (P.valid_step (firstOutStep P j)) hspec.1 hspec.2
    exact inputCount_ge_of_inputNodes_subset hnew.1
  have hdrop_after : ∀ r : Fin m, inputCount (P.trace (cross r).succ) ≤ m - 1 := by
    intro r
    have hmem : cross r ∈ S_cross := Finset.orderEmbOfFin_mem S_cross hcard r
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    rw [← hj]
    have hspec := firstOutStep_spec P j
    exact inputCount_le_sub_one_of_inr_mem hspec.2 (P.space_le _)
  have hinit : (kmmSeparatorSystem m m).ψ (P.trace 0) = 0 := by
    simp [kmmSeparatorSystem, P.init_empty, inputCount]
  have hmain := recomputationLowerBound_of_separator
    (kmmSeparatorSystem m m) P.trace P.valid_step hm hm hinit cross hmono hfull hdrop_after
  change m + (m - 1) * 1 ≤ inputPlacements P ∧ m + m + (m - 1) * 1 ≤ P.steps at hmain
  omega

/-! ### Zero-Recomputation Upper Bounds at `S = m + 1` and `S = 2 * m` -/

/-- The first `k` input vertices `{u_0, ..., u_{k-1}}` of `K_{m, m}`. -/
def prefixInputs (m k : ℕ) : KmmConfig m :=
  (Finset.univ.filter (fun i : Fin m => i.1 < k)).image Sum.inl

/-- The first `k` output vertices `{v_0, ..., v_{k-1}}` of `K_{m, m}`. -/
def prefixOutputs (m k : ℕ) : KmmConfig m :=
  (Finset.univ.filter (fun j : Fin m => j.1 < k)).image Sum.inr

private theorem prefixInputs_zero (m : ℕ) : prefixInputs m 0 = ∅ := by
  simp [prefixInputs]

private theorem prefixOutputs_zero (m : ℕ) : prefixOutputs m 0 = ∅ := by
  simp [prefixOutputs]

private theorem prefixInputs_eq_inputNodes (m : ℕ) : prefixInputs m m = inputNodes m := by
  ext v
  simp [prefixInputs, inputNodes]

private theorem prefixInputs_succ {m k : ℕ} (hk : k < m) :
    prefixInputs m (k + 1) = insert (Sum.inl ⟨k, hk⟩) (prefixInputs m k) := by
  ext v
  simp only [prefixInputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases heq : i.1 = k
    · left
      exact congrArg Sum.inl (Fin.ext heq)
    · right
      exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, by omega, rfl⟩

private theorem prefixOutputs_succ {m k : ℕ} (hk : k < m) :
    prefixOutputs m (k + 1) = insert (Sum.inr ⟨k, hk⟩) (prefixOutputs m k) := by
  ext v
  simp only [prefixOutputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases heq : j.1 = k
    · left
      exact congrArg Sum.inr (Fin.ext heq)
    · right
      exact ⟨j, by omega, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨j, by omega, rfl⟩

private theorem card_prefixInputs {m k : ℕ} (hk : k ≤ m) :
    (prefixInputs m k).card = k := by
  induction k with
  | zero => simp [prefixInputs_zero]
  | succ k ih =>
    have hk' : k < m := by omega
    have hnot : Sum.inl ⟨k, hk'⟩ ∉ prefixInputs m k := by
      simp [prefixInputs]
    rw [prefixInputs_succ hk', Finset.card_insert_of_notMem hnot, ih (Nat.le_of_lt hk')]

private theorem card_prefixOutputs {m k : ℕ} (hk : k ≤ m) :
    (prefixOutputs m k).card = k := by
  induction k with
  | zero => simp [prefixOutputs_zero]
  | succ k ih =>
    have hk' : k < m := by omega
    have hnot : Sum.inr ⟨k, hk'⟩ ∉ prefixOutputs m k := by
      simp [prefixOutputs]
    rw [prefixOutputs_succ hk', Finset.card_insert_of_notMem hnot, ih (Nat.le_of_lt hk')]

private theorem inputCount_prefixInputs {m k : ℕ} (hk : k ≤ m) :
    inputCount (prefixInputs m k) = k := by
  have hfilt :
      (prefixInputs m k).filter (fun v : KmmNode m => v.isLeft = true) = prefixInputs m k := by
    rw [Finset.filter_eq_self]
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    rfl
  rw [inputCount, hfilt, card_prefixInputs hk]

private theorem inputCount_inputNodes (m : ℕ) : inputCount (inputNodes m) = m := by
  rw [← prefixInputs_eq_inputNodes]
  exact inputCount_prefixInputs le_rfl

private theorem inputCount_inputNodes_union_prefixOutputs (m k : ℕ) :
    inputCount (inputNodes m ∪ prefixOutputs m k) = m := by
  have hfilt :
      (inputNodes m ∪ prefixOutputs m k).filter (fun v : KmmNode m => v.isLeft = true) =
        inputNodes m := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_union, inputNodes, prefixOutputs, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩ | ⟨j, _, rfl⟩, hleft⟩
      · exact ⟨i, rfl⟩
      · simp at hleft
    · rintro ⟨i, rfl⟩
      exact ⟨Or.inl ⟨i, rfl⟩, rfl⟩
  rw [inputCount, hfilt, card_inputNodes]

private theorem card_filter_lt {N m : ℕ} (hm : m ≤ N) :
    (Finset.univ.filter (fun t : Fin N => t.1 < m)).card = m := by
  have heq :
      Finset.univ.filter (fun t : Fin N => t.1 < m) =
        Finset.univ.image (fun i : Fin m => (⟨i.1, lt_of_lt_of_le i.2 hm⟩ : Fin N)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ht
      exact ⟨⟨t.1, ht⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.2
  rw [heq, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro i₁ i₂ h
    exact Fin.ext (by simpa using congrArg Fin.val h)

/-- **Zero-Recomputation Upper Bound at `S = m + 1`**:
With just one extra pebble (`S = m + 1`), `K_{m, m}` admits a valid pebbling with **zero input
recomputation** (`inputPlacements P = m`) in `3 * m` steps: place all `m` inputs once, then
repeatedly place and immediately remove each output `v_j`. -/
theorem k_mm_zero_recomp_at_m_plus_one (m : ℕ) :
    ∃ P : ValidKmmPebbling m (m + 1), inputPlacements P = m ∧ P.steps = 3 * m := by
  let tr : Fin (3 * m + 1) → KmmConfig m := fun t =>
    if hle : t.1 ≤ m then
      prefixInputs m t.1
    else if hodd : (t.1 - m) % 2 = 1 then
      insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
    else
      inputNodes m
  have hspace : ∀ t : Fin (3 * m + 1), (tr t).card ≤ m + 1 := by
    intro t
    dsimp only [tr]
    split_ifs with hle hodd
    · rw [card_prefixInputs hle]
      omega
    · have hle_ins := Finset.card_insert_le
        (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
      rw [card_inputNodes] at hle_ins
      exact hle_ins
    · rw [card_inputNodes]
      omega
  have hstep : ∀ t : Fin (3 * m), KmmStep m (m + 1) (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInputs m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = insert (Sum.inl ⟨t.1, hlt⟩) (prefixInputs m t.1) := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInputs_succ hlt
      rw [h1, h2]
      exact KmmStep.placeInput ⟨t.1, hlt⟩ (by rw [card_prefixInputs (Nat.le_of_lt hlt)]; omega)
    · by_cases heven : (t.1 - m) % 2 = 0
      · have h1 : tr t.castSucc = inputNodes m := by
          dsimp only [tr]
          by_cases heq : t.1 = m
          · have hle1 : t.castSucc.1 ≤ m := by simp; omega
            simp only [hle1, ↓reduceDIte]
            simpa [heq] using prefixInputs_eq_inputNodes m
          · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hne1 : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
            simp only [hgt1, hne1, ↓reduceDIte]
        have h2 : tr t.succ =
            insert (Sum.inr ⟨(t.1 - m) / 2, by omega⟩) (inputNodes m) := by
          dsimp only [tr]
          have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
          have hodd2 : (t.succ.1 - m) % 2 = 1 := by simp; omega
          simp only [hgt2, hodd2, ↓reduceDIte]
          congr 2
          ext
          simp only [Fin.val_succ]
          omega
        rw [h1, h2]
        exact KmmStep.placeOutput ⟨(t.1 - m) / 2, by omega⟩ subset_rfl
          (by rw [card_inputNodes]; omega)
      · have h1 : tr t.castSucc =
            insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m) := by
          dsimp only [tr]
          have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
          have hodd1 : (t.castSucc.1 - m) % 2 = 1 := by simp; omega
          simp only [hgt1, hodd1, ↓reduceDIte]
          rfl
        have h2 : tr t.succ = inputNodes m := by
          dsimp only [tr]
          have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
          have hne2 : (t.succ.1 - m) % 2 ≠ 1 := by simp; omega
          simp only [hgt2, hne2, ↓reduceDIte]
        have herase :
            (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).erase
              (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) = inputNodes m := by
          rw [Finset.erase_insert]
          simp [inputNodes]
        have hcard1 :
            (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).card ≤ m + 1 := by
          rw [← h1]
          exact hspace t.castSucc
        rw [h1, h2]
        simpa [herase] using KmmStep.remove (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) hcard1
  have hout : ∀ j : Fin m, ∃ t : Fin (3 * m + 1), Sum.inr j ∈ tr t := by
    intro j
    refine ⟨⟨m + 2 * j.1 + 1, by omega⟩, ?_⟩
    dsimp only [tr]
    have hgt : ¬ (m + 2 * j.1 + 1 ≤ m) := by omega
    have hodd : (m + 2 * j.1 + 1 - m) % 2 = 1 := by omega
    simp only [hgt, hodd, ↓reduceDIte]
    have hidx : (⟨(m + 2 * j.1 + 1 - m - 1) / 2, by omega⟩ : Fin m) = j := by
      ext
      simp only
      omega
    rw [hidx]
    exact Finset.mem_insert_self _ _
  let P : ValidKmmPebbling m (m + 1) :=
    { steps := 3 * m
      trace := tr
      init_empty := by simp [tr, prefixInputs_zero]
      space_le := hspace
      valid_step := hstep
      outputs_computed := hout }
  refine ⟨P, ?_, rfl⟩
  have hpsi : ∀ t : Fin (3 * m + 1), inputCount (tr t) = min t.1 m := by
    intro t
    dsimp only [tr]
    split_ifs with hle hodd
    · rw [inputCount_prefixInputs hle]
      omega
    · rw [inputCount_insert_inr, inputCount_inputNodes]
      omega
    · rw [inputCount_inputNodes]
      omega
  have hrec :
      recoverySet (kmmSeparatorSystem m (m + 1)) tr =
        Finset.univ.filter (fun t : Fin (3 * m) => t.1 < m) := by
    ext t
    simp only [recoverySet, kmmSeparatorSystem, Finset.mem_filter, Finset.mem_univ, true_and,
      hpsi, Fin.val_castSucc, Fin.val_succ]
    omega
  change (recoverySet (kmmSeparatorSystem m (m + 1)) tr).card = m
  rw [hrec, card_filter_lt (by omega)]

/-- **Zero-Recomputation, Optimal-Time Upper Bound at `S = 2 * m`**:
With `2 * m` pebbles, `K_{m, m}` admits a valid pebbling with **zero input recomputation**
(`inputPlacements P = m`) and optimal total time `P.steps = 2 * m`. -/
theorem k_mm_zero_recomp_at_two_m (m : ℕ) :
    ∃ P : ValidKmmPebbling m (2 * m), inputPlacements P = m ∧ P.steps = 2 * m := by
  let tr : Fin (2 * m + 1) → KmmConfig m := fun t =>
    if hle : t.1 ≤ m then
      prefixInputs m t.1
    else
      inputNodes m ∪ prefixOutputs m (t.1 - m)
  have hspace : ∀ t : Fin (2 * m + 1), (tr t).card ≤ 2 * m := by
    intro t
    dsimp only [tr]
    split_ifs with hle
    · rw [card_prefixInputs hle]
      omega
    · have hunion := Finset.card_union_le (inputNodes m) (prefixOutputs m (t.1 - m))
      rw [card_inputNodes, card_prefixOutputs (by omega)] at hunion
      omega
  have hstep : ∀ t : Fin (2 * m), KmmStep m (2 * m) (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInputs m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = insert (Sum.inl ⟨t.1, hlt⟩) (prefixInputs m t.1) := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInputs_succ hlt
      rw [h1, h2]
      exact KmmStep.placeInput ⟨t.1, hlt⟩ (by rw [card_prefixInputs (Nat.le_of_lt hlt)]; omega)
    · have h1 : tr t.castSucc = inputNodes m ∪ prefixOutputs m (t.1 - m) := by
        dsimp only [tr]
        by_cases heq : t.1 = m
        · have hle1 : t.castSucc.1 ≤ m := by simp; omega
          simp only [hle1, ↓reduceDIte]
          simp [heq, prefixInputs_eq_inputNodes, prefixOutputs_zero]
        · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
          simp only [hgt1, ↓reduceDIte]
          rfl
      have h2 : tr t.succ =
          insert (Sum.inr ⟨t.1 - m, by omega⟩)
            (inputNodes m ∪ prefixOutputs m (t.1 - m)) := by
        dsimp only [tr]
        have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
        simp only [hgt2, ↓reduceDIte]
        have hsub_eq : t.1 + 1 - m = (t.1 - m) + 1 := by omega
        simp only [Fin.val_succ, hsub_eq, prefixOutputs_succ (by omega : t.1 - m < m),
          Finset.union_insert]
      have hcard_lt : (inputNodes m ∪ prefixOutputs m (t.1 - m)).card < 2 * m := by
        have hunion := Finset.card_union_le (inputNodes m) (prefixOutputs m (t.1 - m))
        rw [card_inputNodes, card_prefixOutputs (by omega)] at hunion
        omega
      rw [h1, h2]
      exact KmmStep.placeOutput ⟨t.1 - m, by omega⟩ Finset.subset_union_left hcard_lt
  have hout : ∀ j : Fin m, ∃ t : Fin (2 * m + 1), Sum.inr j ∈ tr t := by
    intro j
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) j.2
    refine ⟨⟨2 * m, by omega⟩, ?_⟩
    dsimp only [tr]
    have hgt : ¬ (2 * m ≤ m) := by omega
    simp only [hgt, ↓reduceDIte]
    apply Finset.mem_union_right
    simp only [prefixOutputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, by omega, rfl⟩
  let P : ValidKmmPebbling m (2 * m) :=
    { steps := 2 * m
      trace := tr
      init_empty := by simp [tr, prefixInputs_zero]
      space_le := hspace
      valid_step := hstep
      outputs_computed := hout }
  refine ⟨P, ?_, rfl⟩
  have hpsi : ∀ t : Fin (2 * m + 1), inputCount (tr t) = min t.1 m := by
    intro t
    dsimp only [tr]
    split_ifs with hle
    · rw [inputCount_prefixInputs hle]
      omega
    · rw [inputCount_inputNodes_union_prefixOutputs]
      omega
  have hrec :
      recoverySet (kmmSeparatorSystem m (2 * m)) tr =
        Finset.univ.filter (fun t : Fin (2 * m) => t.1 < m) := by
    ext t
    simp only [recoverySet, kmmSeparatorSystem, Finset.mem_filter, Finset.mem_univ, true_and,
      hpsi, Fin.val_castSucc, Fin.val_succ]
    omega
  change (recoverySet (kmmSeparatorSystem m (2 * m)) tr).card = m
  rw [hrec, card_filter_lt (by omega)]

end Mathmatica.SeparatorRecomputation
