/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.SeparatorRecomputation

/-!
# Exact Idle-Invariant Pareto Frontier for Black Pebbling on `K_{m, m}`

This module extends `Mathmatica.SeparatorRecomputation` with a coupled two-potential conservation
identity (`CoupledSeparatorSystem`, `coupled_conservation_eq`, `coupledSeparatorLowerBound`) and
establishes the **exact** time-space Pareto frontier for sliding black pebbling on the complete
bipartite multi-output DAG `K_{m, m}` across all four standard completion conventions:

1. **VisitAll** (every output is pebbled at least once, arbitrary final configuration):
   - At `S = m`: exact minimum `inputPlacements = 2 * m - 1`, exact minimum `activeSteps = 4 * m - 2`.
   - At `m < S`: exact minimum `inputPlacements = m`, exact minimum
     `activeSteps = max (2 * m) (4 * m - 1 - S)`.
2. **VisitAllClean** (every output is pebbled at least once, final configuration `∅`):
   - At `S = m`: exact minimum `inputPlacements = 2 * m - 1`, exact minimum `activeSteps = 5 * m - 2`.
   - At `m < S`: exact minimum `inputPlacements = m`, exact minimum `activeSteps = 4 * m - 1`.
3. **CoexistAll** (all `m` outputs simultaneously pebbled in the final configuration):
   - Infeasible for `S < 2 * m - 1` (`k_mm_coexistAll_infeasible`).
   - For `2 * m - 1 ≤ S`: exact minimum `inputPlacements = m`, exact minimum `activeSteps = 2 * m`.
4. **CoexistAllClean** (final configuration equals `outputNodes m`):
   - Infeasible for `S < 2 * m - 1`.
   - For `2 * m - 1 ≤ S`: exact minimum `inputPlacements = m`, exact minimum
     `activeSteps = 3 * m - 1`.

Every lower bound holds for idle-invariant `activeSteps P.trace` (and hence for `P.steps`), and
every regime is matched by an explicit, constructive `ValidKmmPebbling` witness achieving exact
equality.

## Epistemic Discipline (Six-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file — including
  `coupled_conservation_eq`, `coupledSeparatorLowerBound`, `k_mm_visitAll_exact_lower_bound`,
  `k_mm_visitAllClean_exact_lower_bound`, `k_mm_coexistAll_infeasible`,
  `k_mm_coexistAll_exact_lower_bound`, `k_mm_coexistAllClean_exact_lower_bound`, and all four
  matching optimal upper bounds — are formally verified in Lean 4 with zero `sorry`s, zero warnings,
  and no extra axioms.
* **Model-Restricted**: All `K_{m, m}` lower and upper bounds apply strictly to the sliding black
  pebbling game (`KmmStep` / `ValidKmmPebbling`) with unit-capacity vertices and explicit
  predecessor requirements. They do not rule out algebraic cancellation, compression, or
  non-pebbling algorithms for specific functions computed on `K_{m, m}`.
* **Numerically Observed**: Exhaustive finite-state checks at small `(m, S)` independently agree
  with every formula proved here (`4m - 2`, `max(2m, 4m - 1 - S)`, `5m - 2`, `4m - 1`, `2m`,
  `3m - 1`, and the `2m - 1` coexistence threshold). No numerical data is assumed by any proof.
* **Conditional**: Transferring coupled-potential conservation bounds to general straight-line
  programs, RAMs, or Turing machines requires white-box dataflow / obliviousness assumptions
  linking machine states to unit-change potentials `(ψ, ω)`.
* **Heuristic / Structural Analogy**: The conservation law pairing active steps, final potential,
  and slide transitions against twice the increase counts is structurally analogous to accounting /
  amortized potential methods in pebbling and memory-hierarchy tradeoffs, without claiming general
  circuit-complexity equivalences.
* **Conjectural / Explicitly Not Claimed**: General algorithm time-space lower bounds, Turing
  machine or circuit lower bounds, and `P ≠ NP` are **NOT** claimed or implied by this module.
-/

namespace Mathmatica.KmmExactPareto

open Mathmatica.SeparatorRecomputation

/-! ### Part 1: `CoupledSeparatorSystem` & Exact Idle-Invariant Conservation Identity -/

/-- A `SeparatorSystem` augmented with a secondary unit-change potential `ω` (e.g., output pebble
count) satisfying coupled single-step constraints:
* both `ψ` and `ω` change by at most `1` per legal step;
* whenever `ψ` strictly increases, `ω` is unchanged;
* whenever `ψ` strictly decreases, `ω` does not decrease (allowing slide steps `(-1, +1)` and
  removal steps `(-1, 0)`, while forbidding simultaneous drops `(-1, -1)`). -/
structure CoupledSeparatorSystem (Q : Type*) extends SeparatorSystem Q where
  /-- Secondary unit-change potential. -/
  ω : Q → ℕ
  /-- Every legal transition decreases `ψ` by at most `1`. -/
  psi_dec_le_one : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ψ q₁ ≤ ψ q₂ + 1
  /-- Every legal transition increases `ω` by at most `1`. -/
  omega_inc_le_one : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ω q₂ ≤ ω q₁ + 1
  /-- Every legal transition decreases `ω` by at most `1`. -/
  omega_dec_le_one : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ω q₁ ≤ ω q₂ + 1
  /-- A strict increase in `ψ` cannot coincide with a change in `ω`. -/
  psi_inc_disjoint_omega_change : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ψ q₁ < ψ q₂ → ω q₂ = ω q₁
  /-- A strict decrease in `ψ` cannot coincide with a strict decrease in `ω`. -/
  psi_dec_disjoint_omega_dec : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ψ q₂ < ψ q₁ → ω q₁ ≤ ω q₂

/-- The set of non-idle step indices `t : Fin T` where the state actually changes. -/
def activeSet {Q : Type*} [DecidableEq Q] {T : ℕ} (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T => tr t.succ ≠ tr t.castSucc)

/-- The idle-invariant count of non-idle steps along `tr`. -/
def activeSteps {Q : Type*} [DecidableEq Q] {T : ℕ} (tr : Fin (T + 1) → Q) : ℕ :=
  (activeSet tr).card

/-- The set of step indices `t : Fin T` where `ω` strictly increases. -/
def omegaIncSet {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T => Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ))

/-- The set of slide step indices `t : Fin T` where `ψ` strictly decreases while `ω` strictly
increases. -/
def slideSet {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T =>
    Sys.ψ (tr t.succ) < Sys.ψ (tr t.castSucc) ∧ Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ))

/-- The set of step indices `t : Fin T` where either `ψ` or `ω` changes. -/
def coupledActiveSet {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T =>
    Sys.ψ (tr t.succ) ≠ Sys.ψ (tr t.castSucc) ∨ Sys.ω (tr t.succ) ≠ Sys.ω (tr t.castSucc))

/-- The count of steps where either `ψ` or `ω` changes. -/
def coupledActiveSteps {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q) : ℕ :=
  (coupledActiveSet Sys tr).card

theorem coupledActiveSteps_le_activeSteps {Q : Type*} [DecidableEq Q]
    (Sys : CoupledSeparatorSystem Q) {T : ℕ} (tr : Fin (T + 1) → Q) :
    coupledActiveSteps Sys tr ≤ activeSteps tr := by
  apply Finset.card_le_card
  intro t ht
  simp only [coupledActiveSet, activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  intro heq
  rcases ht with hψ | hω
  · exact hψ (congrArg Sys.ψ heq)
  · exact hω (congrArg Sys.ω heq)

theorem activeSteps_le_steps {Q : Type*} [DecidableEq Q] {T : ℕ} (tr : Fin (T + 1) → Q) :
    activeSteps tr ≤ T := by
  calc activeSteps tr
      = (activeSet tr).card := rfl
    _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = T := by rw [Finset.card_univ, Fintype.card_fin]

private theorem prefix_conservation_eq {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, Sys.Step (tr t.castSucc) (tr t.succ))
    (n : ℕ) (hn : n ≤ T) :
    (coupledActiveSet Sys tr ∩ stepInterval T 0 n).card +
      Sys.ψ (tr ⟨n, Nat.lt_succ_of_le hn⟩) +
      Sys.ω (tr ⟨n, Nat.lt_succ_of_le hn⟩) +
      (slideSet Sys tr ∩ stepInterval T 0 n).card =
    Sys.ψ (tr 0) + Sys.ω (tr 0) +
      2 * (recoverySet Sys.toSeparatorSystem tr ∩ stepInterval T 0 n).card +
      2 * (omegaIncSet Sys tr ∩ stepInterval T 0 n).card := by
  induction n with
  | zero =>
    have h0 : stepInterval T 0 0 = ∅ := by
      ext x
      simp [stepInterval]
    have htr0 : (⟨0, Nat.lt_succ_of_le hn⟩ : Fin (T + 1)) = 0 := rfl
    simp [h0, htr0]
  | succ k ih =>
    have hk : k < T := by omega
    have ih' := ih (Nat.le_of_lt hk)
    let t : Fin T := ⟨k, hk⟩
    have hstep_t := hstep t
    have hψ_inc := Sys.step_inc_le_one hstep_t
    have hψ_dec := Sys.psi_dec_le_one hstep_t
    have hω_inc := Sys.omega_inc_le_one hstep_t
    have hω_dec := Sys.omega_dec_le_one hstep_t
    have hψ_disj := Sys.psi_inc_disjoint_omega_change hstep_t
    have hω_disj := Sys.psi_dec_disjoint_omega_dec hstep_t
    have hcast : (⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩ : Fin (T + 1)) = t.castSucc := rfl
    have hsucc : (⟨k + 1, Nat.lt_succ_of_le hn⟩ : Fin (T + 1)) = t.succ := rfl
    rw [hcast] at ih'
    rw [hsucc]
    have hstep_int : stepInterval T 0 (k + 1) = insert t (stepInterval T 0 k) := by
      ext x
      simp only [stepInterval, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, t]
      omega
    have ht_not : t ∉ stepInterval T 0 k := by
      simp [stepInterval, t]
    have card_inter_step : ∀ (A : Finset (Fin T)),
        (A ∩ stepInterval T 0 (k + 1)).card =
          (A ∩ stepInterval T 0 k).card + if t ∈ A then 1 else 0 := by
      intro A
      rw [hstep_int]
      by_cases hmem : t ∈ A
      · rw [Finset.inter_insert_of_mem hmem, Finset.card_insert_of_notMem]
        · simp only [hmem, ↓reduceIte]
        · intro hm
          exact ht_not (Finset.mem_inter.mp hm).2
      · rw [Finset.inter_insert_of_notMem hmem]
        simp only [hmem, ↓reduceIte, Nat.add_zero]
    have hm1 : t ∈ coupledActiveSet Sys tr ↔
        Sys.ψ (tr t.succ) ≠ Sys.ψ (tr t.castSucc) ∨ Sys.ω (tr t.succ) ≠ Sys.ω (tr t.castSucc) := by
      simp [coupledActiveSet]
    have hm2 : t ∈ slideSet Sys tr ↔
        Sys.ψ (tr t.succ) < Sys.ψ (tr t.castSucc) ∧ Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ) := by
      simp [slideSet]
    have hm3 : t ∈ recoverySet Sys.toSeparatorSystem tr ↔
        Sys.ψ (tr t.castSucc) < Sys.ψ (tr t.succ) := by
      simp [recoverySet]
    have hm4 : t ∈ omegaIncSet Sys tr ↔
        Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ) := by
      simp [omegaIncSet]
    rw [card_inter_step (coupledActiveSet Sys tr),
      card_inter_step (slideSet Sys tr),
      card_inter_step (recoverySet Sys.toSeparatorSystem tr),
      card_inter_step (omegaIncSet Sys tr)]
    simp only [hm1, hm2, hm3, hm4]
    split_ifs <;> omega

/-- **Exact Idle-Invariant Conservation Identity**:
Along any legal trace of a `CoupledSeparatorSystem` starting from `(ψ, ω) = (0, 0)`,
`coupledActiveSteps + ψ(T) + ω(T) + |slideSet| = 2 * recoverySteps + 2 * |omegaIncSet|`. -/
theorem coupled_conservation_eq {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, Sys.Step (tr t.castSucc) (tr t.succ))
    (hinit_psi : Sys.ψ (tr 0) = 0)
    (hinit_omega : Sys.ω (tr 0) = 0) :
    coupledActiveSteps Sys tr +
      Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) +
      Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) +
      (slideSet Sys tr).card =
    2 * recoverySteps Sys.toSeparatorSystem tr + 2 * (omegaIncSet Sys tr).card := by
  have huniv : stepInterval T 0 T = Finset.univ := by
    ext x
    simp [stepInterval]
  have h := prefix_conservation_eq Sys tr hstep T le_rfl
  rw [huniv, Finset.inter_univ, Finset.inter_univ, Finset.inter_univ, Finset.inter_univ,
    hinit_psi, hinit_omega] at h
  change coupledActiveSteps Sys tr + Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) +
      Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) + (slideSet Sys tr).card =
    0 + 0 + 2 * recoverySteps Sys.toSeparatorSystem tr + 2 * (omegaIncSet Sys tr).card at h
  omega

/-- **Abstract Coupled Separator Lower Bound**:
Given a legal trace starting at `(ψ, ω) = (0, 0)` that reaches `ψ ≥ m` (with `1 ≤ m`), performs at
least `k` strict `ω`-increases, and whose slide steps all cross from `ψ ≥ m` down to `ψ ≤ m - 1`:
1. `m + k ≤ coupledActiveSteps Sys tr`;
2. `2 * m + 2 * k - 1 ≤ coupledActiveSteps Sys tr + ψ(T) + ω(T)`;
3. For every `1 ≤ s ≤ (slideSet Sys tr).card`, `m + (s - 1) ≤ recoverySteps` and
   `2 * m + 2 * k + s - 2 ≤ coupledActiveSteps Sys tr + ψ(T) + ω(T)`. -/
theorem coupledSeparatorLowerBound {Q : Type*} (Sys : CoupledSeparatorSystem Q) {T : ℕ}
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, Sys.Step (tr t.castSucc) (tr t.succ))
    {m k : ℕ} (hm : 1 ≤ m)
    (hinit_psi : Sys.ψ (tr 0) = 0)
    (hinit_omega : Sys.ω (tr 0) = 0)
    (hreach : ∃ t : Fin (T + 1), m ≤ Sys.ψ (tr t))
    (hk : k ≤ (omegaIncSet Sys tr).card)
    (hslide : ∀ t ∈ slideSet Sys tr,
      m ≤ Sys.ψ (tr t.castSucc) ∧ Sys.ψ (tr t.succ) ≤ m - 1) :
    m + k ≤ coupledActiveSteps Sys tr ∧
    2 * m + 2 * k - 1 ≤ coupledActiveSteps Sys tr +
      Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) + Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) ∧
    ∀ s : ℕ, 1 ≤ s → s ≤ (slideSet Sys tr).card →
      m + (s - 1) ≤ recoverySteps Sys.toSeparatorSystem tr ∧
      2 * m + 2 * k + s - 2 ≤ coupledActiveSteps Sys tr +
        Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) + Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) := by
  have hrec_ge_m : m ≤ recoverySteps Sys.toSeparatorSystem tr := by
    rcases hreach with ⟨t, ht⟩
    have hdiff := recoverySteps_ge_potential_diff Sys.toSeparatorSystem tr hstep
      (Nat.zero_le t.1) (Nat.le_of_lt_succ t.2)
    have htr0 : tr ⟨0, Nat.lt_succ_of_le ((Nat.zero_le t.1).trans (Nat.le_of_lt_succ t.2))⟩ =
        tr 0 := rfl
    have htrt : tr ⟨t.1, Nat.lt_succ_of_le (Nat.le_of_lt_succ t.2)⟩ = tr t := rfl
    rw [htr0, htrt, hinit_psi] at hdiff
    have hsub : (recoverySet Sys.toSeparatorSystem tr ∩ stepInterval T 0 t.1).card ≤
        recoverySteps Sys.toSeparatorSystem tr :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hcons := coupled_conservation_eq Sys tr hstep hinit_psi hinit_omega
  have hbound1 : m + k ≤ coupledActiveSteps Sys tr := by
    have hdisj : Disjoint (recoverySet Sys.toSeparatorSystem tr) (omegaIncSet Sys tr) := by
      rw [Finset.disjoint_left]
      intro t ht_rec ht_ω
      have hψ_lt : Sys.ψ (tr t.castSucc) < Sys.ψ (tr t.succ) := (Finset.mem_filter.mp ht_rec).2
      have hω_lt : Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ) := (Finset.mem_filter.mp ht_ω).2
      have hω_eq := Sys.psi_inc_disjoint_omega_change (hstep t) hψ_lt
      omega
    have hunion_sub :
        recoverySet Sys.toSeparatorSystem tr ∪ omegaIncSet Sys tr ⊆ coupledActiveSet Sys tr := by
      intro t ht
      simp only [coupledActiveSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp ht with ht_rec | ht_ω
      · left
        have hψ_lt : Sys.ψ (tr t.castSucc) < Sys.ψ (tr t.succ) := (Finset.mem_filter.mp ht_rec).2
        omega
      · right
        have hω_lt : Sys.ω (tr t.castSucc) < Sys.ω (tr t.succ) := (Finset.mem_filter.mp ht_ω).2
        omega
    have hcard : recoverySteps Sys.toSeparatorSystem tr + (omegaIncSet Sys tr).card ≤
        coupledActiveSteps Sys tr := by
      calc recoverySteps Sys.toSeparatorSystem tr + (omegaIncSet Sys tr).card
          = (recoverySet Sys.toSeparatorSystem tr ∪ omegaIncSet Sys tr).card :=
              (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ coupledActiveSteps Sys tr := Finset.card_le_card hunion_sub
    omega
  have hbound3 : ∀ s : ℕ, 1 ≤ s → s ≤ (slideSet Sys tr).card →
      m + (s - 1) ≤ recoverySteps Sys.toSeparatorSystem tr ∧
      2 * m + 2 * k + s - 2 ≤ coupledActiveSteps Sys tr +
        Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) + Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) := by
    intro s hs_pos hs_le
    let S_sl := (slideSet Sys tr).card
    have hS_pos : 1 ≤ S_sl := le_trans hs_pos hs_le
    let cross : Fin S_sl → Fin T := (slideSet Sys tr).orderEmbOfFin rfl
    have hmono : StrictMono cross := ((slideSet Sys tr).orderEmbOfFin rfl).strictMono
    have hfull : ∀ j : Fin S_sl, m ≤ Sys.ψ (tr (cross j).castSucc) := fun j =>
      (hslide (cross j) (Finset.orderEmbOfFin_mem (slideSet Sys tr) rfl j)).1
    have hdrop : ∀ j : Fin S_sl, Sys.ψ (tr (cross j).succ) ≤ m - 1 := fun j =>
      (hslide (cross j) (Finset.orderEmbOfFin_mem (slideSet Sys tr) rfl j)).2
    have hsep := recomputationLowerBound_of_separator Sys.toSeparatorSystem tr hstep
      hS_pos hm hinit_psi cross hmono hfull hdrop
    have hrec_sl : m + (S_sl - 1) ≤ recoverySteps Sys.toSeparatorSystem tr := by
      have := hsep.1
      omega
    refine ⟨by omega, by omega⟩
  have hbound2 :
      2 * m + 2 * k - 1 ≤ coupledActiveSteps Sys tr +
        Sys.ψ (tr ⟨T, Nat.lt_succ_self T⟩) + Sys.ω (tr ⟨T, Nat.lt_succ_self T⟩) := by
    by_cases hsl : (slideSet Sys tr).card = 0
    · omega
    · have hpos : 1 ≤ (slideSet Sys tr).card := by omega
      have h3 := (hbound3 (slideSet Sys tr).card hpos le_rfl).2
      omega
  exact ⟨hbound1, hbound2, hbound3⟩

/-! ### Part 2: Exact `K_{m, m}` Lower Bounds Across All Four Completion Conventions -/

/-- The set of all `m` output vertices `{v_0, ..., v_{m-1}}` of `K_{m, m}`. -/
def outputNodes (m : ℕ) : KmmConfig m :=
  Finset.univ.image Sum.inr

/-- Number of pebbles currently placed on output vertices of `K_{m, m}`. -/
def outputCount {m : ℕ} (C : KmmConfig m) : ℕ :=
  (C.filter (fun v : KmmNode m => v.isRight = true)).card

theorem card_outputNodes (m : ℕ) : (outputNodes m).card = m := by
  rw [outputNodes, Finset.card_image_of_injective _ Sum.inr_injective,
    Finset.card_univ, Fintype.card_fin]

theorem outputCount_empty (m : ℕ) : outputCount (∅ : KmmConfig m) = 0 := by
  simp [outputCount]

theorem inputCount_add_outputCount {m : ℕ} (C : KmmConfig m) :
    inputCount C + outputCount C = C.card := by
  unfold inputCount outputCount
  have hdisj : Disjoint
      (C.filter (fun v : KmmNode m => v.isLeft = true))
      (C.filter (fun v : KmmNode m => v.isRight = true)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rcases v with i | j
    · simp at hv2
    · simp at hv1
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext v
  simp only [Finset.mem_union, Finset.mem_filter]
  rcases v with i | j <;> simp

theorem inputCount_le_m {m : ℕ} (C : KmmConfig m) : inputCount C ≤ m := by
  have hsub : C.filter (fun v : KmmNode m => v.isLeft = true) ⊆ inputNodes m := by
    intro v hv
    rcases v with i | j
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · simp at hv
  calc inputCount C
      ≤ (inputNodes m).card := Finset.card_le_card hsub
    _ = m := card_inputNodes m

theorem inputCount_outputNodes (m : ℕ) : inputCount (outputNodes m) = 0 := by
  unfold inputCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hmem, hleft⟩
  rcases Finset.mem_image.mp hmem with ⟨j, _, rfl⟩
  simp at hleft

theorem outputCount_outputNodes (m : ℕ) : outputCount (outputNodes m) = m := by
  have h := inputCount_add_outputCount (outputNodes m)
  rw [inputCount_outputNodes, card_outputNodes] at h
  omega

private theorem inputCount_insert_inl_ge {m : ℕ} (i : Fin m) (C : KmmConfig m) :
    inputCount C ≤ inputCount (insert (Sum.inl i) C) :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))

private theorem inputCount_erase_inl_ge {m : ℕ} (v : KmmNode m) (C : KmmConfig m) :
    inputCount C ≤ inputCount (C.erase v) + 1 := by
  unfold inputCount
  have hsub :
      C.filter (fun w : KmmNode m => w.isLeft = true) ⊆
        insert v ((C.erase v).filter (fun w : KmmNode m => w.isLeft = true)) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwC, hwL⟩
    by_cases hEq : w = v
    · exact hEq ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hEq, hwC⟩, hwL⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

private theorem inputCount_erase_inr {m : ℕ} (j : Fin m) (C : KmmConfig m) :
    inputCount (C.erase (Sum.inr j)) = inputCount C := by
  unfold inputCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hvC⟩, hvL⟩
    exact ⟨hvC, hvL⟩
  · rintro ⟨hvC, hvL⟩
    refine ⟨⟨?_, hvC⟩, hvL⟩
    rintro rfl
    simp at hvL

private theorem inputCount_erase_inl_of_mem {m : ℕ} {i : Fin m} {C : KmmConfig m}
    (hmem : Sum.inl i ∈ C) :
    inputCount (C.erase (Sum.inl i)) + 1 = inputCount C := by
  unfold inputCount
  have hfilt :
      (C.erase (Sum.inl i)).filter (fun v : KmmNode m => v.isLeft = true) =
        (C.filter (fun v : KmmNode m => v.isLeft = true)).erase (Sum.inl i) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hfilt]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hmem, rfl⟩)

private theorem outputCount_insert_inl {m : ℕ} (i : Fin m) (C : KmmConfig m) :
    outputCount (insert (Sum.inl i) C) = outputCount C := by
  unfold outputCount
  rw [Finset.filter_insert]
  simp

private theorem outputCount_insert_inr_le {m : ℕ} (j : Fin m) (C : KmmConfig m) :
    outputCount (insert (Sum.inr j) C) ≤ outputCount C + 1 := by
  unfold outputCount
  rw [Finset.filter_insert]
  simp only [Sum.isRight_inr, ↓reduceIte]
  exact Finset.card_insert_le _ _

private theorem outputCount_insert_inr_ge {m : ℕ} (j : Fin m) (C : KmmConfig m) :
    outputCount C ≤ outputCount (insert (Sum.inr j) C) :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))

private theorem outputCount_insert_inr_of_notMem {m : ℕ} {j : Fin m} {C : KmmConfig m}
    (hnot : Sum.inr j ∉ C) :
    outputCount (insert (Sum.inr j) C) = outputCount C + 1 := by
  unfold outputCount
  rw [Finset.filter_insert]
  simp only [Sum.isRight_inr, ↓reduceIte]
  rw [Finset.card_insert_of_notMem]
  intro hmem
  exact hnot (Finset.mem_filter.mp hmem).1

private theorem outputCount_erase_inl {m : ℕ} (i : Fin m) (C : KmmConfig m) :
    outputCount (C.erase (Sum.inl i)) = outputCount C := by
  unfold outputCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hvC⟩, hvR⟩
    exact ⟨hvC, hvR⟩
  · rintro ⟨hvC, hvR⟩
    refine ⟨⟨?_, hvC⟩, hvR⟩
    rintro rfl
    simp at hvR

private theorem outputCount_erase_le {m : ℕ} (v : KmmNode m) (C : KmmConfig m) :
    outputCount (C.erase v) ≤ outputCount C :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v C))

private theorem outputCount_erase_ge {m : ℕ} (v : KmmNode m) (C : KmmConfig m) :
    outputCount C ≤ outputCount (C.erase v) + 1 := by
  unfold outputCount
  have hsub :
      C.filter (fun w : KmmNode m => w.isRight = true) ⊆
        insert v ((C.erase v).filter (fun w : KmmNode m => w.isRight = true)) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwC, hwR⟩
    by_cases hEq : w = v
    · exact hEq ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hEq, hwC⟩, hwR⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- The `CoupledSeparatorSystem` induced by `KmmStep m S` with potentials
`(ψ, ω) = (inputCount, outputCount)`. -/
def kmmCoupledSeparatorSystem (m S : ℕ) : CoupledSeparatorSystem (KmmConfig m) where
  toSeparatorSystem := kmmSeparatorSystem m S
  ω := outputCount
  psi_dec_le_one := by
    intro C₁ C₂ h
    dsimp [kmmSeparatorSystem] at h ⊢
    cases h with
    | placeInput i _ =>
      have := inputCount_insert_inl_ge i C₁
      omega
    | placeOutput j _ _ =>
      rw [inputCount_insert_inr]
      omega
    | slideOutput i j _ _ =>
      rw [inputCount_insert_inr]
      exact inputCount_erase_inl_ge (Sum.inl i) C₁
    | remove v _ =>
      exact inputCount_erase_inl_ge v C₁
    | idle _ =>
      omega
  omega_inc_le_one := by
    intro C₁ C₂ h
    dsimp [kmmSeparatorSystem] at h ⊢
    cases h with
    | placeInput i _ =>
      rw [outputCount_insert_inl]
      omega
    | placeOutput j _ _ =>
      exact outputCount_insert_inr_le j C₁
    | slideOutput i j _ _ =>
      have h1 := outputCount_insert_inr_le j (C₁.erase (Sum.inl i))
      rw [outputCount_erase_inl] at h1
      exact h1
    | remove v _ =>
      exact le_trans (outputCount_erase_le v C₁) (Nat.le_succ _)
    | idle _ =>
      omega
  omega_dec_le_one := by
    intro C₁ C₂ h
    dsimp [kmmSeparatorSystem] at h ⊢
    cases h with
    | placeInput i _ =>
      rw [outputCount_insert_inl]
      omega
    | placeOutput j _ _ =>
      have := outputCount_insert_inr_ge j C₁
      omega
    | slideOutput i j _ _ =>
      have h1 := outputCount_insert_inr_ge j (C₁.erase (Sum.inl i))
      rw [outputCount_erase_inl] at h1
      omega
    | remove v _ =>
      exact outputCount_erase_ge v C₁
    | idle _ =>
      omega
  psi_inc_disjoint_omega_change := by
    intro C₁ C₂ h hlt
    dsimp [kmmSeparatorSystem] at h hlt ⊢
    cases h with
    | placeInput i _ =>
      exact outputCount_insert_inl i C₁
    | placeOutput j _ _ =>
      rw [inputCount_insert_inr] at hlt
      exact absurd hlt (lt_irrefl _)
    | slideOutput i j _ _ =>
      rw [inputCount_insert_inr] at hlt
      have := inputCount_erase_le (Sum.inl i) C₁
      omega
    | remove v _ =>
      have := inputCount_erase_le v C₁
      omega
    | idle _ =>
      exact absurd hlt (lt_irrefl _)
  psi_dec_disjoint_omega_dec := by
    intro C₁ C₂ h hlt
    dsimp [kmmSeparatorSystem] at h hlt ⊢
    cases h with
    | placeInput i _ =>
      have := inputCount_insert_inl_ge i C₁
      omega
    | placeOutput j _ _ =>
      rw [inputCount_insert_inr] at hlt
      exact absurd hlt (lt_irrefl _)
    | slideOutput i j _ _ =>
      have h1 := outputCount_insert_inr_ge j (C₁.erase (Sum.inl i))
      rw [outputCount_erase_inl] at h1
      exact h1
    | remove v _ =>
      rcases v with i | j
      · rw [outputCount_erase_inl]
      · rw [inputCount_erase_inr] at hlt
        exact absurd hlt (lt_irrefl _)
    | idle _ =>
      exact absurd hlt (lt_irrefl _)

private theorem kmm_firstOutStep_spec {m S : ℕ} (P : ValidKmmPebbling m S) (j : Fin m) :
    Sum.inr j ∉ P.trace (firstOutStep P j).castSucc ∧
      Sum.inr j ∈ P.trace (firstOutStep P j).succ := by
  classical
  have hex : ∃ n : ℕ, ∃ hn : n < P.steps + 1, Sum.inr j ∈ P.trace ⟨n, hn⟩ := by
    rcases P.outputs_computed j with ⟨t, ht⟩
    exact ⟨t.1, t.2, ht⟩
  dsimp only [firstOutStep]
  set n := Nat.find hex
  have hspec : ∃ hn : n < P.steps + 1, Sum.inr j ∈ P.trace ⟨n, hn⟩ := Nat.find_spec hex
  rcases hspec with ⟨hn, hmem⟩
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    have h0_eq : (⟨n, hn⟩ : Fin (P.steps + 1)) = 0 := Fin.ext hn0
    rw [h0_eq, P.init_empty] at hmem
    simp at hmem
  have hnot_prev : Sum.inr j ∉ P.trace ⟨n - 1, by omega⟩ := by
    intro hprev
    exact Nat.find_min hex (by omega : n - 1 < n) ⟨by omega, hprev⟩
  refine ⟨hnot_prev, ?_⟩
  convert hmem using 2
  ext
  simp only [Fin.val_succ]
  omega

private theorem kmm_firstOutStep_injective {m S : ℕ} (P : ValidKmmPebbling m S) :
    Function.Injective (firstOutStep P) := by
  intro j₁ j₂ heq
  have h1 := kmm_firstOutStep_spec P j₁
  have h2 := kmm_firstOutStep_spec P j₂
  rw [heq] at h1
  have hnew := kmmStep_new_output (P.valid_step (firstOutStep P j₂)) h2.1 h2.2
  exact hnew.2 j₁ h1.1 h1.2

private theorem kmmStep_outputCount_inc_of_new_output {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (hstep : KmmStep m S C₁ C₂) {j : Fin m}
    (hnot : Sum.inr j ∉ C₁) (hin : Sum.inr j ∈ C₂) :
    outputCount C₁ < outputCount C₂ := by
  cases hstep with
  | placeInput i _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
    · exact absurd hmem hnot
  | placeOutput j₀ _ _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
      rw [outputCount_insert_inr_of_notMem hnot]
      omega
    · exact absurd hmem hnot
  | slideOutput i j₀ _ _ =>
    rcases Finset.mem_insert.mp hin with hEq | hmem
    · cases hEq
      have hnot' : Sum.inr j ∉ C₁.erase (Sum.inl i) :=
        fun h => hnot (Finset.mem_of_mem_erase h)
      rw [outputCount_insert_inr_of_notMem hnot', outputCount_erase_inl]
      omega
    · exact absurd (Finset.mem_of_mem_erase hmem) hnot
  | remove v _ =>
    exact absurd (Finset.mem_of_mem_erase hin) hnot
  | idle _ =>
    exact absurd hin hnot

private theorem kmm_firstOutStep_mem_omegaIncSet {m S : ℕ} (P : ValidKmmPebbling m S) (j : Fin m) :
    firstOutStep P j ∈ omegaIncSet (kmmCoupledSeparatorSystem m S) P.trace := by
  have hspec := kmm_firstOutStep_spec P j
  rw [omegaIncSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    kmmStep_outputCount_inc_of_new_output (P.valid_step (firstOutStep P j)) hspec.1 hspec.2⟩

private theorem kmmStep_slide_crossing {m S : ℕ} {C₁ C₂ : KmmConfig m}
    (hstep : KmmStep m S C₁ C₂)
    (hψ_dec : inputCount C₂ < inputCount C₁)
    (hω_inc : outputCount C₁ < outputCount C₂) :
    m ≤ inputCount C₁ ∧ inputCount C₂ ≤ m - 1 := by
  cases hstep with
  | placeInput i _ =>
    rw [outputCount_insert_inl] at hω_inc
    exact absurd hω_inc (lt_irrefl _)
  | placeOutput j _ _ =>
    rw [inputCount_insert_inr] at hψ_dec
    exact absurd hψ_dec (lt_irrefl _)
  | slideOutput i j hin _ =>
    have hge : m ≤ inputCount C₁ := inputCount_ge_of_inputNodes_subset hin
    have hle : inputCount C₁ ≤ m := inputCount_le_m _
    have hmem : Sum.inl i ∈ C₁ :=
      hin (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have herase := inputCount_erase_inl_of_mem hmem
    rw [inputCount_insert_inr]
    omega
  | remove v _ =>
    have := outputCount_erase_le v C₁
    omega
  | idle _ =>
    exact absurd hω_inc (lt_irrefl _)

private theorem kmm_slideSet_crossing {m S : ℕ} (P : ValidKmmPebbling m S) :
    ∀ t ∈ slideSet (kmmCoupledSeparatorSystem m S) P.trace,
      m ≤ (kmmCoupledSeparatorSystem m S).ψ (P.trace t.castSucc) ∧
        (kmmCoupledSeparatorSystem m S).ψ (P.trace t.succ) ≤ m - 1 := by
  intro t ht
  rw [slideSet, Finset.mem_filter] at ht
  exact kmmStep_slide_crossing (P.valid_step t) ht.2.1 ht.2.2

private theorem kmm_coupled_bounds {m S : ℕ} (hm : 1 ≤ m) (P : ValidKmmPebbling m S) :
    m ≤ inputPlacements P ∧
    2 * m ≤ coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace ∧
    4 * m - 1 ≤ coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace +
      (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card ∧
    ∀ s : ℕ, 1 ≤ s → s ≤ (slideSet (kmmCoupledSeparatorSystem m S) P.trace).card →
      m + (s - 1) ≤ inputPlacements P ∧
      4 * m + s - 2 ≤ coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace +
        (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card := by
  have hreach : ∃ t : Fin (P.steps + 1),
      m ≤ (kmmCoupledSeparatorSystem m S).ψ (P.trace t) := by
    let j0 : Fin m := ⟨0, hm⟩
    refine ⟨(firstOutStep P j0).castSucc, ?_⟩
    have hspec := kmm_firstOutStep_spec P j0
    have hnew := kmmStep_new_output (P.valid_step (firstOutStep P j0)) hspec.1 hspec.2
    exact inputCount_ge_of_inputNodes_subset hnew.1
  have hk : m ≤ (omegaIncSet (kmmCoupledSeparatorSystem m S) P.trace).card := by
    have hsub : Finset.univ.image (firstOutStep P) ⊆
        omegaIncSet (kmmCoupledSeparatorSystem m S) P.trace := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨j, _, rfl⟩
      exact kmm_firstOutStep_mem_omegaIncSet P j
    calc m = (Finset.univ.image (firstOutStep P)).card := by
            rw [Finset.card_image_of_injective _ (kmm_firstOutStep_injective P),
              Finset.card_univ, Fintype.card_fin]
      _ ≤ (omegaIncSet (kmmCoupledSeparatorSystem m S) P.trace).card := Finset.card_le_card hsub
  have hinit_psi : (kmmCoupledSeparatorSystem m S).ψ (P.trace 0) = 0 := by
    simp [kmmCoupledSeparatorSystem, kmmSeparatorSystem, P.init_empty, inputCount]
  have hinit_omega : (kmmCoupledSeparatorSystem m S).ω (P.trace 0) = 0 := by
    simp [kmmCoupledSeparatorSystem, P.init_empty, outputCount]
  have hrec_ge_m : m ≤ inputPlacements P := by
    rcases hreach with ⟨t, ht⟩
    have hdiff := recoverySteps_ge_potential_diff (kmmSeparatorSystem m S) P.trace P.valid_step
      (Nat.zero_le t.1) (Nat.le_of_lt_succ t.2)
    have htr0 : P.trace ⟨0, Nat.lt_succ_of_le ((Nat.zero_le t.1).trans (Nat.le_of_lt_succ t.2))⟩ =
        P.trace 0 := rfl
    have htrt : P.trace ⟨t.1, Nat.lt_succ_of_le (Nat.le_of_lt_succ t.2)⟩ = P.trace t := rfl
    rw [htr0, htrt] at hdiff
    have h0 : (kmmSeparatorSystem m S).ψ (P.trace 0) = 0 := hinit_psi
    rw [h0] at hdiff
    have hsub : (recoverySet (kmmSeparatorSystem m S) P.trace ∩
        stepInterval P.steps 0 t.1).card ≤ inputPlacements P :=
      Finset.card_le_card Finset.inter_subset_left
    change m ≤ (kmmSeparatorSystem m S).ψ (P.trace t) at ht
    omega
  have hmain := coupledSeparatorLowerBound (kmmCoupledSeparatorSystem m S) P.trace P.valid_step
    hm hinit_psi hinit_omega hreach hk (kmm_slideSet_crossing P)
  have hcard_end :
      (kmmCoupledSeparatorSystem m S).ψ (P.trace ⟨P.steps, Nat.lt_succ_self _⟩) +
        (kmmCoupledSeparatorSystem m S).ω (P.trace ⟨P.steps, Nat.lt_succ_self _⟩) =
      (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card :=
    inputCount_add_outputCount _
  refine ⟨hrec_ge_m, by omega, by omega, ?_⟩
  intro s hs1 hs2
  have h3 := hmain.2.2 s hs1 hs2
  exact ⟨h3.1, by omega⟩

private theorem kmm_slideSet_ge_m_at_S_eq_m {m : ℕ} (P : ValidKmmPebbling m m) :
    m ≤ (slideSet (kmmCoupledSeparatorSystem m m) P.trace).card := by
  have hsub : Finset.univ.image (firstOutStep P) ⊆
      slideSet (kmmCoupledSeparatorSystem m m) P.trace := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨j, _, rfl⟩
    have hspec := kmm_firstOutStep_spec P j
    have hω := kmm_firstOutStep_mem_omegaIncSet P j
    have hnew := kmmStep_new_output (P.valid_step (firstOutStep P j)) hspec.1 hspec.2
    have hge : m ≤ inputCount (P.trace (firstOutStep P j).castSucc) :=
      inputCount_ge_of_inputNodes_subset hnew.1
    have hle : inputCount (P.trace (firstOutStep P j).succ) ≤ m - 1 :=
      inputCount_le_sub_one_of_inr_mem hspec.2 (P.space_le _)
    have hm_pos : 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) j.2)
    rw [omegaIncSet, Finset.mem_filter] at hω
    rw [slideSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hω.2⟩
    change inputCount (P.trace (firstOutStep P j).succ) <
      inputCount (P.trace (firstOutStep P j).castSucc)
    omega
  calc m = (Finset.univ.image (firstOutStep P)).card := by
          rw [Finset.card_image_of_injective _ (kmm_firstOutStep_injective P),
            Finset.card_univ, Fintype.card_fin]
    _ ≤ (slideSet (kmmCoupledSeparatorSystem m m) P.trace).card := Finset.card_le_card hsub

/-- **Exact VisitAll Lower Bound on `K_{m, m}`**:
* At `S = m`: `2 * m - 1 ≤ inputPlacements P` and `4 * m - 2 ≤ activeSteps P.trace ≤ P.steps`.
* At `m < S`: `m ≤ inputPlacements P` and
  `max (2 * m) (4 * m - 1 - S) ≤ activeSteps P.trace ≤ P.steps`. -/
theorem k_mm_visitAll_exact_lower_bound {m S : ℕ} (hm : 1 ≤ m) (_hS : m ≤ S)
    (P : ValidKmmPebbling m S) :
    (S = m → 2 * m - 1 ≤ inputPlacements P ∧
      4 * m - 2 ≤ activeSteps P.trace ∧ 4 * m - 2 ≤ P.steps) ∧
    (m < S → m ≤ inputPlacements P ∧
      max (2 * m) (4 * m - 1 - S) ≤ activeSteps P.trace ∧
      max (2 * m) (4 * m - 1 - S) ≤ P.steps) := by
  have hact_le : coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace ≤
      activeSteps P.trace := coupledActiveSteps_le_activeSteps _ _
  have hsteps_le : activeSteps P.trace ≤ P.steps := activeSteps_le_steps P.trace
  have hend_le : (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card ≤ S := P.space_le _
  have hcb := kmm_coupled_bounds hm P
  constructor
  · intro hEq
    subst S
    have hsl := kmm_slideSet_ge_m_at_S_eq_m P
    have h3 := hcb.2.2.2 m hm hsl
    exact ⟨by omega, by omega, by omega⟩
  · intro _hlt
    refine ⟨hcb.1, ?_, ?_⟩
    · exact max_le (by omega) (by omega)
    · exact le_trans (max_le (by omega) (by omega)) hsteps_le

/-- **Exact VisitAllClean Lower Bound on `K_{m, m}`**:
When the final configuration is empty (`C_T = ∅`):
* At `S = m`: `2 * m - 1 ≤ inputPlacements P` and `5 * m - 2 ≤ activeSteps P.trace ≤ P.steps`.
* At `m < S`: `m ≤ inputPlacements P` and `4 * m - 1 ≤ activeSteps P.trace ≤ P.steps`. -/
theorem k_mm_visitAllClean_exact_lower_bound {m S : ℕ} (hm : 1 ≤ m) (_hS : m ≤ S)
    (P : ValidKmmPebbling m S)
    (hclean : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = ∅) :
    (S = m → 2 * m - 1 ≤ inputPlacements P ∧
      5 * m - 2 ≤ activeSteps P.trace ∧ 5 * m - 2 ≤ P.steps) ∧
    (m < S → m ≤ inputPlacements P ∧
      4 * m - 1 ≤ activeSteps P.trace ∧ 4 * m - 1 ≤ P.steps) := by
  have hact_le : coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace ≤
      activeSteps P.trace := coupledActiveSteps_le_activeSteps _ _
  have hsteps_le : activeSteps P.trace ≤ P.steps := activeSteps_le_steps P.trace
  have hend : (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card = 0 := by simp [hclean]
  have hcb := kmm_coupled_bounds hm P
  constructor
  · intro hEq
    subst S
    have hsl := kmm_slideSet_ge_m_at_S_eq_m P
    have h3 := hcb.2.2.2 m hm hsl
    exact ⟨by omega, by omega, by omega⟩
  · intro _hlt
    exact ⟨hcb.1, by omega, by omega⟩

/-- The last step `t : Fin P.steps` at which output `j` is newly placed when `Sum.inr j` is
present in the final configuration `P.trace ⟨P.steps, _⟩`. -/
private def lastOutStep {m S : ℕ} (P : ValidKmmPebbling m S)
    (hcoexist : outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩) (j : Fin m) : Fin P.steps :=
  let A : Finset (Fin (P.steps + 1)) :=
    Finset.univ.filter (fun t : Fin (P.steps + 1) => Sum.inr j ∉ P.trace t)
  have hne : A.Nonempty := ⟨0, by simp [A, P.init_empty]⟩
  let a := A.max' hne
  have ha_mem : a ∈ A := Finset.max'_mem A hne
  have ha_not : Sum.inr j ∉ P.trace a := (Finset.mem_filter.mp ha_mem).2
  have hj_end : Sum.inr j ∈ P.trace ⟨P.steps, Nat.lt_succ_self _⟩ :=
    hcoexist (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have ha_lt : a.1 < P.steps := by
    by_contra hge
    have ha_le : a.1 ≤ P.steps := Nat.le_of_lt_succ a.2
    have heq : a = ⟨P.steps, Nat.lt_succ_self _⟩ := Fin.ext (by show a.1 = P.steps; omega)
    rw [heq] at ha_not
    exact ha_not hj_end
  ⟨a.1, ha_lt⟩

private theorem lastOutStep_spec {m S : ℕ} (P : ValidKmmPebbling m S)
    (hcoexist : outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩) (j : Fin m) :
    Sum.inr j ∉ P.trace (lastOutStep P hcoexist j).castSucc ∧
      ∀ s : Fin (P.steps + 1), (lastOutStep P hcoexist j).succ ≤ s → Sum.inr j ∈ P.trace s := by
  dsimp only [lastOutStep]
  set A : Finset (Fin (P.steps + 1)) :=
    Finset.univ.filter (fun t : Fin (P.steps + 1) => Sum.inr j ∉ P.trace t)
  have hne : A.Nonempty := ⟨0, by simp [A, P.init_empty]⟩
  set a := A.max' hne
  have ha_not : Sum.inr j ∉ P.trace a := (Finset.mem_filter.mp (Finset.max'_mem A hne)).2
  refine ⟨ha_not, ?_⟩
  intro s hs
  by_contra hnot
  have hsA : s ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
  have hs_le : s ≤ a := Finset.le_max' A s hsA
  have : a.1 + 1 ≤ s.1 := hs
  have : s.1 ≤ a.1 := hs_le
  omega

private theorem lastOutStep_injective {m S : ℕ} (P : ValidKmmPebbling m S)
    (hcoexist : outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩) :
    Function.Injective (lastOutStep P hcoexist) := by
  intro j₁ j₂ heq
  have h1 := lastOutStep_spec P hcoexist j₁
  have h2 := lastOutStep_spec P hcoexist j₂
  rw [heq] at h1
  have hnew := kmmStep_new_output (P.valid_step (lastOutStep P hcoexist j₂))
    h2.1 (h2.2 _ le_rfl)
  exact hnew.2 j₁ h1.1 (h1.2 _ le_rfl)

/-- **CoexistAll Infeasibility Below `2 * m - 1` Pebbles**:
If `1 ≤ m` and `S < 2 * m - 1`, no valid pebbling of `K_{m, m}` with `S` pebbles can terminate
with all `m` outputs simultaneously pebbled. -/
theorem k_mm_coexistAll_infeasible {m S : ℕ} (hm : 1 ≤ m) (hS : S < 2 * m - 1) :
    ¬ ∃ P : ValidKmmPebbling m S, outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩ := by
  rintro ⟨P, hcoexist⟩
  let f : Fin m → Fin P.steps := lastOutStep P hcoexist
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨j_max, _, hj_max⟩ := Finset.exists_max_image Finset.univ f hne
  let t_max : Fin P.steps := f j_max
  let C : KmmConfig m := P.trace t_max.castSucc
  have hspec_max := lastOutStep_spec P hcoexist j_max
  have hnew_max := kmmStep_new_output (P.valid_step t_max) hspec_max.1 (hspec_max.2 _ le_rfl)
  have hin_sub : inputNodes m ⊆ C := hnew_max.1
  let otherOuts : KmmConfig m := (outputNodes m).erase (Sum.inr j_max)
  have hout_sub : otherOuts ⊆ C := by
    intro v hv
    rcases Finset.mem_erase.mp hv with ⟨hne_v, hv_out⟩
    rcases Finset.mem_image.mp hv_out with ⟨j, _, rfl⟩
    have hj_ne : j ≠ j_max := fun h => hne_v (congrArg Sum.inr h)
    have hle : f j ≤ f j_max := hj_max j (Finset.mem_univ _)
    have hne_f : f j ≠ f j_max := fun h => hj_ne (lastOutStep_injective P hcoexist h)
    have hlt : f j < t_max := lt_of_le_of_ne hle hne_f
    have hsucc_le : (f j).succ ≤ t_max.castSucc := by
      show (f j).1 + 1 ≤ t_max.1
      have : (f j).1 < t_max.1 := hlt
      omega
    exact (lastOutStep_spec P hcoexist j).2 t_max.castSucc hsucc_le
  have hdisj : Disjoint (inputNodes m) otherOuts := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rcases Finset.mem_image.mp hv1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hv2) with ⟨j, _, hEq⟩
    cases hEq
  have hcard_other : otherOuts.card = m - 1 := by
    have hmem : Sum.inr j_max ∈ outputNodes m :=
      Finset.mem_image.mpr ⟨j_max, Finset.mem_univ _, rfl⟩
    have h := Finset.card_erase_add_one hmem
    rw [card_outputNodes] at h
    dsimp only [otherOuts]
    omega
  have hcard_le : m + (m - 1) ≤ C.card := by
    calc m + (m - 1)
        = (inputNodes m).card + otherOuts.card := by rw [card_inputNodes, hcard_other]
      _ = (inputNodes m ∪ otherOuts).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ C.card := Finset.card_le_card (Finset.union_subset hin_sub hout_sub)
  have hC_le : C.card ≤ S := P.space_le t_max.castSucc
  omega

/-- **Exact CoexistAll Lower Bound on `K_{m, m}`**:
Any valid pebbling ending with all `m` outputs pebbled uses at least `m` input placements and at
least `2 * m` active steps. -/
theorem k_mm_coexistAll_exact_lower_bound {m S : ℕ} (hm : 1 ≤ m)
    (P : ValidKmmPebbling m S)
    (_hcoexist : outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩) :
    m ≤ inputPlacements P ∧ 2 * m ≤ activeSteps P.trace ∧ 2 * m ≤ P.steps := by
  have hact_le : coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace ≤
      activeSteps P.trace := coupledActiveSteps_le_activeSteps _ _
  have hsteps_le : activeSteps P.trace ≤ P.steps := activeSteps_le_steps P.trace
  have hcb := kmm_coupled_bounds hm P
  exact ⟨hcb.1, by omega, by omega⟩

/-- **Exact CoexistAllClean Lower Bound on `K_{m, m}`**:
Any valid pebbling ending with configuration exactly `outputNodes m` uses at least `m` input
placements and at least `3 * m - 1` active steps. -/
theorem k_mm_coexistAllClean_exact_lower_bound {m S : ℕ} (hm : 1 ≤ m)
    (P : ValidKmmPebbling m S)
    (hclean : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = outputNodes m) :
    m ≤ inputPlacements P ∧ 3 * m - 1 ≤ activeSteps P.trace ∧ 3 * m - 1 ≤ P.steps := by
  have hact_le : coupledActiveSteps (kmmCoupledSeparatorSystem m S) P.trace ≤
      activeSteps P.trace := coupledActiveSteps_le_activeSteps _ _
  have hsteps_le : activeSteps P.trace ≤ P.steps := activeSteps_le_steps P.trace
  have hend : (P.trace ⟨P.steps, Nat.lt_succ_self _⟩).card = m := by
    rw [hclean, card_outputNodes]
  have hcb := kmm_coupled_bounds hm P
  exact ⟨hcb.1, by omega, by omega⟩

/-! ### Part 3: Constructive Exact Optimal Upper Bounds Matching Every Regime -/

private theorem kmmStep_weaken {m S₁ S₂ : ℕ} (hS : S₁ ≤ S₂) {C₁ C₂ : KmmConfig m}
    (h : KmmStep m S₁ C₁ C₂) : KmmStep m S₂ C₁ C₂ := by
  cases h with
  | placeInput i hcard => exact KmmStep.placeInput i (lt_of_lt_of_le hcard hS)
  | placeOutput j hin hcard => exact KmmStep.placeOutput j hin (lt_of_lt_of_le hcard hS)
  | slideOutput i j hin hcard => exact KmmStep.slideOutput i j hin (le_trans hcard hS)
  | remove v hcard => exact KmmStep.remove v (le_trans hcard hS)
  | idle hcard => exact KmmStep.idle (le_trans hcard hS)

private def weakenPebbling {m S₁ S₂ : ℕ} (hS : S₁ ≤ S₂) (P : ValidKmmPebbling m S₁) :
    ValidKmmPebbling m S₂ where
  steps := P.steps
  trace := P.trace
  init_empty := P.init_empty
  space_le := fun t => le_trans (P.space_le t) hS
  valid_step := fun t => kmmStep_weaken hS (P.valid_step t)
  outputs_computed := P.outputs_computed

private theorem inputPlacements_weakenPebbling {m S₁ S₂ : ℕ} (hS : S₁ ≤ S₂)
    (P : ValidKmmPebbling m S₁) :
    inputPlacements (weakenPebbling hS P) = inputPlacements P := rfl

/-- The suffix of input vertices `{u_k, ..., u_{m-1}}`. -/
private def suffixInputs (m k : ℕ) : KmmConfig m :=
  (Finset.univ.filter (fun i : Fin m => k ≤ i.1)).image Sum.inl

private theorem suffixInputs_ge (m k : ℕ) (hk : m ≤ k) : suffixInputs m k = ∅ := by
  ext v
  simp only [suffixInputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_exists, not_and]
  intro i hi _
  omega

private theorem suffixInputs_one (m : ℕ) (hm : 1 ≤ m) :
    suffixInputs m 1 = (inputNodes m).erase (Sum.inl ⟨0, hm⟩) := by
  ext v
  simp only [suffixInputs, inputNodes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, ⟨i, rfl⟩⟩
    intro hEq
    have := Fin.ext_iff.mp (Sum.inl.inj hEq)
    simp at this
    omega
  · rintro ⟨hne, ⟨i, rfl⟩⟩
    refine ⟨i, ?_, rfl⟩
    by_contra hlt
    have hi0 : i = ⟨0, hm⟩ := Fin.ext (by simp; omega)
    exact hne (congrArg Sum.inl hi0)

private theorem suffixInputs_succ {m k : ℕ} (hk : k < m) :
    suffixInputs m (k + 1) = (suffixInputs m k).erase (Sum.inl ⟨k, hk⟩) := by
  ext v
  simp only [suffixInputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, ⟨i, by omega, rfl⟩⟩
    intro hEq
    have := Fin.ext_iff.mp (Sum.inl.inj hEq)
    simp at this
    omega
  · rintro ⟨hne, ⟨i, hi, rfl⟩⟩
    refine ⟨i, ?_, rfl⟩
    by_contra hlt
    have hik : i = ⟨k, hk⟩ := Fin.ext (by simp; omega)
    exact hne (congrArg Sum.inl hik)

private theorem card_suffixInputs {m k : ℕ} (hk : k ≤ m) :
    (suffixInputs m k).card = m - k := by
  have h : ∀ d : ℕ, d ≤ m → (suffixInputs m (m - d)).card = d := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [suffixInputs_ge]
    | succ d ih =>
      intro hd
      have hlt : m - (d + 1) < m := by omega
      have hsucc := suffixInputs_succ hlt
      have heq : m - (d + 1) + 1 = m - d := by omega
      rw [heq] at hsucc
      have hmem : Sum.inl ⟨m - (d + 1), hlt⟩ ∈ suffixInputs m (m - (d + 1)) :=
        Finset.mem_image.mpr ⟨⟨m - (d + 1), hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩
      have hcard := Finset.card_erase_add_one hmem
      rw [← hsucc, ih (by omega)] at hcard
      omega
  have := h (m - k) (Nat.sub_le m k)
  have heq : m - (m - k) = k := by omega
  rw [heq] at this
  exact this

private theorem inputCount_suffixInputs {m k : ℕ} (hk : k ≤ m) :
    inputCount (suffixInputs m k) = m - k := by
  have hfilt : (suffixInputs m k).filter (fun v : KmmNode m => v.isLeft = true) =
      suffixInputs m k := by
    rw [Finset.filter_eq_self]
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    rfl
  rw [inputCount, hfilt, card_suffixInputs hk]

private theorem prefixInputs_zero' (m : ℕ) : prefixInputs m 0 = ∅ := by
  simp [prefixInputs]

private theorem prefixInputs_eq_inputNodes' (m : ℕ) : prefixInputs m m = inputNodes m := by
  ext v
  simp [prefixInputs, inputNodes]

private theorem prefixInputs_succ' {m k : ℕ} (hk : k < m) :
    prefixInputs m (k + 1) = insert (Sum.inl ⟨k, hk⟩) (prefixInputs m k) := by
  ext v
  simp only [prefixInputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases heq : i.1 = k
    · left; exact congrArg Sum.inl (Fin.ext heq)
    · right; exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, by omega, rfl⟩

private theorem card_prefixInputs' {m k : ℕ} (hk : k ≤ m) : (prefixInputs m k).card = k := by
  induction k with
  | zero => simp [prefixInputs_zero']
  | succ k ih =>
    have hk' : k < m := by omega
    have hnot : Sum.inl ⟨k, hk'⟩ ∉ prefixInputs m k := by simp [prefixInputs]
    rw [prefixInputs_succ' hk', Finset.card_insert_of_notMem hnot, ih (Nat.le_of_lt hk')]

private theorem inputCount_prefixInputs' {m k : ℕ} (hk : k ≤ m) :
    inputCount (prefixInputs m k) = k := by
  have hfilt : (prefixInputs m k).filter (fun v : KmmNode m => v.isLeft = true) =
      prefixInputs m k := by
    rw [Finset.filter_eq_self]
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    rfl
  rw [inputCount, hfilt, card_prefixInputs' hk]

private theorem inputCount_inputNodes' (m : ℕ) : inputCount (inputNodes m) = m := by
  rw [← prefixInputs_eq_inputNodes']
  exact inputCount_prefixInputs' le_rfl

/-- Concatenate two valid traces sharing the junction configuration `tr₁ T₁ = tr₂ 0`. -/
private def appendTrace {Q : Type*} {T₁ T₂ : ℕ}
    (tr₁ : Fin (T₁ + 1) → Q) (tr₂ : Fin (T₂ + 1) → Q) : Fin (T₁ + T₂ + 1) → Q :=
  fun t =>
    if h : t.1 ≤ T₁ then
      tr₁ ⟨t.1, by omega⟩
    else
      tr₂ ⟨t.1 - T₁, by omega⟩

private theorem appendTrace_zero {Q : Type*} {T₁ T₂ : ℕ}
    (tr₁ : Fin (T₁ + 1) → Q) (tr₂ : Fin (T₂ + 1) → Q) :
    appendTrace tr₁ tr₂ 0 = tr₁ 0 := by
  simp [appendTrace]

private theorem appendTrace_last {Q : Type*} {T₁ T₂ : ℕ}
    (tr₁ : Fin (T₁ + 1) → Q) (tr₂ : Fin (T₂ + 1) → Q)
    (hjoin : tr₁ ⟨T₁, Nat.lt_succ_self _⟩ = tr₂ 0) :
    appendTrace tr₁ tr₂ ⟨T₁ + T₂, Nat.lt_succ_self _⟩ = tr₂ ⟨T₂, Nat.lt_succ_self _⟩ := by
  dsimp only [appendTrace]
  by_cases h : T₁ + T₂ ≤ T₁
  · have hT₂ : T₂ = 0 := by omega
    subst hT₂
    simp only [Nat.add_zero, le_rfl, ↓reduceDIte]
    exact hjoin
  · simp only [h, ↓reduceDIte]
    congr 1
    ext
    simp

/-- Append a non-increasing-`inputCount` tail trace to a `ValidKmmPebbling`, preserving
`inputPlacements` and setting the final configuration to the end of the tail. -/
private def appendTailPebbling {m S T₂ : ℕ} (P : ValidKmmPebbling m S)
    (tr₂ : Fin (T₂ + 1) → KmmConfig m)
    (hjoin : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = tr₂ 0)
    (hspace₂ : ∀ t : Fin (T₂ + 1), (tr₂ t).card ≤ S)
    (hstep₂ : ∀ t : Fin T₂, KmmStep m S (tr₂ t.castSucc) (tr₂ t.succ)) :
    ValidKmmPebbling m S where
  steps := P.steps + T₂
  trace := appendTrace P.trace tr₂
  init_empty := by
    rw [appendTrace_zero]
    exact P.init_empty
  space_le := by
    intro t
    dsimp only [appendTrace]
    split_ifs
    · exact P.space_le _
    · exact hspace₂ _
  valid_step := by
    intro t
    by_cases hlt : t.1 < P.steps
    · have h1 : appendTrace P.trace tr₂ t.castSucc = P.trace ⟨t.1, by omega⟩ := by
        dsimp only [appendTrace]
        have hle : t.castSucc.1 ≤ P.steps := by simp; omega
        simp only [hle, ↓reduceDIte]
        rfl
      have h2 : appendTrace P.trace tr₂ t.succ = P.trace ⟨t.1 + 1, by omega⟩ := by
        dsimp only [appendTrace]
        have hle : t.succ.1 ≤ P.steps := by simp; omega
        simp only [hle, ↓reduceDIte]
        rfl
      rw [h1, h2]
      exact P.valid_step ⟨t.1, hlt⟩
    · have h1 : appendTrace P.trace tr₂ t.castSucc = tr₂ ⟨t.1 - P.steps, by omega⟩ := by
        dsimp only [appendTrace]
        by_cases heq : t.1 = P.steps
        · have hle : t.castSucc.1 ≤ P.steps := by simp; omega
          simp only [hle, ↓reduceDIte]
          have hfin : (⟨t.castSucc.1, by simp; omega⟩ : Fin (P.steps + 1)) =
              ⟨P.steps, Nat.lt_succ_self _⟩ := Fin.ext (by simp [heq])
          rw [hfin, hjoin]
          congr 1
          ext
          simp [heq]
        · have hgt : ¬ t.castSucc.1 ≤ P.steps := by simp; omega
          simp only [hgt, ↓reduceDIte]
          rfl
      have h2 : appendTrace P.trace tr₂ t.succ = tr₂ ⟨t.1 - P.steps + 1, by omega⟩ := by
        dsimp only [appendTrace]
        have hgt : ¬ t.succ.1 ≤ P.steps := by simp; omega
        simp only [hgt, ↓reduceDIte]
        congr 1
        ext
        simp only [Fin.val_succ]
        omega
      rw [h1, h2]
      exact hstep₂ ⟨t.1 - P.steps, by omega⟩
  outputs_computed := by
    intro j
    rcases P.outputs_computed j with ⟨t, ht⟩
    refine ⟨⟨t.1, by omega⟩, ?_⟩
    dsimp only [appendTrace]
    have hle : t.1 ≤ P.steps := Nat.le_of_lt_succ t.2
    simp only [hle, ↓reduceDIte]
    exact ht

private theorem inputPlacements_appendTailPebbling {m S T₂ : ℕ} (P : ValidKmmPebbling m S)
    (tr₂ : Fin (T₂ + 1) → KmmConfig m)
    (hjoin : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = tr₂ 0)
    (hspace₂ : ∀ t : Fin (T₂ + 1), (tr₂ t).card ≤ S)
    (hstep₂ : ∀ t : Fin T₂, KmmStep m S (tr₂ t.castSucc) (tr₂ t.succ))
    (hnoninc : ∀ t : Fin T₂, inputCount (tr₂ t.succ) ≤ inputCount (tr₂ t.castSucc)) :
    inputPlacements (appendTailPebbling P tr₂ hjoin hspace₂ hstep₂) = inputPlacements P := by
  let f : Fin P.steps → Fin (P.steps + T₂) := fun t => ⟨t.1, by omega⟩
  have hfinj : Function.Injective f := fun a b h => Fin.ext (by simpa [f] using congrArg Fin.val h)
  have himg :
      recoverySet (kmmSeparatorSystem m S) (appendTrace P.trace tr₂) =
        (recoverySet (kmmSeparatorSystem m S) P.trace).image f := by
    ext t
    simp only [recoverySet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, f]
    dsimp only [kmmSeparatorSystem]
    constructor
    · intro hlt
      by_cases ht : t.1 < P.steps
      · refine ⟨⟨t.1, ht⟩, ?_, Fin.ext rfl⟩
        have h1 : appendTrace P.trace tr₂ t.castSucc = P.trace ⟨t.1, by omega⟩ := by
          dsimp only [appendTrace]
          have hle : t.castSucc.1 ≤ P.steps := by simp; omega
          simp only [hle, ↓reduceDIte]; rfl
        have h2 : appendTrace P.trace tr₂ t.succ = P.trace ⟨t.1 + 1, by omega⟩ := by
          dsimp only [appendTrace]
          have hle : t.succ.1 ≤ P.steps := by simp; omega
          simp only [hle, ↓reduceDIte]; rfl
        rw [h1, h2] at hlt
        exact hlt
      · exfalso
        have h1 : appendTrace P.trace tr₂ t.castSucc = tr₂ ⟨t.1 - P.steps, by omega⟩ := by
          dsimp only [appendTrace]
          by_cases heq : t.1 = P.steps
          · have hle : t.castSucc.1 ≤ P.steps := by simp; omega
            simp only [hle, ↓reduceDIte]
            have hfin : (⟨t.castSucc.1, by simp; omega⟩ : Fin (P.steps + 1)) =
                ⟨P.steps, Nat.lt_succ_self _⟩ := Fin.ext (by simp [heq])
            rw [hfin, hjoin]; congr 1; ext; simp [heq]
          · have hgt : ¬ t.castSucc.1 ≤ P.steps := by simp; omega
            simp only [hgt, ↓reduceDIte]; rfl
        have h2 : appendTrace P.trace tr₂ t.succ = tr₂ ⟨t.1 - P.steps + 1, by omega⟩ := by
          dsimp only [appendTrace]
          have hgt : ¬ t.succ.1 ≤ P.steps := by simp; omega
          simp only [hgt, ↓reduceDIte]
          congr 1; ext; simp only [Fin.val_succ]; omega
        rw [h1, h2] at hlt
        have hni := hnoninc ⟨t.1 - P.steps, by omega⟩
        change inputCount (tr₂ ⟨t.1 - P.steps + 1, _⟩) ≤ inputCount (tr₂ ⟨t.1 - P.steps, _⟩) at hni
        omega
    · rintro ⟨s, hs, rfl⟩
      have h1 : appendTrace P.trace tr₂ (⟨s.1, by omega⟩ : Fin (P.steps + T₂)).castSucc =
          P.trace s.castSucc := by
        dsimp only [appendTrace]
        have hle : (⟨s.1, by omega⟩ : Fin (P.steps + T₂)).castSucc.1 ≤ P.steps :=
          Nat.le_of_lt s.2
        simp only [hle, ↓reduceDIte]; rfl
      have h2 : appendTrace P.trace tr₂ (⟨s.1, by omega⟩ : Fin (P.steps + T₂)).succ =
          P.trace s.succ := by
        dsimp only [appendTrace]
        have hle : (⟨s.1, by omega⟩ : Fin (P.steps + T₂)).succ.1 ≤ P.steps := s.2
        simp only [hle, ↓reduceDIte]; rfl
      rw [h1, h2]
      exact hs
  change (recoverySet (kmmSeparatorSystem m S) (appendTrace P.trace tr₂)).card =
    (recoverySet (kmmSeparatorSystem m S) P.trace).card
  rw [himg, Finset.card_image_of_injective _ hfinj]

/-- Cleanup tail of length `m`: from `insert (Sum.inr ⟨m - 1, _⟩) (suffixInputs m 1)` down to `∅`
by removing `v_{m-1}` and then `u_1, ..., u_{m-1}`. -/
private def cleanupToEmptyTrace (m : ℕ) (hm : 1 ≤ m) : Fin (m + 1) → KmmConfig m :=
  fun k =>
    if k.1 = 0 then
      insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)
    else
      suffixInputs m k.1

private theorem cleanupToEmpty_space {m S : ℕ} (hm : 1 ≤ m) (hS : m ≤ S)
    (k : Fin (m + 1)) : (cleanupToEmptyTrace m hm k).card ≤ S := by
  dsimp only [cleanupToEmptyTrace]
  split_ifs with h0
  · have hins := Finset.card_insert_le (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)
    rw [card_suffixInputs hm] at hins
    omega
  · rw [card_suffixInputs (Nat.le_of_lt_succ k.2)]
    omega

private theorem cleanupToEmpty_step {m S : ℕ} (hm : 1 ≤ m) (hS : m ≤ S)
    (k : Fin m) :
    KmmStep m S (cleanupToEmptyTrace m hm k.castSucc) (cleanupToEmptyTrace m hm k.succ) := by
  by_cases h0 : k.1 = 0
  · have h1 : cleanupToEmptyTrace m hm k.castSucc =
        insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1) := by
      simp [cleanupToEmptyTrace, h0]
    have h2 : cleanupToEmptyTrace m hm k.succ = suffixInputs m 1 := by
      dsimp only [cleanupToEmptyTrace]
      simp [h0]
    have hnot : Sum.inr ⟨m - 1, by omega⟩ ∉ suffixInputs m 1 := by simp [suffixInputs]
    have herase : (insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)).erase
        (Sum.inr ⟨m - 1, by omega⟩) = suffixInputs m 1 := Finset.erase_insert hnot
    have hcard : (insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)).card ≤ S := by
      rw [← h1]; exact cleanupToEmpty_space hm hS k.castSucc
    rw [h1, h2]
    simpa [herase] using KmmStep.remove (Sum.inr ⟨m - 1, by omega⟩) hcard
  · have h1 : cleanupToEmptyTrace m hm k.castSucc = suffixInputs m k.1 := by
      dsimp only [cleanupToEmptyTrace]
      simp only [Fin.val_castSucc, h0, ↓reduceIte]
    have h2 : cleanupToEmptyTrace m hm k.succ =
        (suffixInputs m k.1).erase (Sum.inl k) := by
      dsimp only [cleanupToEmptyTrace]
      simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte]
      simpa using suffixInputs_succ k.2
    have hcard : (suffixInputs m k.1).card ≤ S := by
      rw [← h1]; exact cleanupToEmpty_space hm hS k.castSucc
    rw [h1, h2]
    exact KmmStep.remove (Sum.inl k) hcard

private theorem cleanupToEmpty_noninc {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    inputCount (cleanupToEmptyTrace m hm k.succ) ≤
      inputCount (cleanupToEmptyTrace m hm k.castSucc) := by
  dsimp only [cleanupToEmptyTrace]
  by_cases h0 : k.1 = 0
  · simp [h0, inputCount_insert_inr]
  · simp only [Fin.val_castSucc, Fin.val_succ, h0, Nat.succ_ne_zero, ↓reduceIte]
    rw [inputCount_suffixInputs (Nat.le_of_lt k.2), inputCount_suffixInputs k.2]
    omega

/-- Optimal VisitAll pebbling at `S = m`: `4 * m - 2` steps, `2 * m - 1` input placements, ending
at `insert (Sum.inr ⟨m - 1, _⟩) (suffixInputs m 1)`. -/
private def visitAllAtM (m : ℕ) (hm : 1 ≤ m) :
    { P : ValidKmmPebbling m m //
      inputPlacements P = 2 * m - 1 ∧ P.steps = 4 * m - 2 ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ =
        insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1) } := by
  let T := 4 * m - 2
  let tr : Fin (T + 1) → KmmConfig m := fun t =>
    if hle : t.1 ≤ m then
      prefixInputs m t.1
    else if h0 : (t.1 - m - 1) % 3 = 0 then
      insert (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) (suffixInputs m 1)
    else if h1 : (t.1 - m - 1) % 3 = 1 then
      suffixInputs m 1
    else
      inputNodes m
  have hspace : ∀ t : Fin (T + 1), (tr t).card ≤ m := by
    intro t
    dsimp only [tr]
    split_ifs with hle h0 h1
    · rw [card_prefixInputs' hle]; omega
    · have hins := Finset.card_insert_le (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) (suffixInputs m 1)
      rw [card_suffixInputs hm] at hins; omega
    · rw [card_suffixInputs hm]; omega
    · rw [card_inputNodes]
  have hstep : ∀ t : Fin T, KmmStep m m (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInputs m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = insert (Sum.inl ⟨t.1, hlt⟩) (prefixInputs m t.1) := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInputs_succ' hlt
      rw [h1, h2]
      exact KmmStep.placeInput ⟨t.1, hlt⟩ (by rw [card_prefixInputs' (Nat.le_of_lt hlt)]; omega)
    · by_cases hm0 : (t.1 - m) % 3 = 0
      · have h1 : tr t.castSucc = inputNodes m := by
          dsimp only [tr]
          by_cases heq : t.1 = m
          · have hle1 : t.castSucc.1 ≤ m := by simp; omega
            simp only [hle1, ↓reduceDIte]
            simpa [heq] using prefixInputs_eq_inputNodes' m
          · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hne0 : (t.castSucc.1 - m - 1) % 3 ≠ 0 := by simp; omega
            have hne1 : (t.castSucc.1 - m - 1) % 3 ≠ 1 := by simp; omega
            simp only [hgt1, hne0, hne1, ↓reduceDIte]
        have h2 : tr t.succ =
            insert (Sum.inr ⟨(t.1 - m) / 3, by omega⟩) ((inputNodes m).erase (Sum.inl ⟨0, hm⟩)) := by
          dsimp only [tr]
          have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
          have heq0 : (t.succ.1 - m - 1) % 3 = 0 := by simp; omega
          simp only [hgt2, heq0, ↓reduceDIte, suffixInputs_one m hm]
          congr 2
          ext
          simp only [Fin.val_succ]
          omega
        rw [h1, h2]
        exact KmmStep.slideOutput ⟨0, hm⟩ ⟨(t.1 - m) / 3, by omega⟩ subset_rfl
          (by rw [card_inputNodes])
      · by_cases hm1 : (t.1 - m) % 3 = 1
        · have h1 : tr t.castSucc =
              insert (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) (suffixInputs m 1) := by
            dsimp only [tr]
            have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
            have heq0 : (t.castSucc.1 - m - 1) % 3 = 0 := by simp; omega
            simp only [hgt1, heq0, ↓reduceDIte]
            rfl
          have h2 : tr t.succ = suffixInputs m 1 := by
            dsimp only [tr]
            have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
            have heq1 : (t.succ.1 - m - 1) % 3 = 1 := by simp; omega
            simp only [hgt2, heq1, Nat.one_ne_zero, ↓reduceDIte]
          have hnot : Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩ ∉ suffixInputs m 1 := by
            simp [suffixInputs]
          have herase :
              (insert (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) (suffixInputs m 1)).erase
                (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) = suffixInputs m 1 :=
            Finset.erase_insert hnot
          have hcard :
              (insert (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) (suffixInputs m 1)).card ≤ m := by
            rw [← h1]; exact hspace t.castSucc
          rw [h1, h2]
          simpa [herase] using KmmStep.remove (Sum.inr ⟨(t.1 - m - 1) / 3, by omega⟩) hcard
        · have h1 : tr t.castSucc = suffixInputs m 1 := by
            dsimp only [tr]
            have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
            have heq1 : (t.castSucc.1 - m - 1) % 3 = 1 := by simp; omega
            simp only [hgt1, heq1, Nat.one_ne_zero, ↓reduceDIte]
          have h2 : tr t.succ = insert (Sum.inl ⟨0, hm⟩) (suffixInputs m 1) := by
            dsimp only [tr]
            have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
            have hne0 : (t.succ.1 - m - 1) % 3 ≠ 0 := by simp; omega
            have hne1 : (t.succ.1 - m - 1) % 3 ≠ 1 := by simp; omega
            simp only [hgt2, hne0, hne1, ↓reduceDIte, suffixInputs_one m hm]
            have hmem : Sum.inl ⟨0, hm⟩ ∈ inputNodes m :=
              Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩
            exact (Finset.insert_erase hmem).symm
          have hcard : (suffixInputs m 1).card < m := by
            rw [card_suffixInputs hm]; omega
          rw [h1, h2]
          exact KmmStep.placeInput ⟨0, hm⟩ hcard
  have hout : ∀ j : Fin m, ∃ t : Fin (T + 1), Sum.inr j ∈ tr t := by
    intro j
    refine ⟨⟨m + 3 * j.1 + 1, by omega⟩, ?_⟩
    dsimp only [tr]
    have hgt : ¬ (m + 3 * j.1 + 1 ≤ m) := by omega
    have heq0 : (m + 3 * j.1 + 1 - m - 1) % 3 = 0 := by omega
    simp only [hgt, heq0, ↓reduceDIte]
    have hidx : (⟨(m + 3 * j.1 + 1 - m - 1) / 3, by omega⟩ : Fin m) = j := by
      ext; simp only; omega
    rw [hidx]
    exact Finset.mem_insert_self _ _
  let P : ValidKmmPebbling m m :=
    { steps := T
      trace := tr
      init_empty := by simp [tr, prefixInputs_zero']
      space_le := hspace
      valid_step := hstep
      outputs_computed := hout }
  have hpsi : ∀ t : Fin (T + 1), inputCount (tr t) =
      if t.1 ≤ m then t.1
      else if (t.1 - m - 1) % 3 = 0 then m - 1
      else if (t.1 - m - 1) % 3 = 1 then m - 1
      else m := by
    intro t
    dsimp only [tr]
    by_cases hle : t.1 ≤ m
    · simp only [hle, ↓reduceDIte, ↓reduceIte]
      exact inputCount_prefixInputs' hle
    · by_cases h0 : (t.1 - m - 1) % 3 = 0
      · simp only [hle, h0, ↓reduceDIte, ↓reduceIte, inputCount_insert_inr, inputCount_suffixInputs hm]
      · by_cases h1 : (t.1 - m - 1) % 3 = 1
        · simp only [hle, h1, Nat.one_ne_zero, ↓reduceDIte, ↓reduceIte, inputCount_suffixInputs hm]
        · simp only [hle, h0, h1, ↓reduceDIte, ↓reduceIte, inputCount_inputNodes']
  have hrec_eq :
      recoverySet (kmmSeparatorSystem m m) tr =
        (Finset.univ.image (fun i : Fin m => (⟨i.1, by omega⟩ : Fin T))) ∪
        (Finset.univ.image (fun q : Fin (m - 1) => (⟨m + 3 * q.1 + 2, by omega⟩ : Fin T))) := by
    ext t
    have ht_lt : t.1 < 4 * m - 2 := t.2
    simp only [recoverySet, kmmSeparatorSystem, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image, hpsi, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    constructor
    · intro hlt
      by_cases ht : t.1 < m
      · left; exact ⟨⟨t.1, ht⟩, rfl⟩
      · right
        have hmod : (t.1 - m) % 3 = 2 := by
          split_ifs at hlt <;> omega
        refine ⟨⟨(t.1 - m) / 3, by omega⟩, by simp; omega⟩
    · rintro (⟨i, hi⟩ | ⟨q, hq⟩)
      · split_ifs <;> omega
      · split_ifs <;> omega
  have hdisj : Disjoint
      (Finset.univ.image (fun i : Fin m => (⟨i.1, by omega⟩ : Fin T)))
      (Finset.univ.image (fun q : Fin (m - 1) => (⟨m + 3 * q.1 + 2, by omega⟩ : Fin T))) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rcases Finset.mem_image.mp ht1 with ⟨i, _, hi⟩
    rcases Finset.mem_image.mp ht2 with ⟨q, _, hq⟩
    have : i.1 = m + 3 * q.1 + 2 := by
      have := congrArg Fin.val (hi.trans hq.symm)
      simpa using this
    omega
  have hrec_card : inputPlacements P = 2 * m - 1 := by
    change (recoverySet (kmmSeparatorSystem m m) tr).card = 2 * m - 1
    rw [hrec_eq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by
        have := congrArg Fin.val h; simp at this; omega)),
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    omega
  have hend : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ =
      insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1) := by
    change tr ⟨T, Nat.lt_succ_self _⟩ = _
    dsimp only [tr]
    have hgt : ¬ (T ≤ m) := by omega
    have h0 : (T - m - 1) % 3 = 0 := by omega
    simp only [hgt, h0, ↓reduceDIte]
    congr 2
    ext
    simp only
    omega
  exact ⟨P, hrec_card, rfl, hend⟩

/-- Range of output vertices `{v_a, ..., v_{b-1}}`. -/
private def rangeOutputs (m a b : ℕ) : KmmConfig m :=
  (Finset.univ.filter (fun j : Fin m => a ≤ j.1 ∧ j.1 < b)).image Sum.inr

private theorem rangeOutputs_empty {m a b : ℕ} (hab : b ≤ a) : rangeOutputs m a b = ∅ := by
  ext v
  simp only [rangeOutputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_exists, not_and]
  intro j hj _
  omega

private theorem rangeOutputs_succ {m a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    rangeOutputs m a (b + 1) = insert (Sum.inr ⟨b, hb⟩) (rangeOutputs m a b) := by
  ext v
  simp only [rangeOutputs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases heq : j.1 = b
    · left; exact congrArg Sum.inr (Fin.ext heq)
    · right; exact ⟨j, by omega, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨b, hb⟩, ⟨hab, Nat.lt_succ_self b⟩, rfl⟩
    · exact ⟨j, by omega, rfl⟩

private theorem card_rangeOutputs {m a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    (rangeOutputs m a b).card = b - a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
    simp [rangeOutputs_empty]
  | succ d ih =>
    have hlt : a + d < m := by omega
    have hnot : Sum.inr ⟨a + d, hlt⟩ ∉ rangeOutputs m a (a + d) := by
      simp [rangeOutputs]
    have heq : a + (d + 1) = (a + d) + 1 := by omega
    rw [heq, rangeOutputs_succ (Nat.le_add_right a d) hlt,
      Finset.card_insert_of_notMem hnot, ih (Nat.le_add_right a d) (by omega)]
    omega

private theorem rangeOutputs_zero_eq_outputNodes (m : ℕ) :
    rangeOutputs m 0 m = outputNodes m := by
  ext v
  simp [rangeOutputs, outputNodes]

private theorem inputCount_union_rangeOutputs {m a b : ℕ} (C : KmmConfig m)
    (hC : ∀ v ∈ C, v.isLeft = true) :
    inputCount (C ∪ rangeOutputs m a b) = C.card := by
  have hfilt : (C ∪ rangeOutputs m a b).filter (fun v : KmmNode m => v.isLeft = true) = C := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_union, rangeOutputs, Finset.mem_image]
    constructor
    · rintro ⟨hv | ⟨j, _, rfl⟩, hL⟩
      · exact hv
      · simp at hL
    · intro hv
      exact ⟨Or.inl hv, hC v hv⟩
  rw [inputCount, hfilt]

private theorem inputNodes_all_left {m : ℕ} : ∀ v ∈ inputNodes m, v.isLeft = true := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
  rfl

private theorem suffixInputs_all_left {m k : ℕ} : ∀ v ∈ suffixInputs m k, v.isLeft = true := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
  rfl

/-- Parameterized zero-recomputation pebbling for `r = 0 ∨ r + 2 ≤ m` using space
`S_r = 2 * m - 1 - r` (which satisfies `m + 1 ≤ S_r` whenever `r > 0`, allowing the first `r`
outputs to be placed and removed before filling the remaining `m - 1 - r` outputs and sliding onto
output `m - 1`). Length is `2 * m + r`, `inputPlacements = m`, and the final configuration is
`suffixInputs m 1 ∪ rangeOutputs m r m`. -/
private def zeroRecompParam (m r : ℕ) (hm : 1 ≤ m) (hr : r = 0 ∨ r + 2 ≤ m) :
    { P : ValidKmmPebbling m (2 * m - 1 - r) //
      inputPlacements P = m ∧ P.steps = 2 * m + r ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = suffixInputs m 1 ∪ rangeOutputs m r m } := by
  let S := 2 * m - 1 - r
  let T := 2 * m + r
  have hr_lt : r < m := by omega
  let tr : Fin (T + 1) → KmmConfig m := fun t =>
    if h1 : t.1 ≤ m then
      prefixInputs m t.1
    else if h2 : t.1 ≤ m + 2 * r then
      if (t.1 - m) % 2 = 1 then
        insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
      else
        inputNodes m
    else if h3 : t.1 < T then
      inputNodes m ∪ rangeOutputs m r (t.1 - m - r)
    else
      suffixInputs m 1 ∪ rangeOutputs m r m
  have hspace : ∀ t : Fin (T + 1), (tr t).card ≤ S := by
    intro t
    dsimp only [tr]
    split_ifs with h1 h2 hodd h3
    · rw [card_prefixInputs' h1]; omega
    · have hins := Finset.card_insert_le
        (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
      rw [card_inputNodes] at hins; omega
    · rw [card_inputNodes]; omega
    · have hu := Finset.card_union_le (inputNodes m) (rangeOutputs m r (t.1 - m - r))
      rw [card_inputNodes, card_rangeOutputs (by omega) (by omega)] at hu
      omega
    · have hu := Finset.card_union_le (suffixInputs m 1) (rangeOutputs m r m)
      rw [card_suffixInputs hm, card_rangeOutputs (Nat.le_of_lt hr_lt) le_rfl] at hu
      omega
  have hstep : ∀ t : Fin T, KmmStep m S (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt1 : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInputs m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = insert (Sum.inl ⟨t.1, hlt1⟩) (prefixInputs m t.1) := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInputs_succ' hlt1
      rw [h1, h2]
      exact KmmStep.placeInput ⟨t.1, hlt1⟩ (by rw [card_prefixInputs' (Nat.le_of_lt hlt1)]; omega)
    · by_cases hlt2 : t.1 < m + 2 * r
      · by_cases heven : (t.1 - m) % 2 = 0
        · have h1 : tr t.castSucc = inputNodes m := by
            dsimp only [tr]
            by_cases heq : t.1 = m
            · have hle1 : t.castSucc.1 ≤ m := by simp; omega
              simp only [hle1, ↓reduceDIte]
              simpa [heq] using prefixInputs_eq_inputNodes' m
            · have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
              have hle : t.castSucc.1 ≤ m + 2 * r := by simp; omega
              have hne : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
              simp only [hgt, hle, hne, ↓reduceDIte, ↓reduceIte]
          have h2 : tr t.succ =
              insert (Sum.inr ⟨(t.1 - m) / 2, by omega⟩) (inputNodes m) := by
            dsimp only [tr]
            have hgt : ¬ t.succ.1 ≤ m := by simp; omega
            have hle : t.succ.1 ≤ m + 2 * r := by simp; omega
            have hodd : (t.succ.1 - m) % 2 = 1 := by simp; omega
            simp only [hgt, hle, hodd, ↓reduceDIte, ↓reduceIte]
            congr 2; ext; simp only [Fin.val_succ]; omega
          rw [h1, h2]
          exact KmmStep.placeOutput ⟨(t.1 - m) / 2, by omega⟩ subset_rfl
            (by rw [card_inputNodes]; omega)
        · have h1 : tr t.castSucc =
              insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m) := by
            dsimp only [tr]
            have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hle : t.castSucc.1 ≤ m + 2 * r := by simp; omega
            have hodd : (t.castSucc.1 - m) % 2 = 1 := by simp; omega
            simp only [hgt, hle, hodd, ↓reduceDIte, ↓reduceIte]; rfl
          have h2 : tr t.succ = inputNodes m := by
            dsimp only [tr]
            have hgt : ¬ t.succ.1 ≤ m := by simp; omega
            have hle : t.succ.1 ≤ m + 2 * r := by simp; omega
            have hne : (t.succ.1 - m) % 2 ≠ 1 := by simp; omega
            simp only [hgt, hle, hne, ↓reduceDIte, ↓reduceIte]
          have hnot : Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩ ∉ inputNodes m := by simp [inputNodes]
          have herase : (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).erase
              (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) = inputNodes m := Finset.erase_insert hnot
          have hcard : (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).card ≤ S := by
            rw [← h1]; exact hspace t.castSucc
          rw [h1, h2]
          simpa [herase] using KmmStep.remove (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) hcard
      · by_cases hlt3 : t.1 + 1 < T
        · have h1 : tr t.castSucc = inputNodes m ∪ rangeOutputs m r (t.1 - m - r) := by
            dsimp only [tr]
            by_cases heq : t.1 = m + 2 * r
            · have hrem : rangeOutputs m r (t.1 - m - r) = ∅ := rangeOutputs_empty (by omega)
              rw [hrem, Finset.union_empty]
              by_cases hr0 : r = 0
              · have hle1 : t.castSucc.1 ≤ m := by simp; omega
                simp only [hle1, ↓reduceDIte]
                simpa [heq, hr0] using prefixInputs_eq_inputNodes' m
              · have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
                have hle : t.castSucc.1 ≤ m + 2 * r := by simp; omega
                have hne : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
                simp only [hgt, hle, hne, ↓reduceDIte, ↓reduceIte]
            · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
              have hgt2 : ¬ t.castSucc.1 ≤ m + 2 * r := by simp; omega
              have hltT : t.castSucc.1 < T := t.2
              simp only [hgt1, hgt2, hltT, ↓reduceDIte]; rfl
          have h2 : tr t.succ =
              insert (Sum.inr ⟨t.1 - m - r, by omega⟩)
                (inputNodes m ∪ rangeOutputs m r (t.1 - m - r)) := by
            dsimp only [tr]
            have hgt1 : ¬ t.succ.1 ≤ m := by simp; omega
            have hgt2 : ¬ t.succ.1 ≤ m + 2 * r := by simp; omega
            have hltT : t.succ.1 < T := by simp; omega
            simp only [hgt1, hgt2, hltT, ↓reduceDIte]
            simp only [Fin.val_succ]
            have hsub : t.1 + 1 - m - r = (t.1 - m - r) + 1 := by omega
            rw [hsub, rangeOutputs_succ (by omega) (by omega), Finset.union_insert]
          have hcard : (inputNodes m ∪ rangeOutputs m r (t.1 - m - r)).card < S := by
            have hu := Finset.card_union_le (inputNodes m) (rangeOutputs m r (t.1 - m - r))
            rw [card_inputNodes, card_rangeOutputs (by omega) (by omega)] at hu
            omega
          rw [h1, h2]
          exact KmmStep.placeOutput ⟨t.1 - m - r, by omega⟩ Finset.subset_union_left hcard
        · -- Final slide step: t.1 = T - 1
          have ht_eq : t.1 = T - 1 := by omega
          have h1 : tr t.castSucc = inputNodes m ∪ rangeOutputs m r (m - 1) := by
            dsimp only [tr]
            by_cases heq : t.1 = m + 2 * r
            · have hrem : rangeOutputs m r (m - 1) = ∅ := rangeOutputs_empty (by omega)
              rw [hrem, Finset.union_empty]
              by_cases hr0 : r = 0
              · have hle1 : t.castSucc.1 ≤ m := by simp; omega
                simp only [hle1, ↓reduceDIte]
                have htm : t.castSucc.1 = m := by simp; omega
                rw [htm]; exact prefixInputs_eq_inputNodes' m
              · have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
                have hle : t.castSucc.1 ≤ m + 2 * r := by simp; omega
                have hne : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
                simp only [hgt, hle, hne, ↓reduceDIte, ↓reduceIte]
            · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
              have hgt2 : ¬ t.castSucc.1 ≤ m + 2 * r := by simp; omega
              have hltT : t.castSucc.1 < T := t.2
              simp only [hgt1, hgt2, hltT, ↓reduceDIte]
              simp only [Fin.val_castSucc]
              have hsub : t.1 - m - r = m - 1 := by omega
              rw [hsub]
          have h2 : tr t.succ =
              insert (Sum.inr ⟨m - 1, by omega⟩)
                ((inputNodes m ∪ rangeOutputs m r (m - 1)).erase (Sum.inl ⟨0, hm⟩)) := by
            dsimp only [tr]
            have hgt1 : ¬ t.succ.1 ≤ m := by simp; omega
            have hgt2 : ¬ t.succ.1 ≤ m + 2 * r := by simp; omega
            have hgeT : ¬ t.succ.1 < T := by simp; omega
            simp only [hgt1, hgt2, hgeT, ↓reduceDIte]
            have hnot_out : Sum.inl ⟨0, hm⟩ ∉ rangeOutputs m r (m - 1) := by simp [rangeOutputs]
            rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnot_out,
              ← suffixInputs_one m hm, ← Finset.union_insert]
            have hsucc_out : insert (Sum.inr ⟨m - 1, by omega⟩) (rangeOutputs m r (m - 1)) =
                rangeOutputs m r m := by
              have h := rangeOutputs_succ (by omega : r ≤ m - 1) (by omega : m - 1 < m)
              have hm_eq : m - 1 + 1 = m := by omega
              rw [hm_eq] at h
              exact h.symm
            rw [hsucc_out]
          have hcard : (inputNodes m ∪ rangeOutputs m r (m - 1)).card ≤ S := by
            rw [← h1]; exact hspace t.castSucc
          rw [h1, h2]
          exact KmmStep.slideOutput ⟨0, hm⟩ ⟨m - 1, by omega⟩ Finset.subset_union_left hcard
  have hout : ∀ j : Fin m, ∃ t : Fin (T + 1), Sum.inr j ∈ tr t := by
    intro j
    by_cases hj : j.1 < r
    · refine ⟨⟨m + 2 * j.1 + 1, by omega⟩, ?_⟩
      dsimp only [tr]
      have hgt : ¬ (m + 2 * j.1 + 1 ≤ m) := by omega
      have hle : m + 2 * j.1 + 1 ≤ m + 2 * r := by omega
      have hodd : (m + 2 * j.1 + 1 - m) % 2 = 1 := by omega
      simp only [hgt, hle, hodd, ↓reduceDIte, ↓reduceIte]
      have hidx : (⟨(m + 2 * j.1 + 1 - m - 1) / 2, by omega⟩ : Fin m) = j := by
        ext; simp only; omega
      rw [hidx]
      exact Finset.mem_insert_self _ _
    · refine ⟨⟨T, Nat.lt_succ_self _⟩, ?_⟩
      dsimp only [tr]
      have hgt1 : ¬ (T ≤ m) := by omega
      have hgt2 : ¬ (T ≤ m + 2 * r) := by omega
      have hgeT : ¬ (T < T) := lt_irrefl _
      simp only [hgt1, hgt2, hgeT, ↓reduceDIte]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, j.2⟩, rfl⟩
  let P : ValidKmmPebbling m S :=
    { steps := T
      trace := tr
      init_empty := by simp [tr, prefixInputs_zero']
      space_le := hspace
      valid_step := hstep
      outputs_computed := hout }
  have hpsi : ∀ t : Fin (T + 1), inputCount (tr t) =
      if t.1 ≤ m then t.1 else if t.1 < T then m else m - 1 := by
    intro t
    dsimp only [tr]
    by_cases h1 : t.1 ≤ m
    · simp only [h1, ↓reduceDIte, ↓reduceIte]
      exact inputCount_prefixInputs' h1
    · by_cases h2 : t.1 ≤ m + 2 * r
      · have hltT : t.1 < T := by omega
        simp only [h1, h2, hltT, ↓reduceDIte, ↓reduceIte]
        split_ifs
        · rw [inputCount_insert_inr, inputCount_inputNodes']
        · rw [inputCount_inputNodes']
      · by_cases h3 : t.1 < T
        · simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]
          rw [inputCount_union_rangeOutputs (inputNodes m) inputNodes_all_left, card_inputNodes]
        · simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]
          rw [inputCount_union_rangeOutputs (suffixInputs m 1) suffixInputs_all_left,
            card_suffixInputs hm]
  have hrec_eq :
      recoverySet (kmmSeparatorSystem m S) tr =
        Finset.univ.image (fun i : Fin m => (⟨i.1, by omega⟩ : Fin T)) := by
    ext t
    have ht_lt : t.1 < 2 * m + r := t.2
    simp only [recoverySet, kmmSeparatorSystem, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, hpsi, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    constructor
    · intro hlt
      have ht : t.1 < m := by split_ifs at hlt <;> omega
      exact ⟨⟨t.1, ht⟩, rfl⟩
    · rintro ⟨i, hi⟩
      split_ifs <;> omega
  have hrec_card : inputPlacements P = m := by
    change (recoverySet (kmmSeparatorSystem m S) tr).card = m
    rw [hrec_eq,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)),
      Finset.card_univ, Fintype.card_fin]
  have hend : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = suffixInputs m 1 ∪ rangeOutputs m r m := by
    change tr ⟨T, Nat.lt_succ_self _⟩ = _
    dsimp only [tr]
    have hgt1 : ¬ (T ≤ m) := by omega
    have hgt2 : ¬ (T ≤ m + 2 * r) := by omega
    have hgeT : ¬ (T < T) := lt_irrefl _
    simp only [hgt1, hgt2, hgeT, ↓reduceDIte]
  exact ⟨P, hrec_card, rfl, hend⟩

/-- **Exact Optimal VisitAll Upper Bound on `K_{m, m}`**:
Matches `k_mm_visitAll_exact_lower_bound` in every `(m, S)` regime (`1 ≤ m`, `m ≤ S`). -/
theorem k_mm_visitAll_optimal_upper_bound {m S : ℕ} (hm : 1 ≤ m) (hS : m ≤ S) :
    (S = m → ∃ P : ValidKmmPebbling m S, inputPlacements P = 2 * m - 1 ∧ P.steps = 4 * m - 2) ∧
    (m < S → ∃ P : ValidKmmPebbling m S,
      inputPlacements P = m ∧ P.steps = max (2 * m) (4 * m - 1 - S)) := by
  constructor
  · intro hEq
    subst S
    rcases visitAllAtM m hm with ⟨P, hrec, hsteps, _⟩
    exact ⟨P, hrec, hsteps⟩
  · intro hlt
    by_cases hbig : 2 * m - 1 ≤ S
    · rcases zeroRecompParam m 0 hm (Or.inl rfl) with ⟨P, hrec, hsteps, _⟩
      refine ⟨weakenPebbling (by omega) P, ?_, ?_⟩
      · exact hrec
      · change P.steps = max (2 * m) (4 * m - 1 - S)
        omega
    · let r := 2 * m - 1 - S
      have hr : r = 0 ∨ r + 2 ≤ m := Or.inr (by omega)
      rcases zeroRecompParam m r hm hr with ⟨P, hrec, hsteps, _⟩
      have hSr : 2 * m - 1 - r ≤ S := by omega
      refine ⟨weakenPebbling hSr P, ?_, ?_⟩
      · exact hrec
      · change P.steps = max (2 * m) (4 * m - 1 - S)
        omega

/-- Zero-recomputation VisitAll pebbling at `S = m + 1` in `3 * m - 1` steps ending at
`insert (Sum.inr ⟨m - 1, _⟩) (suffixInputs m 1)` (for appending `cleanupToEmptyTrace`). -/
private def visitAllAtMPlusOneForClean (m : ℕ) (hm : 1 ≤ m) :
    { P : ValidKmmPebbling m (m + 1) //
      inputPlacements P = m ∧ P.steps = 3 * m - 1 ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ =
        insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1) } := by
  let T := 3 * m - 1
  let tr : Fin (T + 1) → KmmConfig m := fun t =>
    if h1 : t.1 ≤ m then
      prefixInputs m t.1
    else if h2 : t.1 < T then
      if (t.1 - m) % 2 = 1 then
        insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
      else
        inputNodes m
    else
      insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)
  have hspace : ∀ t : Fin (T + 1), (tr t).card ≤ m + 1 := by
    intro t
    dsimp only [tr]
    split_ifs with h1 h2 hodd
    · rw [card_prefixInputs' h1]; omega
    · have hins := Finset.card_insert_le
        (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)
      rw [card_inputNodes] at hins; omega
    · rw [card_inputNodes]; omega
    · have hins := Finset.card_insert_le (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1)
      rw [card_suffixInputs hm] at hins; omega
  have hstep : ∀ t : Fin T, KmmStep m (m + 1) (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt1 : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInputs m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = insert (Sum.inl ⟨t.1, hlt1⟩) (prefixInputs m t.1) := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInputs_succ' hlt1
      rw [h1, h2]
      exact KmmStep.placeInput ⟨t.1, hlt1⟩ (by rw [card_prefixInputs' (Nat.le_of_lt hlt1)]; omega)
    · by_cases hlt2 : t.1 + 1 < T
      · by_cases heven : (t.1 - m) % 2 = 0
        · have h1 : tr t.castSucc = inputNodes m := by
            dsimp only [tr]
            by_cases heq : t.1 = m
            · have hle1 : t.castSucc.1 ≤ m := by simp; omega
              simp only [hle1, ↓reduceDIte]
              simpa [heq] using prefixInputs_eq_inputNodes' m
            · have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
              have hlt : t.castSucc.1 < T := t.2
              have hne : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
              simp only [hgt, hlt, hne, ↓reduceDIte, ↓reduceIte]
          have h2 : tr t.succ =
              insert (Sum.inr ⟨(t.1 - m) / 2, by omega⟩) (inputNodes m) := by
            dsimp only [tr]
            have hgt : ¬ t.succ.1 ≤ m := by simp; omega
            have hlt : t.succ.1 < T := by simp; omega
            have hodd : (t.succ.1 - m) % 2 = 1 := by simp; omega
            simp only [hgt, hlt, hodd, ↓reduceDIte, ↓reduceIte]
            congr 2; ext; simp only [Fin.val_succ]; omega
          rw [h1, h2]
          exact KmmStep.placeOutput ⟨(t.1 - m) / 2, by omega⟩ subset_rfl
            (by rw [card_inputNodes]; omega)
        · have h1 : tr t.castSucc =
              insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m) := by
            dsimp only [tr]
            have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hlt : t.castSucc.1 < T := t.2
            have hodd : (t.castSucc.1 - m) % 2 = 1 := by simp; omega
            simp only [hgt, hlt, hodd, ↓reduceDIte, ↓reduceIte]; rfl
          have h2 : tr t.succ = inputNodes m := by
            dsimp only [tr]
            have hgt : ¬ t.succ.1 ≤ m := by simp; omega
            have hlt : t.succ.1 < T := by simp; omega
            have hne : (t.succ.1 - m) % 2 ≠ 1 := by simp; omega
            simp only [hgt, hlt, hne, ↓reduceDIte, ↓reduceIte]
          have hnot : Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩ ∉ inputNodes m := by simp [inputNodes]
          have herase : (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).erase
              (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) = inputNodes m := Finset.erase_insert hnot
          have hcard :
              (insert (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) (inputNodes m)).card ≤ m + 1 := by
            rw [← h1]; exact hspace t.castSucc
          rw [h1, h2]
          simpa [herase] using KmmStep.remove (Sum.inr ⟨(t.1 - m - 1) / 2, by omega⟩) hcard
      · -- Final slide step: t.1 = T - 1 = 3 * m - 2
        have h1 : tr t.castSucc = inputNodes m := by
          dsimp only [tr]
          by_cases hm1 : m = 1
          · have hle1 : t.castSucc.1 ≤ m := by simp; omega
            simp only [hle1, ↓reduceDIte]
            have htm : t.castSucc.1 = m := by simp; omega
            rw [htm]; exact prefixInputs_eq_inputNodes' m
          · have hgt : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hlt : t.castSucc.1 < T := t.2
            have hne : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
            simp only [hgt, hlt, hne, ↓reduceDIte, ↓reduceIte]
        have h2 : tr t.succ =
            insert (Sum.inr ⟨m - 1, by omega⟩) ((inputNodes m).erase (Sum.inl ⟨0, hm⟩)) := by
          dsimp only [tr]
          have hgt : ¬ t.succ.1 ≤ m := by simp; omega
          have hge : ¬ t.succ.1 < T := by simp; omega
          simp only [hgt, hge, ↓reduceDIte, suffixInputs_one m hm]
        rw [h1, h2]
        exact KmmStep.slideOutput ⟨0, hm⟩ ⟨m - 1, by omega⟩ subset_rfl
          (by rw [card_inputNodes]; omega)
  have hout : ∀ j : Fin m, ∃ t : Fin (T + 1), Sum.inr j ∈ tr t := by
    intro j
    by_cases hj : j.1 < m - 1
    · refine ⟨⟨m + 2 * j.1 + 1, by omega⟩, ?_⟩
      dsimp only [tr]
      have hgt : ¬ (m + 2 * j.1 + 1 ≤ m) := by omega
      have hlt : m + 2 * j.1 + 1 < T := by omega
      have hodd : (m + 2 * j.1 + 1 - m) % 2 = 1 := by omega
      simp only [hgt, hlt, hodd, ↓reduceDIte, ↓reduceIte]
      have hidx : (⟨(m + 2 * j.1 + 1 - m - 1) / 2, by omega⟩ : Fin m) = j := by
        ext; simp only; omega
      rw [hidx]
      exact Finset.mem_insert_self _ _
    · refine ⟨⟨T, Nat.lt_succ_self _⟩, ?_⟩
      dsimp only [tr]
      have hgt : ¬ (T ≤ m) := by omega
      have hge : ¬ (T < T) := lt_irrefl _
      simp only [hgt, hge, ↓reduceDIte]
      have hidx : (⟨m - 1, by omega⟩ : Fin m) = j := Fin.ext (by simp; omega)
      rw [hidx]
      exact Finset.mem_insert_self _ _
  let P : ValidKmmPebbling m (m + 1) :=
    { steps := T
      trace := tr
      init_empty := by simp [tr, prefixInputs_zero']
      space_le := hspace
      valid_step := hstep
      outputs_computed := hout }
  have hpsi : ∀ t : Fin (T + 1), inputCount (tr t) =
      if t.1 ≤ m then t.1 else if t.1 < T then m else m - 1 := by
    intro t
    dsimp only [tr]
    by_cases h1 : t.1 ≤ m
    · simp only [h1, ↓reduceDIte, ↓reduceIte]
      exact inputCount_prefixInputs' h1
    · by_cases h2 : t.1 < T
      · simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
        split_ifs
        · rw [inputCount_insert_inr, inputCount_inputNodes']
        · rw [inputCount_inputNodes']
      · simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
        rw [inputCount_insert_inr, inputCount_suffixInputs hm]
  have hrec_eq :
      recoverySet (kmmSeparatorSystem m (m + 1)) tr =
        Finset.univ.image (fun i : Fin m => (⟨i.1, by omega⟩ : Fin T)) := by
    ext t
    have ht_lt : t.1 < 3 * m - 1 := t.2
    simp only [recoverySet, kmmSeparatorSystem, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, hpsi, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    constructor
    · intro hlt
      have ht : t.1 < m := by split_ifs at hlt <;> omega
      exact ⟨⟨t.1, ht⟩, rfl⟩
    · rintro ⟨i, hi⟩
      split_ifs <;> omega
  have hrec_card : inputPlacements P = m := by
    change (recoverySet (kmmSeparatorSystem m (m + 1)) tr).card = m
    rw [hrec_eq,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)),
      Finset.card_univ, Fintype.card_fin]
  have hend : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ =
      insert (Sum.inr ⟨m - 1, by omega⟩) (suffixInputs m 1) := by
    change tr ⟨T, Nat.lt_succ_self _⟩ = _
    dsimp only [tr]
    have hgt : ¬ (T ≤ m) := by omega
    have hge : ¬ (T < T) := lt_irrefl _
    simp only [hgt, hge, ↓reduceDIte]
  exact ⟨P, hrec_card, rfl, hend⟩

/-- **Exact Optimal VisitAllClean Upper Bound on `K_{m, m}`**:
Matches `k_mm_visitAllClean_exact_lower_bound` in every `(m, S)` regime (`1 ≤ m`, `m ≤ S`), ending
at `∅`. -/
theorem k_mm_visitAllClean_optimal_upper_bound {m S : ℕ} (hm : 1 ≤ m) (hS : m ≤ S) :
    (S = m → ∃ P : ValidKmmPebbling m S,
      inputPlacements P = 2 * m - 1 ∧ P.steps = 5 * m - 2 ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = ∅) ∧
    (m < S → ∃ P : ValidKmmPebbling m S,
      inputPlacements P = m ∧ P.steps = 4 * m - 1 ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = ∅) := by
  constructor
  · intro hEq
    subst S
    rcases visitAllAtM m hm with ⟨P, hrec, hsteps, hend⟩
    have hjoin : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = cleanupToEmptyTrace m hm 0 := by
      simpa [cleanupToEmptyTrace] using hend
    let Q := appendTailPebbling P (cleanupToEmptyTrace m hm) hjoin
      (cleanupToEmpty_space hm le_rfl) (cleanupToEmpty_step hm le_rfl)
    refine ⟨Q, ?_, ?_, ?_⟩
    · rw [inputPlacements_appendTailPebbling _ _ _ _ _ (cleanupToEmpty_noninc hm)]
      exact hrec
    · change P.steps + m = 5 * m - 2
      omega
    · change appendTrace P.trace (cleanupToEmptyTrace m hm) ⟨P.steps + m, Nat.lt_succ_self _⟩ = ∅
      rw [appendTrace_last _ _ hjoin]
      dsimp only [cleanupToEmptyTrace]
      have hne : m ≠ 0 := by omega
      simp [hne, suffixInputs_ge m m le_rfl]
  · intro hlt
    rcases visitAllAtMPlusOneForClean m hm with ⟨P, hrec, hsteps, hend⟩
    have hjoin : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = cleanupToEmptyTrace m hm 0 := by
      simpa [cleanupToEmptyTrace] using hend
    let Q := appendTailPebbling P (cleanupToEmptyTrace m hm) hjoin
      (cleanupToEmpty_space hm (by omega)) (cleanupToEmpty_step hm (by omega))
    refine ⟨weakenPebbling (by omega : m + 1 ≤ S) Q, ?_, ?_, ?_⟩
    · rw [inputPlacements_weakenPebbling,
        inputPlacements_appendTailPebbling _ _ _ _ _ (cleanupToEmpty_noninc hm)]
      exact hrec
    · change P.steps + m = 4 * m - 1
      omega
    · change appendTrace P.trace (cleanupToEmptyTrace m hm) ⟨P.steps + m, Nat.lt_succ_self _⟩ = ∅
      rw [appendTrace_last _ _ hjoin]
      dsimp only [cleanupToEmptyTrace]
      have hne : m ≠ 0 := by omega
      simp [hne, suffixInputs_ge m m le_rfl]

/-- **Exact Optimal CoexistAll Upper Bound on `K_{m, m}`**:
For every `1 ≤ m` and `2 * m - 1 ≤ S`, achieves `inputPlacements = m`, `P.steps = 2 * m`, and
`outputNodes m ⊆ P.trace ⟨P.steps, _⟩`. -/
theorem k_mm_coexistAll_optimal_upper_bound {m S : ℕ} (hm : 1 ≤ m) (hS : 2 * m - 1 ≤ S) :
    ∃ P : ValidKmmPebbling m S,
      inputPlacements P = m ∧ P.steps = 2 * m ∧
      outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩ := by
  rcases zeroRecompParam m 0 hm (Or.inl rfl) with ⟨P, hrec, hsteps, hend⟩
  refine ⟨weakenPebbling (by omega : 2 * m - 1 - 0 ≤ S) P, hrec, ?_, ?_⟩
  · change P.steps = 2 * m
    omega
  · change outputNodes m ⊆ P.trace ⟨P.steps, Nat.lt_succ_self _⟩
    rw [hend, rangeOutputs_zero_eq_outputNodes]
    exact Finset.subset_union_right

/-- Cleanup tail of length `m - 1`: from `suffixInputs m 1 ∪ outputNodes m` down to
`outputNodes m` by removing `u_1, ..., u_{m-1}`. -/
private def removeInputsKeepOutputsTrace (m : ℕ) : Fin ((m - 1) + 1) → KmmConfig m :=
  fun k => suffixInputs m (k.1 + 1) ∪ outputNodes m

private theorem removeInputsKeepOutputs_space {m : ℕ} (hm : 1 ≤ m) (k : Fin ((m - 1) + 1)) :
    (removeInputsKeepOutputsTrace m k).card ≤ 2 * m - 1 := by
  dsimp only [removeInputsKeepOutputsTrace]
  have hu := Finset.card_union_le (suffixInputs m (k.1 + 1)) (outputNodes m)
  rw [card_suffixInputs (by omega), card_outputNodes] at hu
  omega

private theorem removeInputsKeepOutputs_step {m : ℕ} (hm : 1 ≤ m) (k : Fin (m - 1)) :
    KmmStep m (2 * m - 1)
      (removeInputsKeepOutputsTrace m k.castSucc) (removeInputsKeepOutputsTrace m k.succ) := by
  dsimp only [removeInputsKeepOutputsTrace]
  have hlt : k.1 + 1 < m := by omega
  have hnot : Sum.inl ⟨k.1 + 1, hlt⟩ ∉ outputNodes m := by simp [outputNodes]
  have herase :
      (suffixInputs m (k.1 + 1) ∪ outputNodes m).erase (Sum.inl ⟨k.1 + 1, hlt⟩) =
        suffixInputs m (k.1 + 1 + 1) ∪ outputNodes m := by
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnot, suffixInputs_succ hlt]
  have hcard : (suffixInputs m (k.1 + 1) ∪ outputNodes m).card ≤ 2 * m - 1 :=
    removeInputsKeepOutputs_space hm k.castSucc
  simpa [Fin.val_castSucc, Fin.val_succ, herase] using
    KmmStep.remove (Sum.inl ⟨k.1 + 1, hlt⟩) hcard

private theorem removeInputsKeepOutputs_noninc {m : ℕ} (k : Fin (m - 1)) :
    inputCount (removeInputsKeepOutputsTrace m k.succ) ≤
      inputCount (removeInputsKeepOutputsTrace m k.castSucc) := by
  dsimp only [removeInputsKeepOutputsTrace]
  have h1 : inputCount (suffixInputs m (k.succ.1 + 1) ∪ outputNodes m) = m - (k.1 + 2) := by
    rw [← rangeOutputs_zero_eq_outputNodes,
      inputCount_union_rangeOutputs (suffixInputs m (k.succ.1 + 1)) suffixInputs_all_left,
      card_suffixInputs (by simp; omega)]
    simp only [Fin.val_succ]
  have h2 : inputCount (suffixInputs m (k.castSucc.1 + 1) ∪ outputNodes m) = m - (k.1 + 1) := by
    rw [← rangeOutputs_zero_eq_outputNodes,
      inputCount_union_rangeOutputs (suffixInputs m (k.castSucc.1 + 1)) suffixInputs_all_left,
      card_suffixInputs (by simp; omega)]
    simp only [Fin.val_castSucc]
  rw [h1, h2]
  omega

/-- **Exact Optimal CoexistAllClean Upper Bound on `K_{m, m}`**:
For every `1 ≤ m` and `2 * m - 1 ≤ S`, achieves `inputPlacements = m`, `P.steps = 3 * m - 1`, and
`P.trace ⟨P.steps, _⟩ = outputNodes m`. -/
theorem k_mm_coexistAllClean_optimal_upper_bound {m S : ℕ} (hm : 1 ≤ m) (hS : 2 * m - 1 ≤ S) :
    ∃ P : ValidKmmPebbling m S,
      inputPlacements P = m ∧ P.steps = 3 * m - 1 ∧
      P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = outputNodes m := by
  rcases zeroRecompParam m 0 hm (Or.inl rfl) with ⟨P, hrec, hsteps, hend⟩
  have hjoin : P.trace ⟨P.steps, Nat.lt_succ_self _⟩ = removeInputsKeepOutputsTrace m 0 := by
    simpa [removeInputsKeepOutputsTrace, rangeOutputs_zero_eq_outputNodes] using hend
  let Q := appendTailPebbling P (removeInputsKeepOutputsTrace m) hjoin
    (removeInputsKeepOutputs_space hm) (removeInputsKeepOutputs_step hm)
  refine ⟨weakenPebbling (by omega : 2 * m - 1 - 0 ≤ S) Q, ?_, ?_, ?_⟩
  · rw [inputPlacements_weakenPebbling,
      inputPlacements_appendTailPebbling _ _ _ _ _ removeInputsKeepOutputs_noninc]
    exact hrec
  · change P.steps + (m - 1) = 3 * m - 1
    omega
  · change appendTrace P.trace (removeInputsKeepOutputsTrace m)
      ⟨P.steps + (m - 1), Nat.lt_succ_self _⟩ = outputNodes m
    rw [appendTrace_last _ _ hjoin]
    dsimp only [removeInputsKeepOutputsTrace]
    have hge : m ≤ m - 1 + 1 := by omega
    rw [suffixInputs_ge m (m - 1 + 1) hge, Finset.empty_union]

end Mathmatica.KmmExactPareto
