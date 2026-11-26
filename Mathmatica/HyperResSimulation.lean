/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.SeparatorRecomputation
import Mathmatica.DAGResolution

/-!
# Bounded-Increment Micro-Step Simulation, `BoundedHyperRes`, and Binary Resolution Space Separation

This module extends the abstract unit-increment separator recovery lower bound of
`Mathmatica.SeparatorRecomputation` to `c`-increment transition systems via micro-step subdivision,
instantiates it on a bounded-arity simultaneous-premise hyper-resolution model (`BoundedHyperRes`)
for the `K_{m, m}` pebbling CNF (`pebKmmCNF m`), and proves a formal separation showing that
unrestricted binary resolution breaks the `S = m` clause-space barrier at constant space `S = 3`.

## Proof Architecture

1. **Part 1 (Generic `c`-Increment Micro-Step Simulation)**:
   Given a `BoundedIncSystem Q c` whose potential `ψ` increases by at most `c` per macro-step,
   we construct a unit-increment `SeparatorSystem (Q × ℕ)` (`microSystem B`) and subdivide any
   legal macro-trace `tr : Fin (T + 1) → Q` into a legal micro-trace
   `microTrace B hc tr : Fin (c * T + 1) → Q × ℕ`.
   * Every macro-boundary `c * k` preserves the exact potential (`microTrace_psi_boundary`).
   * Every micro-recovery step falls inside a macro-recovery step, yielding
     `recoverySteps (microSystem B) (microTrace B hc tr) ≤ c * macroRecoverySteps B tr`.
   * Applying `recomputationLowerBound_of_separator` to the subdivided trace yields
     `boundedInc_recomputation_lower_bound`:
     `m + (k - 1) * drop ≤ c * macroRecoverySteps B tr ∧ m + (k - 1) * drop ≤ c * (T - k)`.

2. **Part 2 (`BoundedHyperRes m S c` on `pebKmmCNF m`)**:
   We encode the complete bipartite pebbling formula `pebKmmCNF m` over `2 * m` Boolean variables
   using `DAGResolution.Lit`, `Clause`, and `CNF`, with unit input clauses `inClause i`, unit
   output clauses `outClause j`, and propagation clauses `propClause j`.
   * `HyperResStep m S c` models a clause-space-`S` hyper-resolution solver that can batch-load up
     to `c` input clauses per step and derives `outClause j` by simultaneously resolving all `m`
     input clauses against `propClause j` (`hyperResolve` / `slideHyperResolve`).
   * At `S = m`, `hyperRes_kmm_recomputation_lower_bound` proves
     `2 * m - 1 ≤ c * macroRecoverySteps (hyperResBoundedInc m m c) P.trace` and
     `2 * m - 1 ≤ c * (P.steps - m)`.
   * At `S = m + 1` (with `c = 1`), `hyperRes_kmm_zero_recomp_at_m_plus_one` constructs an explicit
     zero-recomputation trace achieving `macroRecoverySteps = m` in `3 * m` steps, exhibiting a
     sharp 1-slot phase transition from `S = m` to `S = m + 1`.
   * For `S < m`, `hyperRes_infeasible_below_m` proves `IsEmpty (ValidHyperRes m S c)`.

3. **Part 3 (Explicit Obstruction: Unrestricted Binary Resolution at Clause Space `S = 3`)**:
   We define `BinaryResStep m S` and `ValidBinaryRes m S` using `DAGResolution.IsResolvent`,
   allowing standard two-premise binary resolution on `pebKmmCNF m`.
   * `binaryRes_pebKmm_space_three` constructively derives every `outClause j` in clause space
     `S = 3` for all `m ≥ 1` by incrementally resolving each `inClause i` into the width-`m`
     partial propagation clause `partialPropClause j k`, which acts as a bit-vector accumulator.
   * Consequently, for all `m ≥ 4`, `binaryRes_vs_hyperRes_separation` establishes
     `Nonempty (ValidBinaryRes m 3) ∧ IsEmpty (ValidHyperRes m 3 c)`: dropping the simultaneous
     hyper-resolution requirement destroys the `S = m` barrier completely.

## Epistemic Discipline (Six-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file — including
  `microTrace_valid`, `microTrace_psi_boundary`, `recoverySteps_microTrace_le`,
  `boundedInc_recomputation_lower_bound`, `hyperRes_kmm_recomputation_lower_bound`,
  `hyperRes_kmm_zero_recomp_at_m_plus_one`, `hyperRes_infeasible_below_m`,
  `binaryRes_pebKmm_space_three`, and `binaryRes_vs_hyperRes_separation` — are formally verified
  in Lean 4 with zero `sorry`s and no extra axioms.
* **Model-Restricted**: The recomputation lower bound in Part 2 applies strictly to the
  `BoundedHyperRes` model (requiring all `m` input clauses to be simultaneously present in memory
  to derive `outClause j`, with batch input-loading rate at most `c`). Part 3 explicitly proves
  that this restriction is load-bearing: unrestricted binary resolution (`ValidBinaryRes`) escapes
  the `S = m` barrier at `S = 3`.
* **Numerically Observed**: None; all bounds and constructions are symbolic in `m`, `S`, and `c`.
* **Conditional**: Transferring `BoundedIncSystem` lower bounds to other proof systems or solver
  architectures requires a sound potential `ψ` with bounded per-step increment `c` and forced
  potential drops at crossing events.
* **Heuristic / Structural Analogy**: `BoundedHyperRes` is structurally analogous to simultaneous
  pebbling / hyper-resolution inference rules, whereas `BinaryResStep` reflects why clause-space
  bounds for general resolution require wide-clause or width-space tradeoffs rather than naive
  unit-clause pebbling barriers.
* **Conjectural / Explicitly Not Claimed**: Lower bounds for general CDCL SAT solvers, general
  unrestricted resolution refutation size/space on arbitrary CNFs, circuit lower bounds, and
  `P ≠ NP` are **NOT** claimed or implied by this module.
-/

namespace Mathmatica.HyperResSimulation

open Mathmatica.SeparatorRecomputation
open Mathmatica.DAGResolution
open Mathmatica.BSWTradeoff

/-! ### Part 1: Generic `c`-Increment Micro-Step Simulation -/

/-- A deterministic transition system equipped with a potential `ψ` that increases by at most `c`
on every legal macro-step. -/
structure BoundedIncSystem (Q : Type*) (c : ℕ) where
  /-- Legal one-step macro-transition relation on states. -/
  Step : Q → Q → Prop
  /-- Potential function on states. -/
  ψ : Q → ℕ
  /-- Every legal macro-transition increases `ψ` by at most `c`. -/
  step_inc_le : ∀ {q₁ q₂ : Q}, Step q₁ q₂ → ψ q₂ ≤ ψ q₁ + c

/-- The set of macro-step indices `t : Fin T` along `tr` at which `B.ψ` strictly increases.
Idle macro-steps never belong to `macroRecoverySet`. -/
def macroRecoverySet {Q : Type*} {c : ℕ} (B : BoundedIncSystem Q c) {T : ℕ}
    (tr : Fin (T + 1) → Q) : Finset (Fin T) :=
  Finset.univ.filter (fun t : Fin T => B.ψ (tr t.castSucc) < B.ψ (tr t.succ))

/-- The number of strict potential-recovery macro-steps along `tr`. -/
def macroRecoverySteps {Q : Type*} {c : ℕ} (B : BoundedIncSystem Q c) {T : ℕ}
    (tr : Fin (T + 1) → Q) : ℕ :=
  (macroRecoverySet B tr).card

/-- An idle macro-step (`tr t.succ = tr t.castSucc`) is never a macro-recovery step. -/
theorem not_mem_macroRecoverySet_of_eq {Q : Type*} {c : ℕ} (B : BoundedIncSystem Q c) {T : ℕ}
    (tr : Fin (T + 1) → Q) (t : Fin T) (hidle : tr t.succ = tr t.castSucc) :
    t ∉ macroRecoverySet B tr := by
  simp [macroRecoverySet, hidle]

/-- Micro-step transition relation on `Q × ℕ` subdividing each `c`-increment macro-step into
unit-increment micro-steps: either ramp the auxiliary counter by at most `1` while staying at `q`,
or commit a legal macro-step `B.Step q₁ q₂` resetting the auxiliary counter to `0`. -/
inductive MicroStep {Q : Type*} {c : ℕ} (B : BoundedIncSystem Q c) :
    Q × ℕ → Q × ℕ → Prop where
  | ramp {q : Q} {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁ + 1) :
      MicroStep B (q, r₁) (q, r₂)
  | commit {q₁ q₂ : Q} {r : ℕ} (hstep : B.Step q₁ q₂)
      (hle : B.ψ q₂ ≤ B.ψ q₁ + r + 1) :
      MicroStep B (q₁, r) (q₂, 0)

/-- The unit-increment `SeparatorSystem (Q × ℕ)` induced by a `c`-increment system `B`. -/
def microSystem {Q : Type*} {c : ℕ} (B : BoundedIncSystem Q c) :
    SeparatorSystem (Q × ℕ) where
  Step := MicroStep B
  ψ := fun s => B.ψ s.1 + s.2
  step_inc_le_one := by
    intro s₁ s₂ h
    cases h with
    | ramp hr =>
      dsimp
      omega
    | commit _ hle =>
      dsimp
      omega

private theorem div_lt_of_lt_mul_left {a c T : ℕ} (h : a < c * T) : a / c < T :=
  Nat.div_lt_of_lt_mul h

/-- Subdivide a macro-trace `tr : Fin (T + 1) → Q` into a micro-trace of length `c * T + 1` by
ramping the auxiliary counter from `0` up to `min (c - 1) (ψ(tr (t+1)) - ψ(tr t))` during each
macro-step `t`, then committing to `(tr (t+1), 0)` at the next macro-boundary. -/
def microTrace {Q : Type*} {c T : ℕ} (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q) (s : Fin (c * T + 1)) : Q × ℕ :=
  if h : s.1 < c * T then
    let t : Fin T := ⟨s.1 / c, div_lt_of_lt_mul_left h⟩
    (tr t.castSucc, min (s.1 % c) (B.ψ (tr t.succ) - B.ψ (tr t.castSucc)))
  else
    have _ := hc
    (tr ⟨T, Nat.lt_succ_self T⟩, 0)

/-- At every macro-boundary `c * k`, `microTrace` agrees exactly with `(tr k, 0)`. -/
theorem microTrace_boundary {Q : Type*} {c T : ℕ} (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q) (k : Fin (T + 1)) :
    microTrace B hc tr ⟨c * k.1, Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ k.2))⟩ =
      (tr k, 0) := by
  unfold microTrace
  by_cases hk : k.1 < T
  · have hlt : c * k.1 < c * T := Nat.mul_lt_mul_of_pos_left hk (by omega)
    simp only [hlt, ↓reduceDIte]
    have hdiv : c * k.1 / c = k.1 := Nat.mul_div_right k.1 (by omega)
    have hmod : c * k.1 % c = 0 := Nat.mul_mod_right c k.1
    have hcast : (⟨c * k.1 / c, div_lt_of_lt_mul_left hlt⟩ : Fin T).castSucc = k := by
      ext
      simp [hdiv]
    rw [hcast, hmod]
    simp
  · have hkT : k.1 = T := by omega
    have hnot : ¬ c * k.1 < c * T := by rw [hkT]; exact Nat.lt_irrefl _
    simp only [hnot, ↓reduceDIte]
    have hkeq : (⟨T, Nat.lt_succ_self T⟩ : Fin (T + 1)) = k := Fin.ext hkT.symm
    rw [hkeq]

/-- At every macro-boundary `c * k`, the micro-potential equals the macro-potential `B.ψ (tr k)`. -/
theorem microTrace_psi_boundary {Q : Type*} {c T : ℕ} (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q) (k : Fin (T + 1)) :
    (microSystem B).ψ
      (microTrace B hc tr ⟨c * k.1, Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ k.2))⟩) =
      B.ψ (tr k) := by
  rw [microTrace_boundary]
  simp [microSystem]

/-- Every consecutive transition of `microTrace` is a legal `MicroStep` of `microSystem B`. -/
theorem microTrace_valid {Q : Type*} {c T : ℕ} (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, B.Step (tr t.castSucc) (tr t.succ)) :
    ∀ s : Fin (c * T),
      (microSystem B).Step (microTrace B hc tr s.castSucc) (microTrace B hc tr s.succ) := by
  intro s
  have hs_lt : s.1 < c * T := s.2
  let t : Fin T := ⟨s.1 / c, div_lt_of_lt_mul_left hs_lt⟩
  have hcur :
      microTrace B hc tr s.castSucc =
        (tr t.castSucc, min (s.1 % c) (B.ψ (tr t.succ) - B.ψ (tr t.castSucc))) := by
    unfold microTrace
    simp only [Fin.val_castSucc, hs_lt, ↓reduceDIte]
    rfl
  rw [hcur]
  by_cases hlast : s.1 % c + 1 < c
  · have hs1_lt : s.1 + 1 < c * T := by
      have hdm := Nat.div_add_mod s.1 c
      have hdiv_lt : s.1 / c < T := t.2
      have : c * (s.1 / c) + c ≤ c * T := by
        calc c * (s.1 / c) + c = c * (s.1 / c + 1) := by rw [Nat.mul_succ]
          _ ≤ c * T := Nat.mul_le_mul_left c hdiv_lt
      omega
    have hdiv1 : (s.1 + 1) / c = s.1 / c := by
      have hdm := Nat.div_add_mod s.1 c
      have heq : s.1 + 1 = (s.1 % c + 1) + c * (s.1 / c) := by omega
      rw [heq, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlast, Nat.zero_add]
    have hmod1 : (s.1 + 1) % c = s.1 % c + 1 := by
      have hdm := Nat.div_add_mod s.1 c
      have heq : s.1 + 1 = (s.1 % c + 1) + c * (s.1 / c) := by omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlast]
    have hnext :
        microTrace B hc tr s.succ =
          (tr t.castSucc, min (s.1 % c + 1) (B.ψ (tr t.succ) - B.ψ (tr t.castSucc))) := by
      unfold microTrace
      simp only [Fin.val_succ, hs1_lt, ↓reduceDIte]
      have ht_eq :
          (⟨(s.1 + 1) / c, div_lt_of_lt_mul_left hs1_lt⟩ : Fin T) = t := by
        ext
        exact hdiv1
      rw [ht_eq, hmod1]
    rw [hnext]
    exact MicroStep.ramp (by omega)
  · have hmod_eq : s.1 % c = c - 1 := by
      have hmod_lt : s.1 % c < c := Nat.mod_lt s.1 (by omega)
      omega
    have hs1_eq : s.1 + 1 = c * t.succ.1 := by
      have hdm := Nat.div_add_mod s.1 c
      have hts : t.succ.1 = s.1 / c + 1 := rfl
      rw [hts, Nat.mul_succ]
      omega
    have hnext : microTrace B hc tr s.succ = (tr t.succ, 0) := by
      have hfin :
          s.succ =
            ⟨c * t.succ.1, Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ t.succ.2))⟩ := by
        ext
        exact hs1_eq
      rw [hfin]
      exact microTrace_boundary B hc tr t.succ
    rw [hnext]
    have hinc := B.step_inc_le (hstep t)
    exact MicroStep.commit (hstep t) (by omega)

/-- Every micro-recovery step in `microTrace` lies within a macro-recovery step of `tr`, so the
number of micro-recovery steps is at most `c * macroRecoverySteps B tr`. -/
theorem recoverySteps_microTrace_le {Q : Type*} {c T : ℕ} (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q) :
    recoverySteps (microSystem B) (microTrace B hc tr) ≤ c * macroRecoverySteps B tr := by
  let f : Fin (c * T) → Fin T × Fin c := fun s =>
    (⟨s.1 / c, div_lt_of_lt_mul_left s.2⟩,
     ⟨s.1 % c, Nat.mod_lt s.1 (by omega)⟩)
  have hf_inj : Function.Injective f := by
    intro s₁ s₂ h
    have hdiv : s₁.1 / c = s₂.1 / c := congrArg (fun p => p.1.1) h
    have hmod : s₁.1 % c = s₂.1 % c := congrArg (fun p => p.2.1) h
    have h1 := Nat.div_add_mod s₁.1 c
    have h2 := Nat.div_add_mod s₂.1 c
    rw [hdiv, hmod] at h1
    ext
    omega
  have hf_maps :
      ∀ s ∈ recoverySet (microSystem B) (microTrace B hc tr),
        f s ∈ macroRecoverySet B tr ×ˢ (Finset.univ : Finset (Fin c)) := by
    intro s hs
    have hinc :
        (microSystem B).ψ (microTrace B hc tr s.castSucc) <
          (microSystem B).ψ (microTrace B hc tr s.succ) :=
      (Finset.mem_filter.mp hs).2
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [macroRecoverySet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hs_lt : s.1 < c * T := s.2
    let t : Fin T := ⟨s.1 / c, div_lt_of_lt_mul_left hs_lt⟩
    have hcur :
        microTrace B hc tr s.castSucc =
          (tr t.castSucc, min (s.1 % c) (B.ψ (tr t.succ) - B.ψ (tr t.castSucc))) := by
      unfold microTrace
      simp only [Fin.val_castSucc, hs_lt, ↓reduceDIte]
      rfl
    rw [hcur] at hinc
    by_cases hlast : s.1 % c + 1 < c
    · have hs1_lt : s.1 + 1 < c * T := by
        have hdm := Nat.div_add_mod s.1 c
        have hdiv_lt : s.1 / c < T := t.2
        have : c * (s.1 / c) + c ≤ c * T := by
          calc c * (s.1 / c) + c = c * (s.1 / c + 1) := by rw [Nat.mul_succ]
            _ ≤ c * T := Nat.mul_le_mul_left c hdiv_lt
        omega
      have hdiv1 : (s.1 + 1) / c = s.1 / c := by
        have hdm := Nat.div_add_mod s.1 c
        have heq : s.1 + 1 = (s.1 % c + 1) + c * (s.1 / c) := by omega
        rw [heq, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlast, Nat.zero_add]
      have hmod1 : (s.1 + 1) % c = s.1 % c + 1 := by
        have hdm := Nat.div_add_mod s.1 c
        have heq : s.1 + 1 = (s.1 % c + 1) + c * (s.1 / c) := by omega
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlast]
      have hnext :
          microTrace B hc tr s.succ =
            (tr t.castSucc, min (s.1 % c + 1) (B.ψ (tr t.succ) - B.ψ (tr t.castSucc))) := by
        unfold microTrace
        simp only [Fin.val_succ, hs1_lt, ↓reduceDIte]
        have ht_eq :
            (⟨(s.1 + 1) / c, div_lt_of_lt_mul_left hs1_lt⟩ : Fin T) = t := by
          ext
          exact hdiv1
        rw [ht_eq, hmod1]
      rw [hnext] at hinc
      dsimp only [microSystem] at hinc
      change B.ψ (tr t.castSucc) < B.ψ (tr t.succ)
      omega
    · have hmod_eq : s.1 % c = c - 1 := by
        have hmod_lt : s.1 % c < c := Nat.mod_lt s.1 (by omega)
        omega
      have hs1_eq : s.1 + 1 = c * t.succ.1 := by
        have hdm := Nat.div_add_mod s.1 c
        have hts : t.succ.1 = s.1 / c + 1 := rfl
        rw [hts, Nat.mul_succ]
        omega
      have hnext : microTrace B hc tr s.succ = (tr t.succ, 0) := by
        have hfin :
            s.succ =
              ⟨c * t.succ.1, Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ t.succ.2))⟩ := by
          ext
          exact hs1_eq
        rw [hfin]
        exact microTrace_boundary B hc tr t.succ
      rw [hnext] at hinc
      dsimp only [microSystem] at hinc
      change B.ψ (tr t.castSucc) < B.ψ (tr t.succ)
      omega
  calc
    recoverySteps (microSystem B) (microTrace B hc tr)
        = (recoverySet (microSystem B) (microTrace B hc tr)).card := rfl
    _ ≤ (macroRecoverySet B tr ×ˢ (Finset.univ : Finset (Fin c))).card :=
        Finset.card_le_card_of_injOn f hf_maps (fun _ _ _ _ h => hf_inj h)
    _ = macroRecoverySteps B tr * c := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, macroRecoverySteps]
    _ = c * macroRecoverySteps B tr := Nat.mul_comm _ _

/-- **Abstract `c`-Increment Separator Recovery Lower Bound**:
If a legal trace of a `c`-increment system (`1 ≤ c`) starts at `B.ψ (tr 0) = 0` and has `k ≥ 1`
strictly ordered crossing steps `cross : Fin k → Fin T` where `m ≤ B.ψ (tr (cross j).castSucc)`
and `B.ψ (tr (cross j).succ) ≤ m - drop` (with `drop ≤ m`), then:
1. `m + (k - 1) * drop ≤ c * macroRecoverySteps B tr`; and
2. `m + (k - 1) * drop ≤ c * (T - k)` (with `macroRecoverySteps B tr + k ≤ T`). -/
theorem boundedInc_recomputation_lower_bound {Q : Type*} {c T : ℕ}
    (B : BoundedIncSystem Q c) (hc : 1 ≤ c)
    (tr : Fin (T + 1) → Q)
    (hstep : ∀ t : Fin T, B.Step (tr t.castSucc) (tr t.succ))
    {k m drop : ℕ} (hk : 1 ≤ k) (hdrop : drop ≤ m)
    (hinit : B.ψ (tr 0) = 0)
    (cross : Fin k → Fin T) (hmono : StrictMono cross)
    (hfull : ∀ j : Fin k, m ≤ B.ψ (tr (cross j).castSucc))
    (hdrop_after : ∀ j : Fin k, B.ψ (tr (cross j).succ) ≤ m - drop) :
    m + (k - 1) * drop ≤ c * macroRecoverySteps B tr ∧
      m + (k - 1) * drop ≤ c * (T - k) := by
  let microCross : Fin k → Fin (c * T) := fun j =>
    ⟨c * (cross j).1 + (c - 1), by
      have hlt : (cross j).1 < T := (cross j).2
      have hmul : c * ((cross j).1 + 1) ≤ c * T := Nat.mul_le_mul_left c hlt
      rw [Nat.mul_succ] at hmul
      omega⟩
  have hmicro_mono : StrictMono microCross := by
    intro j₁ j₂ hlt
    show (microCross j₁).1 < (microCross j₂).1
    have hclt : (cross j₁).1 < (cross j₂).1 := hmono hlt
    have hmul : c * ((cross j₁).1 + 1) ≤ c * (cross j₂).1 := Nat.mul_le_mul_left c hclt
    rw [Nat.mul_succ] at hmul
    dsimp only [microCross]
    omega
  have hmicro_init : (microSystem B).ψ (microTrace B hc tr 0) = 0 := by
    have h0 : (0 : Fin (c * T + 1)) =
        ⟨c * (0 : Fin (T + 1)).1, Nat.lt_succ_of_le (Nat.zero_le _)⟩ := by
      ext
      simp
    rw [h0, microTrace_psi_boundary]
    exact hinit
  have hmicro_full :
      ∀ j : Fin k, m ≤ (microSystem B).ψ (microTrace B hc tr (microCross j).castSucc) := by
    intro j
    have hs_lt : (microCross j).1 < c * T := (microCross j).2
    have hdiv : (microCross j).1 / c = (cross j).1 := by
      dsimp only [microCross]
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    have hcur :
        microTrace B hc tr (microCross j).castSucc =
          (tr (cross j).castSucc,
            min ((microCross j).1 % c)
              (B.ψ (tr (cross j).succ) - B.ψ (tr (cross j).castSucc))) := by
      unfold microTrace
      simp only [Fin.val_castSucc, hs_lt, ↓reduceDIte]
      have ht_eq :
          (⟨(microCross j).1 / c, div_lt_of_lt_mul_left hs_lt⟩ : Fin T) =
            cross j := Fin.ext hdiv
      rw [ht_eq]
    rw [hcur]
    dsimp only [microSystem]
    have hf := hfull j
    omega
  have hmicro_drop :
      ∀ j : Fin k, (microSystem B).ψ (microTrace B hc tr (microCross j).succ) ≤ m - drop := by
    intro j
    have hfin :
        (microCross j).succ =
          ⟨c * (cross j).succ.1,
            Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ (cross j).succ.2))⟩ := by
      ext
      dsimp only [microCross]
      simp only [Fin.val_succ, Nat.mul_succ]
      omega
    rw [hfin, microTrace_psi_boundary]
    exact hdrop_after j
  have hmicro_lb :=
    recomputationLowerBound_of_separator
      (microSystem B) (microTrace B hc tr) (microTrace_valid B hc tr hstep)
      hk hdrop hmicro_init microCross hmicro_mono hmicro_full hmicro_drop
  have hrec_le := recoverySteps_microTrace_le B hc tr
  have hrec_lb : m + (k - 1) * drop ≤ c * macroRecoverySteps B tr :=
    le_trans hmicro_lb.1 hrec_le
  let C : Finset (Fin T) := Finset.univ.image cross
  have hC_card : C.card = k := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (macroRecoverySet B tr) C := by
    rw [Finset.disjoint_left]
    intro t ht_rec ht_C
    rcases Finset.mem_image.mp ht_C with ⟨j, _, rfl⟩
    have hinc : B.ψ (tr (cross j).castSucc) < B.ψ (tr (cross j).succ) :=
      (Finset.mem_filter.mp ht_rec).2
    have hf := hfull j
    have hd := hdrop_after j
    omega
  have hmacro_sum : macroRecoverySteps B tr + k ≤ T := by
    calc macroRecoverySteps B tr + k
        = (macroRecoverySet B tr).card + C.card := by rw [macroRecoverySteps, hC_card]
      _ = (macroRecoverySet B tr ∪ C).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = T := by rw [Finset.card_univ, Fintype.card_fin]
  have hrec_le_sub : macroRecoverySteps B tr ≤ T - k := by omega
  exact ⟨hrec_lb, le_trans hrec_lb (Nat.mul_le_mul_left c hrec_le_sub)⟩

/-! ### Part 2: `BoundedHyperRes m S c` on `pebKmmCNF m` -/

/-- Input variable `x_i` (`0 ≤ i < m`) in the `2 * m`-variable encoding of `K_{m, m}`. -/
def inVar {m : ℕ} (i : Fin m) : Fin (2 * m) :=
  ⟨i.1, by omega⟩

/-- Output variable `y_j` (`m ≤ m + j < 2 * m`) in the `2 * m`-variable encoding of `K_{m, m}`. -/
def outVar {m : ℕ} (j : Fin m) : Fin (2 * m) :=
  ⟨m + j.1, by omega⟩

/-- Unit input clause `{x_i}` asserting that input `i` is pebbled. -/
def inClause {m : ℕ} (i : Fin m) : Clause (2 * m) :=
  {Lit.mk (inVar i) true}

/-- Unit output clause `{y_j}` asserting that output `j` is pebbled. -/
def outClause {m : ℕ} (j : Fin m) : Clause (2 * m) :=
  {Lit.mk (outVar j) true}

/-- Propagation clause `(⋁_i ¬x_i) ∨ y_j` encoding that output `y_j` depends on all `m` inputs. -/
def propClause {m : ℕ} (j : Fin m) : Clause (2 * m) :=
  insert (Lit.mk (outVar j) true)
    (Finset.univ.image (fun i : Fin m => Lit.mk (inVar i) false))

/-- The `K_{m, m}` pebbling CNF formula consisting of all `m` unit input clauses `{x_i}` and all
`m` propagation clauses `(⋁_i ¬x_i) ∨ y_j`. -/
def pebKmmCNF (m : ℕ) : CNF (2 * m) :=
  Finset.univ.image (inClause (m := m)) ∪ Finset.univ.image (propClause (m := m))

/-- The set of all `m` unit input clauses `{x_0}, ..., {x_{m-1}}`. -/
def allInClauses (m : ℕ) : Finset (Clause (2 * m)) :=
  Finset.univ.image (inClause (m := m))

theorem inVar_injective {m : ℕ} : Function.Injective (inVar (m := m)) := by
  intro i₁ i₂ h
  exact Fin.ext (by simpa [inVar] using congrArg Fin.val h)

theorem outVar_injective {m : ℕ} : Function.Injective (outVar (m := m)) := by
  intro j₁ j₂ h
  have hval : m + j₁.1 = m + j₂.1 := by simpa [outVar] using congrArg Fin.val h
  exact Fin.ext (by omega)

theorem inVar_ne_outVar {m : ℕ} (i j : Fin m) : inVar i ≠ outVar j := by
  intro h
  have hval : i.1 = m + j.1 := by simpa [inVar, outVar] using congrArg Fin.val h
  omega

theorem inClause_injective {m : ℕ} : Function.Injective (inClause (m := m)) := by
  intro i₁ i₂ h
  have hmem : Lit.mk (inVar i₁) true ∈ inClause i₂ := by
    rw [← h]
    exact Finset.mem_singleton_self _
  have hlit : Lit.mk (inVar i₁) true = Lit.mk (inVar i₂) true := Finset.mem_singleton.mp hmem
  exact inVar_injective (congrArg Lit.var hlit)

theorem outClause_injective {m : ℕ} : Function.Injective (outClause (m := m)) := by
  intro j₁ j₂ h
  have hmem : Lit.mk (outVar j₁) true ∈ outClause j₂ := by
    rw [← h]
    exact Finset.mem_singleton_self _
  have hlit : Lit.mk (outVar j₁) true = Lit.mk (outVar j₂) true := Finset.mem_singleton.mp hmem
  exact outVar_injective (congrArg Lit.var hlit)

theorem inClause_ne_outClause {m : ℕ} (i j : Fin m) : inClause i ≠ outClause j := by
  intro h
  have hmem : Lit.mk (inVar i) true ∈ outClause j := by
    rw [← h]
    exact Finset.mem_singleton_self _
  have hlit : Lit.mk (inVar i) true = Lit.mk (outVar j) true := Finset.mem_singleton.mp hmem
  exact inVar_ne_outVar i j (congrArg Lit.var hlit)

theorem card_allInClauses (m : ℕ) : (allInClauses m).card = m := by
  rw [allInClauses, Finset.card_image_of_injective _ inClause_injective,
    Finset.card_univ, Fintype.card_fin]

theorem outClause_not_mem_allInClauses {m : ℕ} (j : Fin m) :
    outClause j ∉ allInClauses m := by
  intro h
  rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
  exact inClause_ne_outClause i j hi

/-- Number of unit input clauses currently held in memory `M`. -/
def hyperResInputCount {m : ℕ} (M : Finset (Clause (2 * m))) : ℕ :=
  (M ∩ allInClauses m).card

theorem hyperResInputCount_empty (m : ℕ) :
    hyperResInputCount (∅ : Finset (Clause (2 * m))) = 0 := by
  simp [hyperResInputCount]

theorem hyperResInputCount_ge_of_allInClauses_subset {m : ℕ} {M : Finset (Clause (2 * m))}
    (hin : allInClauses m ⊆ M) : m ≤ hyperResInputCount M := by
  have hsub : allInClauses m ⊆ M ∩ allInClauses m :=
    Finset.subset_inter hin Finset.Subset.rfl
  calc m = (allInClauses m).card := (card_allInClauses m).symm
    _ ≤ (M ∩ allInClauses m).card := Finset.card_le_card hsub

theorem hyperResInputCount_le_sub_one_of_outClause_mem {m : ℕ} {M : Finset (Clause (2 * m))}
    {j : Fin m} (hmem : outClause j ∈ M) (hcard : M.card ≤ m) :
    hyperResInputCount M ≤ m - 1 := by
  have hnot : outClause j ∉ M ∩ allInClauses m := by
    intro h
    exact outClause_not_mem_allInClauses j (Finset.mem_inter.mp h).2
  have hsub : insert (outClause j) (M ∩ allInClauses m) ⊆ M := by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC'
    · exact hmem
    · exact (Finset.mem_inter.mp hC').1
  have hle : hyperResInputCount M + 1 ≤ M.card := by
    rw [hyperResInputCount, ← Finset.card_insert_of_notMem hnot]
    exact Finset.card_le_card hsub
  omega

/-- Legal transitions of `BoundedHyperRes m S c` on `pebKmmCNF m`:
* `batchLoadInputs`: load up to `c` unit input clauses into memory simultaneously;
* `hyperResolve`: simultaneously resolve all `m` unit input clauses against `propClause j` to
  store `outClause j` (requiring `< S` clauses in memory);
* `slideHyperResolve`: simultaneously resolve all `m` unit input clauses against `propClause j` and
  overwrite one input clause `inClause i` with `outClause j`;
* `erase`: delete any clause from memory;
* `idle`: leave memory unchanged. -/
inductive HyperResStep (m S c : ℕ) :
    Finset (Clause (2 * m)) → Finset (Clause (2 * m)) → Prop where
  | batchLoadInputs {M B : Finset (Clause (2 * m))}
      (hBsub : B ⊆ allInClauses m) (hBcard : B.card ≤ c)
      (hM : M.card ≤ S) (hU : (M ∪ B).card ≤ S) :
      HyperResStep m S c M (M ∪ B)
  | hyperResolve {M : Finset (Clause (2 * m))} (j : Fin m)
      (hin : allInClauses m ⊆ M) (hcard : M.card < S) :
      HyperResStep m S c M (insert (outClause j) M)
  | slideHyperResolve {M : Finset (Clause (2 * m))} (i j : Fin m)
      (hin : allInClauses m ⊆ M) (hcard : M.card ≤ S) :
      HyperResStep m S c M (insert (outClause j) (M.erase (inClause i)))
  | erase {M : Finset (Clause (2 * m))} (C : Clause (2 * m)) (hcard : M.card ≤ S) :
      HyperResStep m S c M (M.erase C)
  | idle {M : Finset (Clause (2 * m))} (hcard : M.card ≤ S) :
      HyperResStep m S c M M

theorem hyperResStep_inputCount_le_add {m S c : ℕ} {M₁ M₂ : Finset (Clause (2 * m))}
    (h : HyperResStep m S c M₁ M₂) :
    hyperResInputCount M₂ ≤ hyperResInputCount M₁ + c := by
  cases h with
  | @batchLoadInputs B _ hBcard _ _ =>
    unfold hyperResInputCount
    have hsub : (M₁ ∪ B) ∩ allInClauses m ⊆ (M₁ ∩ allInClauses m) ∪ B := by
      intro C hC
      rcases Finset.mem_inter.mp hC with ⟨hU, hA⟩
      rcases Finset.mem_union.mp hU with hM | hB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hM, hA⟩)
      · exact Finset.mem_union_right _ hB
    calc ((M₁ ∪ B) ∩ allInClauses m).card
        ≤ ((M₁ ∩ allInClauses m) ∪ B).card := Finset.card_le_card hsub
      _ ≤ (M₁ ∩ allInClauses m).card + B.card := Finset.card_union_le _ _
      _ ≤ (M₁ ∩ allInClauses m).card + c := Nat.add_le_add_left hBcard _
  | hyperResolve j _ _ =>
    unfold hyperResInputCount
    have heq : insert (outClause j) M₁ ∩ allInClauses m = M₁ ∩ allInClauses m := by
      ext C
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hM, hA⟩
        · exact absurd hA (outClause_not_mem_allInClauses j)
        · exact ⟨hM, hA⟩
      · rintro ⟨hM, hA⟩
        exact ⟨Or.inr hM, hA⟩
    rw [heq]
    omega
  | slideHyperResolve i j _ _ =>
    unfold hyperResInputCount
    have hsub : insert (outClause j) (M₁.erase (inClause i)) ∩ allInClauses m ⊆
        M₁ ∩ allInClauses m := by
      intro C hC
      rcases Finset.mem_inter.mp hC with ⟨hins, hA⟩
      rcases Finset.mem_insert.mp hins with rfl | her
      · exact absurd hA (outClause_not_mem_allInClauses j)
      · exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase her, hA⟩
    exact le_trans (Finset.card_le_card hsub) (Nat.le_add_right _ c)
  | erase C _ =>
    unfold hyperResInputCount
    have hsub : M₁.erase C ∩ allInClauses m ⊆ M₁ ∩ allInClauses m :=
      Finset.inter_subset_inter_right (Finset.erase_subset C M₁)
    exact le_trans (Finset.card_le_card hsub) (Nat.le_add_right _ c)
  | idle _ =>
    omega

/-- The `BoundedIncSystem` induced by `HyperResStep m S c` and the input-clause potential
`hyperResInputCount`. -/
def hyperResBoundedInc (m S c : ℕ) : BoundedIncSystem (Finset (Clause (2 * m))) c where
  Step := HyperResStep m S c
  ψ := hyperResInputCount
  step_inc_le := hyperResStep_inputCount_le_add

/-- Any `HyperResStep` that introduces a newly derived output clause `outClause j` must start from
a memory containing all `m` unit input clauses, and can introduce no other new output clause. -/
theorem hyperResStep_new_output {m S c : ℕ} {M₁ M₂ : Finset (Clause (2 * m))}
    (h : HyperResStep m S c M₁ M₂) {j : Fin m}
    (hnot : outClause j ∉ M₁) (hin : outClause j ∈ M₂) :
    allInClauses m ⊆ M₁ ∧
      ∀ j' : Fin m, outClause j' ∉ M₁ → outClause j' ∈ M₂ → j' = j := by
  cases h with
  | batchLoadInputs hBsub _ _ _ =>
    rcases Finset.mem_union.mp hin with hM | hB
    · exact absurd hM hnot
    · exact absurd (hBsub hB) (outClause_not_mem_allInClauses j)
  | hyperResolve j₀ hinputs _ =>
    rcases Finset.mem_insert.mp hin with hEq | hM
    · have hj : j = j₀ := outClause_injective hEq
      subst hj
      refine ⟨hinputs, fun j' hnot' hin' => ?_⟩
      rcases Finset.mem_insert.mp hin' with hEq' | hM'
      · exact outClause_injective hEq'
      · exact absurd hM' hnot'
    · exact absurd hM hnot
  | slideHyperResolve i j₀ hinputs _ =>
    rcases Finset.mem_insert.mp hin with hEq | hM
    · have hj : j = j₀ := outClause_injective hEq
      subst hj
      refine ⟨hinputs, fun j' hnot' hin' => ?_⟩
      rcases Finset.mem_insert.mp hin' with hEq' | hM'
      · exact outClause_injective hEq'
      · exact absurd (Finset.mem_of_mem_erase hM') hnot'
    · exact absurd (Finset.mem_of_mem_erase hM) hnot
  | erase C _ =>
    exact absurd (Finset.mem_of_mem_erase hin) hnot
  | idle _ =>
    exact absurd hin hnot

/-- A valid `BoundedHyperRes m S c` derivation of all `m` outputs `outClause j` of `pebKmmCNF m`
using clause space at most `S` and batch input-loading rate at most `c`. -/
structure ValidHyperRes (m S c : ℕ) where
  /-- Total number of macro-steps. -/
  steps : ℕ
  /-- Sequence of memory configurations of length `steps + 1`. -/
  trace : Fin (steps + 1) → Finset (Clause (2 * m))
  /-- Memory starts empty. -/
  init_empty : trace 0 = ∅
  /-- Every memory configuration has at most `S` clauses. -/
  space_le : ∀ t : Fin (steps + 1), (trace t).card ≤ S
  /-- Every consecutive transition is a legal `HyperResStep`. -/
  valid_step : ∀ t : Fin steps, HyperResStep m S c (trace t.castSucc) (trace t.succ)
  /-- Every output clause `outClause j` is derived at least once along the trace. -/
  outputs_derived : ∀ j : Fin m, ∃ t : Fin (steps + 1), outClause j ∈ trace t

private theorem exists_first_output_time_hyper {m S c : ℕ} (P : ValidHyperRes m S c) (j : Fin m) :
    ∃ n : ℕ, ∃ hn : n < P.steps + 1, outClause j ∈ P.trace ⟨n, hn⟩ := by
  rcases P.outputs_derived j with ⟨t, ht⟩
  exact ⟨t.1, t.2, ht⟩

/-- The step index `t : Fin P.steps` at which `outClause j` is derived for the very first time. -/
noncomputable def firstOutStepHyper {m S c : ℕ} (P : ValidHyperRes m S c) (j : Fin m) :
    Fin P.steps :=
  let n := Nat.find (exists_first_output_time_hyper P j)
  have hspec : ∃ hn : n < P.steps + 1, outClause j ∈ P.trace ⟨n, hn⟩ :=
    Nat.find_spec (exists_first_output_time_hyper P j)
  have hn_pos : 0 < n := by
    rcases hspec with ⟨hn, hmem⟩
    by_contra h0
    have hn0 : n = 0 := by omega
    have h0_eq : (⟨n, hn⟩ : Fin (P.steps + 1)) = 0 := Fin.ext hn0
    rw [h0_eq, P.init_empty] at hmem
    simp at hmem
  ⟨n - 1, by rcases hspec with ⟨hn, _⟩; omega⟩

private theorem firstOutStepHyper_spec {m S c : ℕ} (P : ValidHyperRes m S c) (j : Fin m) :
    outClause j ∉ P.trace (firstOutStepHyper P j).castSucc ∧
      outClause j ∈ P.trace (firstOutStepHyper P j).succ := by
  classical
  dsimp only [firstOutStepHyper]
  set n := Nat.find (exists_first_output_time_hyper P j)
  have hspec : ∃ hn : n < P.steps + 1, outClause j ∈ P.trace ⟨n, hn⟩ :=
    Nat.find_spec (exists_first_output_time_hyper P j)
  rcases hspec with ⟨hn, hmem⟩
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    have h0_eq : (⟨n, hn⟩ : Fin (P.steps + 1)) = 0 := Fin.ext hn0
    rw [h0_eq, P.init_empty] at hmem
    simp at hmem
  have hlt : n - 1 < n := by omega
  have hnot_prev : outClause j ∉ P.trace ⟨n - 1, by omega⟩ := by
    intro hprev
    exact Nat.find_min (exists_first_output_time_hyper P j) hlt ⟨by omega, hprev⟩
  refine ⟨hnot_prev, ?_⟩
  convert hmem using 2
  ext
  simp only [Fin.val_succ]
  omega

private theorem firstOutStepHyper_injective {m S c : ℕ} (P : ValidHyperRes m S c) :
    Function.Injective (firstOutStepHyper P) := by
  intro j₁ j₂ heq
  have h1 := firstOutStepHyper_spec P j₁
  have h2 := firstOutStepHyper_spec P j₂
  rw [heq] at h1
  have hnew := hyperResStep_new_output (P.valid_step (firstOutStepHyper P j₂)) h2.1 h2.2
  exact hnew.2 j₁ h1.1 h1.2

/-- **Infeasibility Below `S = m`**:
For `m ≥ 1` and `S < m`, no valid `BoundedHyperRes m S c` derivation of `pebKmmCNF m` exists,
because deriving even one output clause requires all `m` input clauses simultaneously in memory. -/
theorem hyperRes_infeasible_below_m {m S c : ℕ} (hm : 1 ≤ m) (hS : S < m) :
    IsEmpty (ValidHyperRes m S c) := by
  refine ⟨fun P => ?_⟩
  let j₀ : Fin m := ⟨0, hm⟩
  have hspec := firstOutStepHyper_spec P j₀
  have hnew := hyperResStep_new_output (P.valid_step (firstOutStepHyper P j₀)) hspec.1 hspec.2
  have hle : m ≤ (P.trace (firstOutStepHyper P j₀).castSucc).card := by
    calc m = (allInClauses m).card := (card_allInClauses m).symm
      _ ≤ (P.trace (firstOutStepHyper P j₀).castSucc).card := Finset.card_le_card hnew.1
  have hsp := P.space_le (firstOutStepHyper P j₀).castSucc
  omega

/-- **Forced Recomputation Lower Bound for `BoundedHyperRes` at `S = m`**:
For every `m ≥ 1`, `c ≥ 1`, and valid `BoundedHyperRes m m c` derivation `P`, the micro-step
simulation forces `2 * m - 1 ≤ c * macroRecoverySteps` and `2 * m - 1 ≤ c * (P.steps - m)`. -/
theorem hyperRes_kmm_recomputation_lower_bound {m c : ℕ} (hm : 1 ≤ m) (hc : 1 ≤ c)
    (P : ValidHyperRes m m c) :
    2 * m - 1 ≤ c * macroRecoverySteps (hyperResBoundedInc m m c) P.trace ∧
      2 * m - 1 ≤ c * (P.steps - m) := by
  classical
  let S_cross : Finset (Fin P.steps) := Finset.univ.image (firstOutStepHyper P)
  have hcard : S_cross.card = m := by
    rw [Finset.card_image_of_injective _ (firstOutStepHyper_injective P),
      Finset.card_univ, Fintype.card_fin]
  let cross : Fin m → Fin P.steps := S_cross.orderEmbOfFin hcard
  have hmono : StrictMono cross := (S_cross.orderEmbOfFin hcard).strictMono
  have hfull : ∀ r : Fin m, m ≤ hyperResInputCount (P.trace (cross r).castSucc) := by
    intro r
    have hmem : cross r ∈ S_cross := Finset.orderEmbOfFin_mem S_cross hcard r
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    rw [← hj]
    have hspec := firstOutStepHyper_spec P j
    have hnew := hyperResStep_new_output (P.valid_step (firstOutStepHyper P j)) hspec.1 hspec.2
    exact hyperResInputCount_ge_of_allInClauses_subset hnew.1
  have hdrop_after : ∀ r : Fin m, hyperResInputCount (P.trace (cross r).succ) ≤ m - 1 := by
    intro r
    have hmem : cross r ∈ S_cross := Finset.orderEmbOfFin_mem S_cross hcard r
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    rw [← hj]
    have hspec := firstOutStepHyper_spec P j
    exact hyperResInputCount_le_sub_one_of_outClause_mem hspec.2 (P.space_le _)
  have hinit : (hyperResBoundedInc m m c).ψ (P.trace 0) = 0 := by
    simp [hyperResBoundedInc, P.init_empty, hyperResInputCount]
  have hmain := boundedInc_recomputation_lower_bound
    (hyperResBoundedInc m m c) hc P.trace P.valid_step hm hm hinit cross hmono hfull hdrop_after
  have heq : m + (m - 1) * 1 = 2 * m - 1 := by omega
  rw [heq] at hmain
  exact hmain

/-! ### Sharp Phase Transition at `S = m + 1` (Zero Recomputation) -/

private def prefixInClauses (m k : ℕ) : Finset (Clause (2 * m)) :=
  (Finset.univ.filter (fun i : Fin m => i.1 < k)).image (inClause (m := m))

private theorem prefixInClauses_zero (m : ℕ) : prefixInClauses m 0 = ∅ := by
  simp [prefixInClauses]

private theorem prefixInClauses_eq_all (m : ℕ) : prefixInClauses m m = allInClauses m := by
  ext C
  simp [prefixInClauses, allInClauses]

private theorem prefixInClauses_succ {m k : ℕ} (hk : k < m) :
    prefixInClauses m (k + 1) = prefixInClauses m k ∪ {inClause ⟨k, hk⟩} := by
  ext C
  simp only [prefixInClauses, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases heq : i.1 = k
    · right
      exact congrArg inClause (Fin.ext heq)
    · left
      exact ⟨i, by omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩

private theorem card_prefixInClauses {m k : ℕ} (hk : k ≤ m) :
    (prefixInClauses m k).card = k := by
  induction k with
  | zero => simp [prefixInClauses_zero]
  | succ k ih =>
    have hk' : k < m := by omega
    have hnot : inClause ⟨k, hk'⟩ ∉ prefixInClauses m k := by
      intro h
      rcases Finset.mem_image.mp h with ⟨i, hi, heq⟩
      have h1 : i = ⟨k, hk'⟩ := inClause_injective heq
      have h2 : i.1 < k := (Finset.mem_filter.mp hi).2
      rw [h1] at h2
      exact Nat.lt_irrefl k h2
    rw [prefixInClauses_succ hk', Finset.union_comm, Finset.singleton_union,
      Finset.card_insert_of_notMem hnot, ih (Nat.le_of_lt hk')]

private theorem hyperResInputCount_prefixInClauses {m k : ℕ} (hk : k ≤ m) :
    hyperResInputCount (prefixInClauses m k) = k := by
  have hsub : prefixInClauses m k ⊆ allInClauses m := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [hyperResInputCount, Finset.inter_eq_left.mpr hsub, card_prefixInClauses hk]

private theorem hyperResInputCount_allInClauses (m : ℕ) :
    hyperResInputCount (allInClauses m) = m := by
  rw [← prefixInClauses_eq_all]
  exact hyperResInputCount_prefixInClauses le_rfl

private theorem hyperResInputCount_insert_outClause_allInClauses {m : ℕ} (j : Fin m) :
    hyperResInputCount (insert (outClause j) (allInClauses m)) = m := by
  unfold hyperResInputCount
  have heq : insert (outClause j) (allInClauses m) ∩ allInClauses m = allInClauses m := by
    ext C
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Or.inr h, h⟩
  rw [heq, card_allInClauses]

private theorem card_filter_lt_fin {N m : ℕ} (hm : m ≤ N) :
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
With a single extra clause slot (`S = m + 1`) and `c = 1`, `pebKmmCNF m` admits a valid
`BoundedHyperRes` derivation achieving `macroRecoverySteps = m` (zero recomputation) in `3 * m`
steps: load all `m` input clauses once, then repeatedly hyper-resolve and erase each `outClause j`. -/
theorem hyperRes_kmm_zero_recomp_at_m_plus_one {m : ℕ} (hm : 1 ≤ m) :
    ∃ P : ValidHyperRes m (m + 1) 1,
      macroRecoverySteps (hyperResBoundedInc m (m + 1) 1) P.trace = m ∧
        P.steps = 3 * m := by
  have _ := hm
  let tr : Fin (3 * m + 1) → Finset (Clause (2 * m)) := fun t =>
    if hle : t.1 ≤ m then
      prefixInClauses m t.1
    else if _ : (t.1 - m) % 2 = 1 then
      insert (outClause ⟨(t.1 - m - 1) / 2, by omega⟩) (allInClauses m)
    else
      allInClauses m
  have hspace : ∀ t : Fin (3 * m + 1), (tr t).card ≤ m + 1 := by
    intro t
    dsimp only [tr]
    split_ifs with hle hodd
    · rw [card_prefixInClauses hle]
      omega
    · have hle_ins := Finset.card_insert_le
        (outClause ⟨(t.1 - m - 1) / 2, by omega⟩) (allInClauses m)
      rw [card_allInClauses] at hle_ins
      exact hle_ins
    · rw [card_allInClauses]
      omega
  have hstep : ∀ t : Fin (3 * m), HyperResStep m (m + 1) 1 (tr t.castSucc) (tr t.succ) := by
    intro t
    by_cases hlt : t.1 < m
    · have hle1 : t.castSucc.1 ≤ m := by simp; omega
      have hle2 : t.succ.1 ≤ m := by simp; omega
      have h1 : tr t.castSucc = prefixInClauses m t.1 := by
        dsimp only [tr]; simp only [hle1, ↓reduceDIte]; rfl
      have h2 : tr t.succ = prefixInClauses m t.1 ∪ {inClause ⟨t.1, hlt⟩} := by
        dsimp only [tr]; simp only [hle2, ↓reduceDIte]
        simpa using prefixInClauses_succ hlt
      rw [h1, h2]
      refine HyperResStep.batchLoadInputs ?_ ?_ ?_ ?_
      · intro C hC
        rw [Finset.mem_singleton.mp hC]
        exact Finset.mem_image.mpr ⟨⟨t.1, hlt⟩, Finset.mem_univ _, rfl⟩
      · simp
      · rw [card_prefixInClauses (Nat.le_of_lt hlt)]; omega
      · rw [← prefixInClauses_succ hlt, card_prefixInClauses (by omega)]; omega
    · by_cases heven : (t.1 - m) % 2 = 0
      · have h1 : tr t.castSucc = allInClauses m := by
          dsimp only [tr]
          by_cases heq : t.1 = m
          · have hle1 : t.castSucc.1 ≤ m := by simp; omega
            simp only [hle1, ↓reduceDIte]
            simpa [heq] using prefixInClauses_eq_all m
          · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
            have hne1 : (t.castSucc.1 - m) % 2 ≠ 1 := by simp; omega
            simp only [hgt1, hne1, ↓reduceDIte]
        have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
        have hodd2 : (t.succ.1 - m) % 2 = 1 := by simp; omega
        have h2 :
            tr t.succ = insert (outClause ⟨(t.succ.1 - m - 1) / 2, by omega⟩) (allInClauses m) := by
          dsimp only [tr]
          simp only [hgt2, hodd2, ↓reduceDIte]
        rw [h1, h2]
        exact HyperResStep.hyperResolve ⟨(t.succ.1 - m - 1) / 2, by omega⟩
          Finset.Subset.rfl (by rw [card_allInClauses]; omega)
      · have hgt1 : ¬ t.castSucc.1 ≤ m := by simp; omega
        have hodd1 : (t.castSucc.1 - m) % 2 = 1 := by simp; omega
        have hgt2 : ¬ t.succ.1 ≤ m := by simp; omega
        have hne2 : (t.succ.1 - m) % 2 ≠ 1 := by simp; omega
        let j : Fin m := ⟨(t.castSucc.1 - m - 1) / 2, by omega⟩
        have h1 : tr t.castSucc = insert (outClause j) (allInClauses m) := by
          dsimp only [tr]
          simp only [hgt1, hodd1, ↓reduceDIte]
          rfl
        have h2 : tr t.succ = (insert (outClause j) (allInClauses m)).erase (outClause j) := by
          dsimp only [tr]
          simp only [hgt2, hne2, ↓reduceDIte]
          rw [Finset.erase_insert (outClause_not_mem_allInClauses j)]
        rw [h1, h2]
        refine HyperResStep.erase (outClause j) ?_
        have hle_ins := Finset.card_insert_le (outClause j) (allInClauses m)
        rw [card_allInClauses] at hle_ins
        exact hle_ins
  have hout : ∀ j : Fin m, ∃ t : Fin (3 * m + 1), outClause j ∈ tr t := by
    intro j
    let t : Fin (3 * m + 1) := ⟨m + 2 * j.1 + 1, by omega⟩
    refine ⟨t, ?_⟩
    have hgt : ¬ t.1 ≤ m := by dsimp only [t]; omega
    have hodd : (t.1 - m) % 2 = 1 := by dsimp only [t]; omega
    have hdiv : (t.1 - m - 1) / 2 = j.1 := by dsimp only [t]; omega
    dsimp only [tr]
    simp only [hgt, hodd, ↓reduceDIte]
    have hjeq : (⟨(t.1 - m - 1) / 2, by omega⟩ : Fin m) = j := Fin.ext hdiv
    rw [hjeq]
    exact Finset.mem_insert_self _ _
  let P : ValidHyperRes m (m + 1) 1 :=
    { steps := 3 * m
      trace := tr
      init_empty := by
        dsimp only [tr]
        simp [prefixInClauses_zero]
      space_le := hspace
      valid_step := hstep
      outputs_derived := hout }
  have hpsi : ∀ t : Fin (3 * m + 1), hyperResInputCount (tr t) = min t.1 m := by
    intro t
    dsimp only [tr]
    split_ifs with hle hodd
    · rw [hyperResInputCount_prefixInClauses hle]
      omega
    · rw [hyperResInputCount_insert_outClause_allInClauses]
      omega
    · rw [hyperResInputCount_allInClauses]
      omega
  have hrec_set :
      macroRecoverySet (hyperResBoundedInc m (m + 1) 1) P.trace =
        Finset.univ.filter (fun t : Fin (3 * m) => t.1 < m) := by
    ext t
    simp only [macroRecoverySet, Finset.mem_filter, Finset.mem_univ, true_and]
    change hyperResInputCount (tr t.castSucc) < hyperResInputCount (tr t.succ) ↔ t.1 < m
    rw [hpsi, hpsi]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  refine ⟨P, ?_, rfl⟩
  rw [macroRecoverySteps, hrec_set]
  exact card_filter_lt_fin (by omega)

/-! ### Part 3: Explicit Obstruction — Unrestricted Binary Resolution at Clause Space `S = 3` -/

/-- Legal transitions of unrestricted binary resolution on `pebKmmCNF m` with clause space `S`,
using `DAGResolution.IsResolvent`. -/
inductive BinaryResStep (m S : ℕ) :
    Finset (Clause (2 * m)) → Finset (Clause (2 * m)) → Prop where
  | loadAxiom {M : Finset (Clause (2 * m))} (C : Clause (2 * m))
      (hax : C ∈ pebKmmCNF m) (hM : M.card ≤ S) (hins : (insert C M).card ≤ S) :
      BinaryResStep m S M (insert C M)
  | resolve {M : Finset (Clause (2 * m))} (C₁ C₂ C : Clause (2 * m))
      (h₁ : C₁ ∈ M) (h₂ : C₂ ∈ M) (hres : IsResolvent C₁ C₂ C)
      (hM : M.card ≤ S) (hins : (insert C M).card ≤ S) :
      BinaryResStep m S M (insert C M)
  | erase {M : Finset (Clause (2 * m))} (C : Clause (2 * m)) (hM : M.card ≤ S) :
      BinaryResStep m S M (M.erase C)
  | idle {M : Finset (Clause (2 * m))} (hM : M.card ≤ S) :
      BinaryResStep m S M M

/-- A valid unrestricted binary resolution derivation of all `m` output clauses `outClause j`
from `pebKmmCNF m` in clause space at most `S`. -/
structure ValidBinaryRes (m S : ℕ) where
  /-- Total number of binary resolution steps. -/
  steps : ℕ
  /-- Sequence of clause memories of length `steps + 1`. -/
  trace : Fin (steps + 1) → Finset (Clause (2 * m))
  /-- Memory starts empty. -/
  init_empty : trace 0 = ∅
  /-- Every memory configuration holds at most `S` clauses. -/
  space_le : ∀ t : Fin (steps + 1), (trace t).card ≤ S
  /-- Every consecutive transition is a legal `BinaryResStep`. -/
  valid_step : ∀ t : Fin steps, BinaryResStep m S (trace t.castSucc) (trace t.succ)
  /-- Every output clause `outClause j` is derived at least once along the trace. -/
  outputs_derived : ∀ j : Fin m, ∃ t : Fin (steps + 1), outClause j ∈ trace t

/-- Partial propagation clause `(⋁_{i ≥ k} ¬x_i) ∨ y_j` after resolving away the first `k` input
literals of `propClause j`. -/
def partialPropClause {m : ℕ} (j : Fin m) (k : ℕ) : Clause (2 * m) :=
  insert (Lit.mk (outVar j) true)
    ((Finset.univ.filter (fun i : Fin m => k ≤ i.1)).image (fun i : Fin m => Lit.mk (inVar i) false))

theorem partialPropClause_zero {m : ℕ} (j : Fin m) :
    partialPropClause j 0 = propClause j := by
  ext l
  simp [partialPropClause, propClause]

theorem partialPropClause_eq_outClause {m : ℕ} (j : Fin m) :
    partialPropClause j m = outClause j := by
  ext l
  simp only [partialPropClause, outClause, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · rfl
    · omega
  · intro h
    exact Or.inl h

theorem isResolvent_inClause_partialPropClause {m : ℕ} (j : Fin m) {k : ℕ} (hk : k < m) :
    IsResolvent (inClause ⟨k, hk⟩) (partialPropClause j k) (partialPropClause j (k + 1)) := by
  refine ⟨inVar ⟨k, hk⟩, Finset.mem_singleton_self _, ?_, ?_⟩
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩
  · ext l
    simp only [inClause, partialPropClause, Finset.erase_singleton, Finset.empty_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · refine ⟨?_, Or.inl rfl⟩
        intro h
        exact inVar_ne_outVar ⟨k, hk⟩ j (congrArg Lit.var h).symm
      · refine ⟨?_, Or.inr ⟨i, by omega, rfl⟩⟩
        intro h
        have hi_eq : i = ⟨k, hk⟩ := inVar_injective (congrArg Lit.var h)
        have hi_val : i.1 = k := congrArg Fin.val hi_eq
        omega
    · rintro ⟨hne, rfl | ⟨i, hi, rfl⟩⟩
      · exact Or.inl rfl
      · right
        refine ⟨i, ?_, rfl⟩
        by_contra hlt
        have hi_eq : i = ⟨k, hk⟩ := Fin.ext (by dsimp; omega)
        exact hne (by rw [hi_eq])

private theorem partialPropClause_ne_inClause {m : ℕ} (j : Fin m) (k : ℕ) (i : Fin m) :
    partialPropClause j k ≠ inClause i := by
  intro h
  have hmem : Lit.mk (outVar j) true ∈ inClause i := by
    rw [← h]
    exact Finset.mem_insert_self _ _
  have hlit : Lit.mk (outVar j) true = Lit.mk (inVar i) true := Finset.mem_singleton.mp hmem
  exact inVar_ne_outVar i j (congrArg Lit.var hlit).symm

private theorem partialPropClause_ne_succ {m : ℕ} (j : Fin m) {k : ℕ} (hk : k < m) :
    partialPropClause j k ≠ partialPropClause j (k + 1) := by
  intro h
  have hmem : Lit.mk (inVar ⟨k, hk⟩) false ∈ partialPropClause j (k + 1) := by
    rw [← h]
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩
  rcases Finset.mem_insert.mp hmem with hlit | himg
  · exact inVar_ne_outVar ⟨k, hk⟩ j (congrArg Lit.var hlit)
  · rcases Finset.mem_image.mp himg with ⟨i, hi, hlit⟩
    have hi_eq : i = ⟨k, hk⟩ := inVar_injective (congrArg Lit.var hlit)
    have hge : k + 1 ≤ i.1 := (Finset.mem_filter.mp hi).2
    have hi_val : i.1 = k := congrArg Fin.val hi_eq
    omega

/-- A composable segment of a valid `BinaryResStep m S` trace from `M₁` to `M₂`. -/
private structure BinaryResSeg (m S : ℕ) (M₁ M₂ : Finset (Clause (2 * m))) where
  steps : ℕ
  trace : Fin (steps + 1) → Finset (Clause (2 * m))
  start_eq : trace 0 = M₁
  end_eq : trace ⟨steps, Nat.lt_succ_self steps⟩ = M₂
  space_le : ∀ t : Fin (steps + 1), (trace t).card ≤ S
  valid_step : ∀ t : Fin steps, BinaryResStep m S (trace t.castSucc) (trace t.succ)

private def BinaryResSeg.refl {m S : ℕ} {M : Finset (Clause (2 * m))} (hM : M.card ≤ S) :
    BinaryResSeg m S M M where
  steps := 0
  trace := fun _ => M
  start_eq := rfl
  end_eq := rfl
  space_le := fun _ => hM
  valid_step := fun t => Fin.elim0 t

private def BinaryResSeg.single {m S : ℕ} {M₁ M₂ : Finset (Clause (2 * m))}
    (hstep : BinaryResStep m S M₁ M₂) (h₁ : M₁.card ≤ S) (h₂ : M₂.card ≤ S) :
    BinaryResSeg m S M₁ M₂ where
  steps := 1
  trace := fun t => if t.1 = 0 then M₁ else M₂
  start_eq := rfl
  end_eq := rfl
  space_le := fun t => by
    by_cases h : t.1 = 0 <;> simp [h, h₁, h₂]
  valid_step := fun t => by
    have ht : t.1 = 0 := by omega
    simpa [ht] using hstep

private def BinaryResSeg.trans {m S : ℕ} {M₁ M₂ M₃ : Finset (Clause (2 * m))}
    (s₁ : BinaryResSeg m S M₁ M₂) (s₂ : BinaryResSeg m S M₂ M₃) :
    BinaryResSeg m S M₁ M₃ where
  steps := s₁.steps + s₂.steps
  trace := fun t =>
    if h : t.1 ≤ s₁.steps then
      s₁.trace ⟨t.1, Nat.lt_succ_of_le h⟩
    else
      s₂.trace ⟨t.1 - s₁.steps, by omega⟩
  start_eq := by
    simp [s₁.start_eq]
  end_eq := by
    by_cases h : s₁.steps + s₂.steps ≤ s₁.steps
    · have h2 : s₂.steps = 0 := by omega
      simp only [h, ↓reduceDIte]
      have hfin : (⟨s₁.steps + s₂.steps, Nat.lt_succ_of_le h⟩ : Fin (s₁.steps + 1)) =
          ⟨s₁.steps, Nat.lt_succ_self s₁.steps⟩ := Fin.ext (by dsimp; omega)
      rw [hfin, s₁.end_eq]
      have h0 : (0 : Fin (s₂.steps + 1)) = ⟨s₂.steps, Nat.lt_succ_self s₂.steps⟩ :=
        Fin.ext (by dsimp; omega)
      rw [← s₂.start_eq, h0, s₂.end_eq]
    · simp only [h, ↓reduceDIte]
      have hfin : (⟨s₁.steps + s₂.steps - s₁.steps, by omega⟩ : Fin (s₂.steps + 1)) =
          ⟨s₂.steps, Nat.lt_succ_self s₂.steps⟩ := Fin.ext (by dsimp; omega)
      rw [hfin, s₂.end_eq]
  space_le := fun t => by
    by_cases h : t.1 ≤ s₁.steps
    · simp only [h, ↓reduceDIte]
      exact s₁.space_le _
    · simp only [h, ↓reduceDIte]
      exact s₂.space_le _
  valid_step := fun t => by
    by_cases h : t.1 < s₁.steps
    · have h1 : t.castSucc.1 ≤ s₁.steps := by simp; omega
      have h2 : t.succ.1 ≤ s₁.steps := by simp; omega
      simp only [h1, h2, ↓reduceDIte]
      exact s₁.valid_step ⟨t.1, h⟩
    · by_cases heq : t.1 = s₁.steps
      · have h1 : t.castSucc.1 ≤ s₁.steps := by simp; omega
        have h2 : ¬ t.succ.1 ≤ s₁.steps := by simp; omega
        simp only [h1, h2, ↓reduceDIte]
        have hfin1 : (⟨t.castSucc.1, Nat.lt_succ_of_le h1⟩ : Fin (s₁.steps + 1)) =
            ⟨s₁.steps, Nat.lt_succ_self s₁.steps⟩ := Fin.ext (by simp [heq])
        rw [hfin1, s₁.end_eq]
        have hs2 := s₂.valid_step ⟨0, by omega⟩
        rw [show (⟨0, by omega⟩ : Fin s₂.steps).castSucc = 0 from rfl, s₂.start_eq] at hs2
        have hfin2 : (⟨t.succ.1 - s₁.steps, by omega⟩ : Fin (s₂.steps + 1)) =
            (⟨0, by omega⟩ : Fin s₂.steps).succ := Fin.ext (by simp [heq])
        rw [hfin2]
        exact hs2
      · have h1 : ¬ t.castSucc.1 ≤ s₁.steps := by simp; omega
        have h2 : ¬ t.succ.1 ≤ s₁.steps := by simp; omega
        simp only [h1, h2, ↓reduceDIte]
        have hfin1 : (⟨t.castSucc.1 - s₁.steps, by omega⟩ : Fin (s₂.steps + 1)) =
            (⟨t.1 - s₁.steps, by omega⟩ : Fin s₂.steps).castSucc := Fin.ext (by simp)
        have hfin2 : (⟨t.succ.1 - s₁.steps, by omega⟩ : Fin (s₂.steps + 1)) =
            (⟨t.1 - s₁.steps, by omega⟩ : Fin s₂.steps).succ := Fin.ext (by simp; omega)
        rw [hfin1, hfin2]
        exact s₂.valid_step ⟨t.1 - s₁.steps, by omega⟩

private theorem BinaryResSeg.mem_trans_left {m S : ℕ} {M₁ M₂ M₃ : Finset (Clause (2 * m))}
    {s₁ : BinaryResSeg m S M₁ M₂} {s₂ : BinaryResSeg m S M₂ M₃} {C : Clause (2 * m)}
    (h : ∃ t, C ∈ s₁.trace t) : ∃ t, C ∈ (s₁.trans s₂).trace t := by
  rcases h with ⟨t, ht⟩
  refine ⟨⟨t.1, by dsimp [BinaryResSeg.trans]; omega⟩, ?_⟩
  have hle : t.1 ≤ s₁.steps := Nat.le_of_lt_succ t.2
  dsimp only [BinaryResSeg.trans]
  simp only [hle, ↓reduceDIte]
  exact ht

private theorem BinaryResSeg.mem_trans_right {m S : ℕ} {M₁ M₂ M₃ : Finset (Clause (2 * m))}
    {s₁ : BinaryResSeg m S M₁ M₂} {s₂ : BinaryResSeg m S M₂ M₃} {C : Clause (2 * m)}
    (h : ∃ t, C ∈ s₂.trace t) : ∃ t, C ∈ (s₁.trans s₂).trace t := by
  rcases h with ⟨t, ht⟩
  by_cases h0 : t.1 = 0
  · refine ⟨⟨s₁.steps, by dsimp [BinaryResSeg.trans]; omega⟩, ?_⟩
    dsimp only [BinaryResSeg.trans]
    simp only [le_rfl, ↓reduceDIte]
    rw [s₁.end_eq]
    have ht0 : t = 0 := Fin.ext h0
    rw [ht0, s₂.start_eq] at ht
    exact ht
  · refine ⟨⟨s₁.steps + t.1, by dsimp [BinaryResSeg.trans]; omega⟩, ?_⟩
    have hgt : ¬ s₁.steps + t.1 ≤ s₁.steps := by omega
    dsimp only [BinaryResSeg.trans]
    simp only [hgt, ↓reduceDIte]
    have hfin : (⟨s₁.steps + t.1 - s₁.steps, by omega⟩ : Fin (s₂.steps + 1)) = t :=
      Fin.ext (by dsimp; omega)
    rw [hfin]
    exact ht

/-- Eliminate one input literal `¬x_k` from `{partialPropClause j k}` to obtain
`{partialPropClause j (k + 1)}` in 4 steps using clause space at most `3`. -/
private def resolveOneInputSeg {m : ℕ} (j : Fin m) (k : ℕ) (hk : k < m) :
    BinaryResSeg m 3 {partialPropClause j k} {partialPropClause j (k + 1)} :=
  let P₀ := partialPropClause j k
  let I₀ := inClause ⟨k, hk⟩
  let P₁ := partialPropClause j (k + 1)
  have h1 : ({P₀} : Finset (Clause (2 * m))).card ≤ 3 := by simp
  have h2 : (insert I₀ ({P₀} : Finset (Clause (2 * m)))).card ≤ 3 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h3 : (insert P₁ (insert I₀ ({P₀} : Finset (Clause (2 * m))))).card ≤ 3 :=
    le_trans (Finset.card_insert_le _ _) (by
      have := Finset.card_insert_le I₀ ({P₀} : Finset (Clause (2 * m)))
      simp at this ⊢; omega)
  have hI_ax : I₀ ∈ pebKmmCNF m :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩)
  have hstep1 : BinaryResStep m 3 {P₀} (insert I₀ {P₀}) :=
    BinaryResStep.loadAxiom I₀ hI_ax h1 h2
  have hstep2 : BinaryResStep m 3 (insert I₀ {P₀}) (insert P₁ (insert I₀ {P₀})) :=
    BinaryResStep.resolve I₀ P₀ P₁
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (isResolvent_inClause_partialPropClause j hk) h2 h3
  have her1 : (insert P₁ (insert I₀ ({P₀} : Finset (Clause (2 * m))))).erase P₀ =
      insert P₁ {I₀} := by
    ext C
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    have hP₀_ne_P₁ : P₀ ≠ P₁ := partialPropClause_ne_succ j hk
    have hP₀_ne_I₀ : P₀ ≠ I₀ := partialPropClause_ne_inClause j k ⟨k, hk⟩
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
    · rintro (rfl | rfl)
      · exact ⟨hP₀_ne_P₁.symm, Or.inl rfl⟩
      · exact ⟨hP₀_ne_I₀.symm, Or.inr (Or.inl rfl)⟩
  have h4 : (insert P₁ ({I₀} : Finset (Clause (2 * m)))).card ≤ 3 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have hstep3 : BinaryResStep m 3 (insert P₁ (insert I₀ {P₀})) (insert P₁ {I₀}) := by
    rw [← her1]
    exact BinaryResStep.erase P₀ h3
  have her2 : (insert P₁ ({I₀} : Finset (Clause (2 * m)))).erase I₀ = {P₁} := by
    ext C
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    have hP₁_ne_I₀ : P₁ ≠ I₀ := partialPropClause_ne_inClause j (k + 1) ⟨k, hk⟩
    constructor
    · rintro ⟨hne, rfl | rfl⟩
      · rfl
      · exact absurd rfl hne
    · rintro rfl
      exact ⟨hP₁_ne_I₀, Or.inl rfl⟩
  have h5 : ({P₁} : Finset (Clause (2 * m))).card ≤ 3 := by simp
  have hstep4 : BinaryResStep m 3 (insert P₁ {I₀}) {P₁} := by
    rw [← her2]
    exact BinaryResStep.erase I₀ h4
  (((BinaryResSeg.single hstep1 h1 h2).trans
    (BinaryResSeg.single hstep2 h2 h3)).trans
    (BinaryResSeg.single hstep3 h3 h4)).trans
    (BinaryResSeg.single hstep4 h4 h5)

private def resolvePrefixSeg {m : ℕ} (j : Fin m) :
    ∀ k : ℕ, k ≤ m → BinaryResSeg m 3 {partialPropClause j 0} {partialPropClause j k}
  | 0, _ => BinaryResSeg.refl (by simp)
  | k + 1, hk =>
    (resolvePrefixSeg j k (Nat.le_of_lt hk)).trans (resolveOneInputSeg j k hk)

private def deriveOneOutputSeg {m : ℕ} (j : Fin m) :
    { seg : BinaryResSeg m 3 ∅ ∅ // ∃ t, outClause j ∈ seg.trace t } := by
  have h0 : (∅ : Finset (Clause (2 * m))).card ≤ 3 := by simp
  have h1 : ({partialPropClause j 0} : Finset (Clause (2 * m))).card ≤ 3 := by simp
  have h2 : ({outClause j} : Finset (Clause (2 * m))).card ≤ 3 := by simp
  have hax : partialPropClause j 0 ∈ pebKmmCNF m := by
    rw [partialPropClause_zero]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hload : BinaryResStep m 3 ∅ {partialPropClause j 0} := by
    simpa using BinaryResStep.loadAxiom (partialPropClause j 0) hax h0 (by simp)
  have herase : BinaryResStep m 3 {outClause j} ∅ := by
    simpa using BinaryResStep.erase (outClause j) h2
  let seg_mid : BinaryResSeg m 3 {partialPropClause j 0} {outClause j} := by
    simpa [partialPropClause_eq_outClause] using resolvePrefixSeg j m le_rfl
  let seg : BinaryResSeg m 3 ∅ ∅ :=
    ((BinaryResSeg.single hload h0 h1).trans seg_mid).trans
      (BinaryResSeg.single herase h2 h0)
  refine ⟨seg, ?_⟩
  apply BinaryResSeg.mem_trans_left
  apply BinaryResSeg.mem_trans_right
  refine ⟨⟨seg_mid.steps, Nat.lt_succ_self _⟩, ?_⟩
  rw [seg_mid.end_eq]
  exact Finset.mem_singleton_self _

private def deriveAllOutputsSeg {m : ℕ} :
    ∀ k : ℕ, k ≤ m →
      { seg : BinaryResSeg m 3 ∅ ∅ // ∀ j : Fin m, j.1 < k → ∃ t, outClause j ∈ seg.trace t }
  | 0, _ => ⟨BinaryResSeg.refl (by simp), fun j hj => by omega⟩
  | k + 1, hk => by
    let prev := deriveAllOutputsSeg k (Nat.le_of_lt hk)
    let cur := deriveOneOutputSeg ⟨k, hk⟩
    refine ⟨prev.1.trans cur.1, fun j hj => ?_⟩
    by_cases hlt : j.1 < k
    · exact BinaryResSeg.mem_trans_left (prev.2 j hlt)
    · have hj_eq : j = ⟨k, hk⟩ := Fin.ext (by dsimp; omega)
      rw [hj_eq]
      exact BinaryResSeg.mem_trans_right cur.2

/-- **Explicit Counterexample / Obstruction (Unrestricted Binary Resolution at `S = 3`)**:
For every `m ≥ 1`, unrestricted binary resolution (`ValidBinaryRes`) derives every output clause
`outClause j` of `pebKmmCNF m` in constant clause space `S = 3`, because width-`m` partial
propagation clauses act as bit-vector accumulators. -/
theorem binaryRes_pebKmm_space_three {m : ℕ} (hm : 1 ≤ m) :
    Nonempty (ValidBinaryRes m 3) := by
  have _ := hm
  let res := deriveAllOutputsSeg (m := m) m le_rfl
  exact ⟨{
    steps := res.1.steps
    trace := res.1.trace
    init_empty := res.1.start_eq
    space_le := res.1.space_le
    valid_step := res.1.valid_step
    outputs_derived := fun j => res.2 j j.2
  }⟩

/-- **Machine-Verified Separation Between Unrestricted Binary Resolution and `BoundedHyperRes`**:
For every `m ≥ 4` and any batch rate `c`, `pebKmmCNF m` is derivable in clause space `S = 3` by
unrestricted binary resolution (`ValidBinaryRes m 3`), yet completely infeasible at clause space
`S = 3` for `BoundedHyperRes m 3 c`. -/
theorem binaryRes_vs_hyperRes_separation {m c : ℕ} (hm : 4 ≤ m) :
    Nonempty (ValidBinaryRes m 3) ∧ IsEmpty (ValidHyperRes m 3 c) :=
  ⟨binaryRes_pebKmm_space_three (by omega), hyperRes_infeasible_below_m (by omega) (by omega)⟩

end Mathmatica.HyperResSimulation
