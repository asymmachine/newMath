/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathmatica.ResidualEntropy

/-!
# Static Space-Time Volume, Finite-State Cycles, and Feedback-Free Multi-Pass Tradeoffs

This module formalizes three self-contained, non-circular foundations for time-space analysis
built directly on `Mathmatica.ResidualEntropy`:

1. **Part A (Static Space-Time Volume Bridge)**: Layer-by-layer sum of semantic residual class
   counts `totalResidualVolume F π` lower-bounding the static total size `P.totalSize` of any
   correct deterministic layered `OrderedProgram`, together with exact natural instances
   (`innerProductFn`, `eqFn` under split vs. interleaved orders, and `parityFn`).
2. **Part B (Finite-State Deterministic Cycle Theorem)**: Pigeonhole cycle entry, periodic tail,
   and non-reachability for any deterministic transition operator `T : S → S` on a finite state
   space `S`.
3. **Part C (Feedback-Free Multi-Pass Ordered Program Time-Space Tradeoff)**: Product-state
   reduction showing `residualClassCount F π t ht ≤ M ^ p` and `b ≤ p * S` for `p`-pass
   oblivious (feedback-free) ordered programs, yielding `m ≤ p * S` on `innerProductFn m`.

## Epistemic Discipline (Four-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file are formally verified in Lean 4
  with zero `sorry`s and no extra axioms.
* **Model-Restricted**:
  - Part A bounds **static program volume** (`∑ t, Fintype.card (P.State t)` across all prefixes),
    **NOT** single-input online running time `T(x)`.
  - Part B characterizes finite-state determinism and termination boundaries only; it does **NOT**
    imply algorithmic hardness (e.g., Floyd's cycle-finding algorithm detects cycles using `O(1)`
    state copies). All restart counters, head positions, and PRNG seeds must be included in `S`.
  - Part C applies strictly to **feedback-free (`ObliviousMultiPassProgram`)** ordered programs.
    It explicitly excludes suffix-to-prefix feedback: the Indexing function `IND_k` has
    `log₂ N = 2 ^ k` yet admits a 2-pass streaming algorithm with feedback using `S = k + 1` bits.
* **Conditional**: Extending Part A to online running time requires uniformity and reachability
  assumptions; extending Part C to feedback multi-pass streaming requires replacing one-way
  `residualClassCount` by two-way communication complexity `D(F, π, t)`.
* **Conjectural**: General algorithm time-space lower bounds, metastable conductance escape
  bounds, and `P ≠ NP` are **NOT** claimed or implied by this module.

## Main definitions

* `totalResidualVolume`: Layer-by-layer sum `∑_{t=0}^n N_{F,π}(t)`.
* `OrderedProgram.totalSize`: Static program size `∑_{t=0}^n |P.State t|` across all layers.
* `ObliviousMultiPassProgram`, `CorrectObliviousMultiPass`,
  `ObliviousMultiPassProgram.toProductProgram`: Feedback-free `p`-pass ordered programs and their
  product-state compilation into a single `OrderedProgram`.

## Main results

* `ordered_program_totalSize_ge_residualVolume`: `totalResidualVolume F π ≤ P.totalSize`.
* `innerProduct_residualClassCount_prefix_eq`, `innerProduct_totalResidualVolume_ge`,
  `innerProduct_totalSize_ge`: Exact layer-by-layer `2 ^ t` counts and `2 ^ (m + 1) - 1` static
  volume lower bound on `innerProductFn m`.
* `eq_split_residualClassCount_prefix_eq`, `eq_split_totalResidualVolume_ge`,
  `eq_interleaved_totalResidualVolume_le`: Exponential (`≥ 2 ^ (m + 1) - 1`) vs. linear
  (`≤ 3 * (2 * m + 1)`) static volume separation on `eqFn m`.
* `parity_totalResidualVolume_le`: Sanity baseline `≤ 2 * (n + 1)` for `parityFn n` under every
  variable order `π`.
* `finite_state_enters_cycle`, `finite_state_periodic_tail`,
  `finite_state_never_reaches_of_cycle`: Finite-state pigeonhole periodicity and non-reachability.
* `oblivious_multipass_width_tradeoff`, `oblivious_multipass_bit_tradeoff`,
  `innerProduct_oblivious_multipass_bit_tradeoff`: Feedback-free multi-pass tradeoffs
  `N_{F,π}(t) ≤ M ^ p`, `b ≤ p * S`, and `m ≤ p * S`.
-/

namespace Mathmatica.TimeSpaceVolume

open Mathmatica.ResidualEntropy

/-! ### Part A: Static Space-Time Volume Bridge (Layer-by-Layer Sum) -/

/-- Total semantic residual volume `∑_{t=0}^n N_{F,π}(t)` across all layers `0 ≤ t ≤ n`. -/
noncomputable def totalResidualVolume {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) : ℕ :=
  ∑ t : Fin (n + 1), residualClassCount F π t.val (Nat.le_of_lt_succ t.isLt)

/-- Static total size (space-time volume across all prefixes) of a layered `OrderedProgram`.
NOTE: This measures static layered program volume, NOT single-input online running time. -/
def _root_.Mathmatica.ResidualEntropy.OrderedProgram.totalSize {n : ℕ}
    (P : OrderedProgram n) : ℕ :=
  ∑ t : Fin (n + 1), Fintype.card (P.State t)

/-- **Theorem A1 (Static Volume Lower Bound, Model-Restricted)**:
Every correct deterministic layered `OrderedProgram` respecting `π` satisfies
`totalResidualVolume F π ≤ P.totalSize`. -/
theorem ordered_program_totalSize_ge_residualVolume {n : ℕ}
    (P : OrderedProgram n) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectOrderedProgram P F π) :
    totalResidualVolume F π ≤ P.totalSize :=
  Finset.sum_le_sum fun t _ =>
    ordered_program_width_ge_residual_classes P F π hCorr t.val (Nat.le_of_lt_succ t.isLt)

private theorem sum_pow_two_range (m : ℕ) :
    ∑ t ∈ Finset.range (m + 1), 2 ^ t = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by decide)
      have hpow : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
      omega

private theorem totalResidualVolume_ge_of_prefix_pow_two {m : ℕ} (F : BoolFn (2 * m))
    (π : Equiv.Perm (Fin (2 * m)))
    (hPrefix : ∀ (t : ℕ) (ht : t ≤ m), residualClassCount F π t (by omega) = 2 ^ t) :
    2 ^ (m + 1) - 1 ≤ totalResidualVolume F π := by
  let emb : Fin (m + 1) ↪ Fin (2 * m + 1) :=
    ⟨fun t => ⟨t.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
  have hSub :
      (Finset.univ : Finset (Fin (m + 1))).map emb ⊆ (Finset.univ : Finset (Fin (2 * m + 1))) :=
    Finset.subset_univ _
  calc
    2 ^ (m + 1) - 1
        = ∑ t ∈ Finset.range (m + 1), 2 ^ t := (sum_pow_two_range m).symm
    _ = ∑ t : Fin (m + 1), 2 ^ t.val := (Fin.sum_univ_eq_sum_range (fun t => 2 ^ t) (m + 1)).symm
    _ = ∑ t : Fin (m + 1),
          residualClassCount F π (emb t).val (Nat.le_of_lt_succ (emb t).isLt) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact (hPrefix t.val (Nat.le_of_lt_succ t.isLt)).symm
    _ = ∑ t ∈ (Finset.univ : Finset (Fin (m + 1))).map emb,
          residualClassCount F π t.val (Nat.le_of_lt_succ t.isLt) := by
          rw [Finset.sum_map]
    _ ≤ totalResidualVolume F π :=
          Finset.sum_le_sum_of_subset hSub

local instance : Std.Commutative xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative xor := ⟨Bool.xor_assoc⟩

private theorem fold_xor_false_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.fold xor false (fun _ => false) = false := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.fold_insert ha, ih]
      rfl

/-- Indicator suffix at layer `t ≤ m` with a single `true` at suffix coordinate `m + i - t`,
isolating the `i`-th input bit `x_i` in `innerProductFn m`. -/
private def prefixIndicator (m t : ℕ) (i : Fin t) : Fin (2 * m - t) → Bool :=
  fun j => decide (j.val = m + i.val - t)

private theorem innerProduct_residual_prefixIndicator (m t : ℕ) (ht : t ≤ m)
    (ρ : Fin t → Bool) (i : Fin t) :
    residualFn (innerProductFn m) (Equiv.refl (Fin (2 * m))) t (by omega) ρ
      (prefixIndicator m t i) = ρ i := by
  unfold residualFn innerProductFn
  have hterm :
      (fun k : Fin m =>
        glue (Equiv.refl (Fin (2 * m))) t (by omega) ρ (prefixIndicator m t i)
            ⟨k.val, by omega⟩ &&
        glue (Equiv.refl (Fin (2 * m))) t (by omega) ρ (prefixIndicator m t i)
            ⟨m + k.val, by omega⟩) =
      (fun k : Fin m =>
        (if hk : k.val < t then ρ ⟨k.val, hk⟩ else false) && decide (k.val = i.val)) := by
    funext k
    have hnot : ¬ (m + k.val < t) := by omega
    have hiff : (m + k.val - t = m + i.val - t) ↔ k.val = i.val := by omega
    by_cases hk : k.val < t
    · simp [glue, hk, hnot, prefixIndicator, hiff]
    · have hne : k.val ≠ i.val := by omega
      simp [glue, hk, hnot, prefixIndicator, hiff, hne]
  rw [hterm]
  let i' : Fin m := ⟨i.val, by omega⟩
  have hmem : i' ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i'
  rw [← Finset.insert_erase hmem, Finset.fold_insert (Finset.notMem_erase i' Finset.univ)]
  have herase :
      (Finset.univ.erase i').fold xor false
        (fun k : Fin m =>
          (if hk : k.val < t then ρ ⟨k.val, hk⟩ else false) && decide (k.val = i.val)) =
        false := by
    have hzero :
        (Finset.univ.erase i').fold xor false
          (fun k : Fin m =>
            (if hk : k.val < t then ρ ⟨k.val, hk⟩ else false) && decide (k.val = i.val)) =
          (Finset.univ.erase i').fold xor false (fun _ => false) := by
      refine Finset.fold_congr fun k hk => ?_
      have hne : k.val ≠ i.val := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
      simp [hne]
    rw [hzero, fold_xor_false_eq]
  rw [herase]
  simp [i', i.isLt]

/-- **Exact Layer-by-Layer Count (`innerProductFn`)**: Under the split variable order
`Equiv.refl (Fin (2 * m))`, `innerProductFn m` has exactly `2 ^ t` residual classes at every
prefix layer `t ≤ m`. -/
theorem innerProduct_residualClassCount_prefix_eq (m t : ℕ) (ht : t ≤ m) :
    residualClassCount (innerProductFn m) (Equiv.refl (Fin (2 * m))) t (by omega) = 2 ^ t := by
  classical
  unfold residualClassCount
  have hinj :
      Function.Injective
        (residualFn (innerProductFn m) (Equiv.refl (Fin (2 * m))) t (by omega)) :=
    fun ρ₁ ρ₂ hEq => by
      funext i
      have h := congrFun hEq (prefixIndicator m t i)
      simpa [innerProduct_residual_prefixIndicator m t ht] using h
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp

/-- **Exponential Static Volume (`innerProductFn`)**: Summing layers `0 ≤ t ≤ m` gives
`2 ^ (m + 1) - 1 ≤ totalResidualVolume (innerProductFn m) (Equiv.refl (Fin (2 * m)))`. -/
theorem innerProduct_totalResidualVolume_ge (m : ℕ) :
    2 ^ (m + 1) - 1 ≤ totalResidualVolume (innerProductFn m) (Equiv.refl (Fin (2 * m))) :=
  totalResidualVolume_ge_of_prefix_pow_two (innerProductFn m) (Equiv.refl (Fin (2 * m)))
    (innerProduct_residualClassCount_prefix_eq m)

/-- **Static Program Size Lower Bound (`innerProductFn`)**: Any correct ordered program computing
`innerProductFn m` under the split variable order has static total size at least
`2 ^ (m + 1) - 1`. -/
theorem innerProduct_totalSize_ge (m : ℕ) (P : OrderedProgram (2 * m))
    (hCorr : CorrectOrderedProgram P (innerProductFn m) (Equiv.refl (Fin (2 * m)))) :
    2 ^ (m + 1) - 1 ≤ P.totalSize :=
  le_trans (innerProduct_totalResidualVolume_ge m)
    (ordered_program_totalSize_ge_residualVolume P (innerProductFn m)
      (Equiv.refl (Fin (2 * m))) hCorr)

/-- **Exact Layer-by-Layer Count (`eqFn`, split order)**: Under `Equiv.refl (Fin (2 * m))`,
`eqFn m` has exactly `2 ^ t` residual classes at every prefix layer `t ≤ m`. -/
theorem eq_split_residualClassCount_prefix_eq (m t : ℕ) (ht : t ≤ m) :
    residualClassCount (eqFn m) (Equiv.refl (Fin (2 * m))) t (by omega) = 2 ^ t := by
  classical
  unfold residualClassCount
  have hinj :
      Function.Injective (residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) t (by omega)) :=
    fun ρ₁ ρ₂ hEq => by
      let τ : Fin (2 * m - t) → Bool := fun j =>
        if h : m - t ≤ j.val ∧ j.val < m then ρ₁ ⟨j.val + t - m, by omega⟩ else false
      have h₁ :
          residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) t (by omega) ρ₁ τ = true := by
        unfold residualFn eqFn
        rw [decide_eq_true_iff]
        intro i
        by_cases hi : i.val < t
        · have hnot : ¬ (m + i.val < t) := by omega
          have hcond : m - t ≤ m + i.val - t ∧ m + i.val - t < m := by omega
          have hidx : (⟨m + i.val - t + t - m, by omega⟩ : Fin t) = ⟨i.val, hi⟩ := by
            ext; dsimp; omega
          simp only [glue, Equiv.refl_symm, Equiv.refl_apply, hi, hnot, ↓reduceDIte, τ,
            hcond, and_self, hidx]
        · have hnot : ¬ (m + i.val < t) := by omega
          have hcond₁ : ¬ (m - t ≤ i.val - t ∧ i.val - t < m) := by omega
          have hcond₂ : ¬ (m - t ≤ m + i.val - t ∧ m + i.val - t < m) := by omega
          simp only [glue, Equiv.refl_symm, Equiv.refl_apply, hi, hnot, ↓reduceDIte, τ,
            hcond₁, hcond₂]
      have h₂ :
          residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) t (by omega) ρ₂ τ = true := by
        rw [← congrFun hEq τ, h₁]
      unfold residualFn eqFn at h₂
      rw [decide_eq_true_iff] at h₂
      funext i
      have hi := h₂ ⟨i.val, by omega⟩
      have hnot : ¬ (m + i.val < t) := by omega
      have hcond : m - t ≤ m + i.val - t ∧ m + i.val - t < m := by omega
      have hidx : (⟨m + i.val - t + t - m, by omega⟩ : Fin t) = i := by
        ext; dsimp; omega
      simp only [glue, Equiv.refl_symm, Equiv.refl_apply, i.isLt, hnot, ↓reduceDIte, τ,
        hcond, and_self, hidx] at hi
      exact hi.symm
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp

/-- **Exponential Static Volume (`eqFn`, split order)**: Under split order,
`2 ^ (m + 1) - 1 ≤ totalResidualVolume (eqFn m) (Equiv.refl (Fin (2 * m)))`. -/
theorem eq_split_totalResidualVolume_ge (m : ℕ) :
    2 ^ (m + 1) - 1 ≤ totalResidualVolume (eqFn m) (Equiv.refl (Fin (2 * m))) :=
  totalResidualVolume_ge_of_prefix_pow_two (eqFn m) (Equiv.refl (Fin (2 * m)))
    (eq_split_residualClassCount_prefix_eq m)

/-- **Linear Static Volume (`eqFn`, interleaved order)**: Under `interleavePerm m`,
`totalResidualVolume (eqFn m) (interleavePerm m) ≤ 3 * (2 * m + 1)`, demonstrating an
exponential-vs-linear order-sensitivity separation in static volume. -/
theorem eq_interleaved_totalResidualVolume_le (m : ℕ) :
    totalResidualVolume (eqFn m) (interleavePerm m) ≤ 3 * (2 * m + 1) := by
  calc
    totalResidualVolume (eqFn m) (interleavePerm m)
        ≤ ∑ _t : Fin (2 * m + 1), 3 :=
          Finset.sum_le_sum fun t _ =>
            eq_interleaved_residualClassCount_le m t.val (Nat.le_of_lt_succ t.isLt)
    _ = 3 * (2 * m + 1) := by simp [Nat.mul_comm]

/-- **Sanity Baseline (`parityFn`)**: Under *every* variable order `π`,
`totalResidualVolume (parityFn n) π ≤ 2 * (n + 1)`. -/
theorem parity_totalResidualVolume_le (n : ℕ) (π : Equiv.Perm (Fin n)) :
    totalResidualVolume (parityFn n) π ≤ 2 * (n + 1) := by
  calc
    totalResidualVolume (parityFn n) π
        ≤ ∑ _t : Fin (n + 1), 2 :=
          Finset.sum_le_sum fun t _ =>
            parity_residualClassCount_le_two n π t.val (Nat.le_of_lt_succ t.isLt)
    _ = 2 * (n + 1) := by simp [Nat.mul_comm]

/-! ### Part B: Finite-State Deterministic Cycle Theorem (Does NOT Imply Hardness) -/

/-- **Theorem B1 (Finite-State Cycle Entry)**:
Any deterministic transition `T : S → S` on a finite state space `S` repeats a state within
`Fintype.card S` steps.
NOTE: Restart counters, head positions, and PRNG seeds must be included in `S`.
This theorem does NOT imply algorithmic hardness (Floyd's cycle detector uses `O(1)` copies). -/
theorem finite_state_enters_cycle {S : Type*} [Fintype S] (T : S → S) (s₀ : S) :
    ∃ i j, i < j ∧ j ≤ Fintype.card S ∧ T^[i] s₀ = T^[j] s₀ := by
  let f : Fin (Fintype.card S + 1) → S := fun k => T^[k.val] s₀
  obtain ⟨a, b, hne, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact ⟨a.val, b.val, hlt, Nat.le_of_lt_succ b.isLt, hEq⟩
  · exact ⟨b.val, a.val, hgt, Nat.le_of_lt_succ a.isLt, hEq.symm⟩

/-- **Theorem B2 (Periodic Tail)**:
Once a deterministic orbit repeats `T^[i] s₀ = T^[j] s₀`, it remains periodic thereafter. -/
theorem finite_state_periodic_tail {S : Type*} (T : S → S) (s₀ : S)
    {i j : ℕ} (hEq : T^[i] s₀ = T^[j] s₀) :
    ∀ k : ℕ, T^[i + k] s₀ = T^[j + k] s₀ := by
  intro k
  rw [Nat.add_comm i k, Nat.add_comm j k,
    Function.iterate_add_apply, Function.iterate_add_apply, hEq]

/-- **Theorem B3 (Non-Reachability from Cycle Closure)**:
If a deterministic orbit on a finite state space `S` does not visit `Target` during its first
`Fintype.card S` steps (`0 ≤ k < Fintype.card S`), then it never visits `Target` at any step
`k : ℕ`. Does NOT imply algorithmic hardness. -/
theorem finite_state_never_reaches_of_cycle {S : Type*} [Fintype S] (T : S → S) (s₀ : S)
    (Target : S → Prop) (hMiss : ∀ k < Fintype.card S, ¬ Target (T^[k] s₀)) :
    ∀ k : ℕ, ¬ Target (T^[k] s₀) := by
  obtain ⟨i, j, hij, hj, hEq⟩ := finite_state_enters_cycle T s₀
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      by_cases hlt : k < Fintype.card S
      · exact hMiss k hlt
      · have hjk : j ≤ k := by omega
        have hstep : T^[k] s₀ = T^[i + (k - j)] s₀ := by
          calc
            T^[k] s₀ = T^[j + (k - j)] s₀ := by rw [Nat.add_sub_of_le hjk]
            _ = T^[i + (k - j)] s₀ := (finite_state_periodic_tail T s₀ hEq (k - j)).symm
        rw [hstep]
        exact ih (i + (k - j)) (by omega)

/-! ### Part C: Feedback-Free Multi-Pass Ordered Program Time-Space Tradeoff (Conjecture 1A) -/

/-- A `p`-pass feedback-free (oblivious) ordered program: executes `p` independent ordered passes
in variable order `π` and combines their `p` final states to output a Boolean bit.
NOTE: Explicitly excludes suffix-to-prefix feedback (which is broken by `IND_k` in 2 passes). -/
structure ObliviousMultiPassProgram (n p : ℕ) where
  /-- The `p` independent single-pass ordered programs. -/
  pass : Fin p → OrderedProgram n
  /-- Final readout combining the terminal states of all `p` passes. -/
  combine : (∀ r : Fin p, (pass r).State ⟨n, Nat.lt_succ_self n⟩) → Bool

/-- Correctness of an `ObliviousMultiPassProgram` for computing `F` under variable order `π`. -/
def CorrectObliviousMultiPass {n p : ℕ} (P : ObliviousMultiPassProgram n p)
    (F : BoolFn n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n → Bool,
    P.combine (fun r => (P.pass r).runPrefix n le_rfl (fun i => x (π i))) = F x

/-- Product-state compilation of a `p`-pass feedback-free ordered program into a single
`OrderedProgram n` whose layer-`t` state is the tuple of layer-`t` states across all `p` passes. -/
def ObliviousMultiPassProgram.toProductProgram {n p : ℕ}
    (P : ObliviousMultiPassProgram n p) : OrderedProgram n where
  State t := ∀ r : Fin p, (P.pass r).State t
  fintypeState _ := inferInstance
  init r := (P.pass r).init
  trans t s b r := (P.pass r).trans t (s r) b
  output s := P.combine s

private theorem toProductProgram_runPrefix {n p : ℕ}
    (P : ObliviousMultiPassProgram n p) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) (r : Fin p) :
    P.toProductProgram.runPrefix t ht ρ r = (P.pass r).runPrefix t ht ρ := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [OrderedProgram.runPrefix]
      exact congrArg (fun s => (P.pass r).trans ⟨t, ht⟩ s (ρ ⟨t, Nat.lt_succ_self t⟩))
        (ih (Nat.le_of_succ_le ht) _)

/-- Correctness preservation of `ObliviousMultiPassProgram.toProductProgram`. -/
theorem toProductProgram_correct {n p : ℕ} (P : ObliviousMultiPassProgram n p)
    (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectObliviousMultiPass P F π) :
    CorrectOrderedProgram P.toProductProgram F π := by
  intro x
  have hEq :
      P.toProductProgram.runPrefix n le_rfl (fun i => x (π i)) =
        fun r => (P.pass r).runPrefix n le_rfl (fun i => x (π i)) := by
    funext r
    exact toProductProgram_runPrefix P n le_rfl (fun i => x (π i)) r
  change P.combine (P.toProductProgram.runPrefix n le_rfl (fun i => x (π i))) = F x
  rw [hEq]
  exact hCorr x

/-- **Theorem C1 (Feedback-Free Multi-Pass Width Tradeoff, Model-Restricted)**:
If each of the `p` feedback-free passes has layer-`t` width at most `M`, then
`residualClassCount F π t ht ≤ M ^ p`. -/
theorem oblivious_multipass_width_tradeoff {n p M : ℕ}
    (P : ObliviousMultiPassProgram n p) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectObliviousMultiPass P F π) (t : ℕ) (ht : t ≤ n)
    (hM : ∀ r : Fin p, Fintype.card ((P.pass r).State ⟨t, Nat.lt_succ_of_le ht⟩) ≤ M) :
    residualClassCount F π t ht ≤ M ^ p := by
  have hWidth :=
    ordered_program_width_ge_residual_classes P.toProductProgram F π
      (toProductProgram_correct P F π hCorr) t ht
  have hCard :
      Fintype.card (P.toProductProgram.State ⟨t, Nat.lt_succ_of_le ht⟩) ≤ M ^ p := by
    change Fintype.card (∀ r : Fin p, (P.pass r).State ⟨t, Nat.lt_succ_of_le ht⟩) ≤ M ^ p
    rw [Fintype.card_pi]
    calc
      ∏ r : Fin p, Fintype.card ((P.pass r).State ⟨t, Nat.lt_succ_of_le ht⟩)
          ≤ ∏ _r : Fin p, M := Finset.prod_le_prod fun r _ => hM r
      _ = M ^ p := by simp
  exact le_trans hWidth hCard

/-- **Theorem C2 (Feedback-Free Multi-Pass Bit Tradeoff, Model-Restricted)**:
If `EntropyBitsAtLeast F π t ht b` holds and each of the `p` feedback-free passes uses at most
`2 ^ S` states at layer `t`, then `b ≤ p * S`. -/
theorem oblivious_multipass_bit_tradeoff {n p b S : ℕ}
    (P : ObliviousMultiPassProgram n p) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectObliviousMultiPass P F π) (t : ℕ) (ht : t ≤ n)
    (hEnt : EntropyBitsAtLeast F π t ht b)
    (hS : ∀ r : Fin p, Fintype.card ((P.pass r).State ⟨t, Nat.lt_succ_of_le ht⟩) ≤ 2 ^ S) :
    b ≤ p * S := by
  have hWidth := oblivious_multipass_width_tradeoff P F π hCorr t ht hS
  have hPow : 2 ^ b ≤ 2 ^ (p * S) := by
    calc
      2 ^ b ≤ residualClassCount F π t ht := hEnt
      _ ≤ (2 ^ S) ^ p := hWidth
      _ = 2 ^ (S * p) := (Nat.pow_mul 2 S p).symm
      _ = 2 ^ (p * S) := by rw [Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hPow

/-- **Concrete Multi-Pass Tradeoff (`innerProductFn`)**:
Any `p`-pass feedback-free ordered program computing `innerProductFn m` under the split variable
order with at most `2 ^ S` states per pass at layer `m` satisfies `m ≤ p * S`. -/
theorem innerProduct_oblivious_multipass_bit_tradeoff (m p S : ℕ)
    (P : ObliviousMultiPassProgram (2 * m) p)
    (hCorr : CorrectObliviousMultiPass P (innerProductFn m) (Equiv.refl (Fin (2 * m))))
    (hS : ∀ r : Fin p, Fintype.card ((P.pass r).State ⟨m, by omega⟩) ≤ 2 ^ S) :
    m ≤ p * S := by
  have hEnt :
      EntropyBitsAtLeast (innerProductFn m) (Equiv.refl (Fin (2 * m))) m (by omega) m := by
    unfold EntropyBitsAtLeast
    rw [innerProduct_residualClassCount_eq m]
  exact oblivious_multipass_bit_tradeoff P (innerProductFn m) (Equiv.refl (Fin (2 * m)))
    hCorr m (by omega) hEnt hS

end Mathmatica.TimeSpaceVolume
