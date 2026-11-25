/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.OGPBarrier
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Explicit OGP and Unsatisfiable Symmetric Barrier Families

This module constructs concrete CNF formula families that witness the two core barriers
formalized in this project:

1. **1D Ferromagnetic Ising Chain (`isingChainCNF`)**:
   - Exact solution-space characterization (`isingChainCNF_satisfies_iff`): for `n > 0`,
     the satisfying assignments are precisely the all-`false` and all-`true` ground states.
   - Exact Hamming separation (`hammingDist_const_false_true`): the two ground states lie at
     Hamming distance `n`.
   - Full-scale Overlap Gap Property (`isingChainCNF_hasOGP`): for `n > 0`,
     `HasOGP (isingChainCNF n) 0 n`.
   - Concrete instantiation of `OGPBarrier.ogp_rules_out_stable_solver`
     (`isingChainCNF_rules_out_stable_solver`): any `δ`-stable solver with `δ < n` whose
     endpoints select the all-`false` and all-`true` ground states along a coupled Ising-chain
     path must fail on at least one intermediate instance.

2. **Pigeonhole Principle (`phpCNF`)**:
   - Variable encoding `pigeonVar m p h : Fin ((m + 1) * m)` for `m + 1` pigeons and `m` holes.
   - CNF encoding `phpCNF m` asserting that every pigeon occupies at least one hole and no hole
     holds two distinct pigeons.
   - Unsatisfiability (`phpCNF_unsat`): `∀ m : ℕ, ¬ Satisfiable (phpCNF m)`, proved via
     Mathlib's `Fintype.exists_ne_map_eq_of_card_lt`.
-/

namespace Mathmatica.ExplicitBarriers

open Mathmatica.SAT
open Mathmatica.OverlapGap
open Mathmatica.OGPBarrier

/-! ## 1. Explicit OGP Family: Ferromagnetic Ising Chain -/

/-- Ferromagnetic Ising-chain CNF on `n` Boolean variables.
For `n = m + 1`, each variable `i : Fin (m + 1)` is coupled to variable `0` via the two
implication clauses `(x_0 ∨ ¬x_i)` and `(¬x_0 ∨ x_i)`, enforcing `σ i = σ 0`. -/
def isingChainCNF : (n : ℕ) → CNF n
  | 0 => []
  | m + 1 =>
    (List.finRange (m + 1)).flatMap fun i =>
      [ [⟨⟨0, Nat.zero_lt_succ m⟩, true⟩, ⟨i, false⟩],
        [⟨⟨0, Nat.zero_lt_succ m⟩, false⟩, ⟨i, true⟩] ]

/-- Exact ground-state characterization for `isingChainCNF n` when `0 < n`:
an assignment satisfies `isingChainCNF n` if and only if it is identically `false` or
identically `true`. -/
theorem isingChainCNF_satisfies_iff {n : ℕ} (hn : 0 < n) (σ : Assignment n) :
    Satisfies (isingChainCNF n) σ ↔ σ = (fun _ => false) ∨ σ = (fun _ => true) := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m =>
    let z : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
    constructor
    · intro hSat
      have hEq : ∀ i : Fin (m + 1), σ i = σ z := by
        intro i
        have hMem1 : [⟨z, true⟩, ⟨i, false⟩] ∈ isingChainCNF (m + 1) := by
          simp [isingChainCNF, z]
        have hMem2 : [⟨z, false⟩, ⟨i, true⟩] ∈ isingChainCNF (m + 1) := by
          simp [isingChainCNF, z]
        have h1 := hSat _ hMem1
        have h2 := hSat _ hMem2
        simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at h1 h2
        cases hσi : σ i <;> cases hσz : σ z <;> simp_all
      cases hσz : σ z
      · left
        funext i
        rw [hEq i, hσz]
      · right
        funext i
        rw [hEq i, hσz]
    · rintro (rfl | rfl) c hc <;>
      · simp only [isingChainCNF, List.mem_flatMap, List.mem_finRange, true_and,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with ⟨i, rfl | rfl⟩ <;> simp [evalClause, evalLiteral]

/-- The all-`false` and all-`true` assignments on `Fin n` are at Hamming distance `n`. -/
theorem hammingDist_const_false_true (n : ℕ) :
    hammingDist (fun _ : Fin n => false) (fun _ : Fin n => true) = n := by
  unfold hammingDist
  simp

/-- **Main Theorem 1 (Explicit Full-Scale OGP)**:
For every `n ≥ 1`, `isingChainCNF n` satisfies `HasOGP (isingChainCNF n) 0 n`:
any two satisfying assignments have Hamming distance either `0` or `n`. -/
theorem isingChainCNF_hasOGP {n : ℕ} (hn : 0 < n) :
    HasOGP (isingChainCNF n) 0 n := by
  refine ⟨hn, fun σ τ hσ hτ => ?_⟩
  rw [isingChainCNF_satisfies_iff hn] at hσ hτ
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · left
    rw [hammingDist_self]
  · right
    rw [hammingDist_const_false_true]
  · right
    rw [hammingDist_comm, hammingDist_const_false_true]
  · left
    rw [hammingDist_self]

/-- Any path `path : ℕ → CNF n` whose instances all contain the clauses of `isingChainCNF n`
satisfies `HasCoupledOGP path T 0 n` whenever `0 < n`. -/
theorem isingChainCNF_hasCoupledOGP {n : ℕ} (hn : 0 < n)
    (path : ℕ → CNF n) (T : ℕ)
    (hSub : ∀ t ≤ T, ∀ c ∈ isingChainCNF n, c ∈ path t) :
    HasCoupledOGP path T 0 n := by
  have hOGP := isingChainCNF_hasOGP hn
  refine ⟨hOGP.1, fun t ht σ τ hσ hτ => ?_⟩
  have hσ' : Satisfies (isingChainCNF n) σ := fun c hc => hσ c (hSub 0 (Nat.zero_le T) c hc)
  have hτ' : Satisfies (isingChainCNF n) τ := fun c hc => hτ c (hSub t ht c hc)
  exact hOGP.2 σ τ hσ' hτ'

/-- **Main Theorem 2 (Explicit OGP Stability Barrier Instantiation)**:
For every `n ≥ 2`, step bound `δ < n`, and path `path : ℕ → CNF n` containing
`isingChainCNF n` at every step `t ≤ T`, any `δ`-stable solver `A` whose endpoint outputs
are the all-`false` and all-`true` assignments must fail to satisfy `path t` for some
`t ≤ T`. -/
theorem isingChainCNF_rules_out_stable_solver {n : ℕ} (hn : 2 ≤ n)
    (A : CNF n → Assignment n) (path : ℕ → CNF n) (T δ : ℕ)
    (hδ : δ < n)
    (hSub : ∀ t ≤ T, ∀ c ∈ isingChainCNF n, c ∈ path t)
    (hStab : IsStableSolver A path T δ)
    (h0 : A (path 0) = (fun _ => false))
    (hT : A (path T) = (fun _ => true)) :
    ¬ (∀ t ≤ T, Satisfies (path t) (A (path t))) := by
  have hPos : 0 < n := by omega
  have hCOGP : HasCoupledOGP path T 0 n := isingChainCNF_hasCoupledOGP hPos path T hSub
  have hGap : 0 + δ < n := by omega
  have hSep : n ≤ hammingDist (A (path 0)) (A (path T)) := by
    rw [h0, hT, hammingDist_const_false_true]
  exact ogp_rules_out_stable_solver A path T 0 n δ hCOGP hGap hStab hSep

/-! ## 2. Explicit Unsatisfiable High-Symmetry Family: Pigeonhole Principle -/

/-- Variable index encoding the proposition "pigeon `p` is placed in hole `h`"
in the variable space `Fin ((m + 1) * m)`. -/
def pigeonVar (m : ℕ) (p : Fin (m + 1)) (h : Fin m) : Fin ((m + 1) * m) :=
  ⟨p.val * m + h.val, by
    have hp : p.val + 1 ≤ m + 1 := p.isLt
    calc
      p.val * m + h.val < p.val * m + m := Nat.add_lt_add_left h.isLt _
      _ = (p.val + 1) * m := by rw [Nat.succ_mul]
      _ ≤ (m + 1) * m := Nat.mul_le_mul_right m hp⟩

/-- Pigeon clause asserting that pigeon `p` is placed in at least one hole `h : Fin m`. -/
def pigeonClause (m : ℕ) (p : Fin (m + 1)) : Clause ((m + 1) * m) :=
  (List.finRange m).map fun h => ⟨pigeonVar m p h, true⟩

/-- All `m + 1` pigeon clauses of `PHP_{m+1}^m`. -/
def pigeonClauses (m : ℕ) : CNF ((m + 1) * m) :=
  (List.finRange (m + 1)).map (pigeonClause m)

/-- Hole exclusivity clause asserting that distinct pigeons `p₁` and `p₂` cannot both occupy
hole `h`. -/
def holeClause (m : ℕ) (p₁ p₂ : Fin (m + 1)) (h : Fin m) : Clause ((m + 1) * m) :=
  [⟨pigeonVar m p₁ h, false⟩, ⟨pigeonVar m p₂ h, false⟩]

/-- All hole exclusivity clauses of `PHP_{m+1}^m`. -/
def holeClauses (m : ℕ) : CNF ((m + 1) * m) :=
  (List.finRange m).flatMap fun h =>
    (List.finRange (m + 1)).flatMap fun p₁ =>
      ((List.finRange (m + 1)).filter (fun p₂ => decide (p₁ ≠ p₂))).map fun p₂ =>
        holeClause m p₁ p₂ h

/-- The Pigeonhole Principle CNF formula `PHP_{m+1}^m` on `(m + 1) * m` variables:
every pigeon occupies at least one hole, and no hole contains two distinct pigeons. -/
def phpCNF (m : ℕ) : CNF ((m + 1) * m) :=
  pigeonClauses m ++ holeClauses m

/-- **Main Theorem 3 (Unsatisfiability of the Pigeonhole Principle CNF)**:
For every `m : ℕ`, the pigeonhole formula `phpCNF m` is unsatisfiable. -/
theorem phpCNF_unsat (m : ℕ) : ¬ Satisfiable (phpCNF m) := by
  rintro ⟨σ, hSat⟩
  have hPigeon : ∀ p : Fin (m + 1), ∃ h : Fin m, σ (pigeonVar m p h) = true := by
    intro p
    have hMem : pigeonClause m p ∈ phpCNF m := by
      simp [phpCNF, pigeonClauses]
    have hEval := hSat _ hMem
    simp only [pigeonClause, evalClause, List.any_map, List.any_eq_true, List.mem_finRange,
      true_and, Function.comp_apply, evalLiteral, beq_true] at hEval
    exact hEval
  choose f hf using hPigeon
  have hCard : Fintype.card (Fin m) < Fintype.card (Fin (m + 1)) := by simp
  rcases Fintype.exists_ne_map_eq_of_card_lt f hCard with ⟨p₁, p₂, hne, hEq⟩
  have hMem : holeClause m p₁ p₂ (f p₁) ∈ phpCNF m := by
    simp only [phpCNF, List.mem_append, holeClauses, List.mem_flatMap, List.mem_finRange,
      true_and, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨f p₁, p₁, p₂, hne, rfl⟩
  have hEval := hSat _ hMem
  have hf1 : σ (pigeonVar m p₁ (f p₁)) = true := hf p₁
  have hf2 : σ (pigeonVar m p₂ (f p₁)) = true := by
    rw [hEq]
    exact hf p₂
  simp only [holeClause, evalClause, evalLiteral, List.any_cons, List.any_nil,
    Bool.or_false, hf1, hf2] at hEval
  exact Bool.false_ne_true hEval

end Mathmatica.ExplicitBarriers
