/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Fintype.BigOperators
import Mathmatica.BSWTradeoff

/-!
# Pudlák–Impagliazzo Prover–Delayer Game and Tree-like Resolution Lower Bounds

This module formalizes the Prover–Delayer game of Pudlák and Impagliazzo (2000) for proving
exponential lower bounds on the size of tree-like resolution refutations (`ResTree`).

In the game, Prover walks down a tree-like resolution refutation from the empty clause to an
unsatisfied axiom clause while maintaining a partial Boolean assignment `ρ` that falsifies the
current clause. At each resolution step on a variable `v`, Delayer either forces `v` to a Boolean
value `b` (earning `0` points) or defers the choice to Prover (earning `1` point).

## Main definitions

* `PartAssign n`: A partial Boolean assignment `Fin n → Option Bool`.
* `falsifiesLit ρ l`, `falsifiesClause ρ c`: Semantic falsification of literals and clauses under
  a partial assignment.
* `assignVar ρ v b`: Updating a partial assignment at variable `v` to value `b`.
* `DelayerResponse`, `DelayerStrategy n`: Moves and strategies for Delayer.
* `ConsistentStrategy S`: A strategy that agrees with already-assigned variables in `ρ`.
* `minScore S ρ T`: Minimum score guaranteed by Delayer strategy `S` against an optimal Prover
  descending the tree-like resolution proof `T` from partial assignment `ρ`.
* `ScoresAtLeast S φ k ρ`: Purely semantic inductive predicate asserting that Delayer strategy `S`
  earns at least `k` points before reaching any clause of `φ` falsified by the current assignment.
* `allClauses n`: The complete unsatisfiable CNF formula consisting of all `2 ^ n` full-width
  clauses over `n` variables.

## Main results

* `prover_delayer_size_lower_bound`: For every tree-like resolution proof `T`, strategy `S`, and
  partial assignment `ρ`, `2 ^ minScore S ρ T ≤ T.size`.
* `minScore_ge_of_scoresAtLeast`: If `S` is consistent, `ρ` falsifies `c`, and
  `ScoresAtLeast S φ k ρ`, then `k ≤ minScore S ρ T` for every `T : ResTree φ c`.
* `size_lower_bound_of_adversary`: If `S` is consistent and `ScoresAtLeast S φ k ρ`, then every
  tree-like resolution refutation `T : ResTree φ ∅` satisfies `2 ^ k ≤ T.size`.
* `allClauses_size_lower_bound`: Every tree-like resolution refutation
  `T : ResTree (allClauses n) ∅` satisfies `2 ^ n ≤ T.size`.

## References

* P. Pudlák and R. Impagliazzo, *A lower bound for DLL algorithms for k-SAT (preliminary version)*,
  Proceedings of the 11th Annual ACM–SIAM Symposium on Discrete Algorithms (SODA 2000), 128–136.
-/

namespace Mathmatica.ProverDelayer

open Mathmatica.BSWTradeoff

/-! ### Partial assignments and falsification -/

/-- A partial Boolean assignment on `n` variables. -/
abbrev PartAssign (n : ℕ) := Fin n → Option Bool

/-- The empty partial assignment leaving every variable unassigned. -/
def emptyAssign (n : ℕ) : PartAssign n := fun _ => none

/-- A partial assignment `ρ` falsifies a literal `l` if it assigns `l.var` to `!l.pol`. -/
def falsifiesLit {n : ℕ} (ρ : PartAssign n) (l : Lit n) : Prop :=
  ρ l.var = some (!l.pol)

/-- A partial assignment `ρ` falsifies a clause `c` if it falsifies every literal in `c`. -/
def falsifiesClause {n : ℕ} (ρ : PartAssign n) (c : Clause n) : Prop :=
  ∀ l ∈ c, falsifiesLit ρ l

/-- The empty clause is falsified by every partial assignment. -/
lemma falsifiesClause_empty {n : ℕ} (ρ : PartAssign n) : falsifiesClause ρ ∅ := by
  intro l hl
  exact absurd hl (Finset.notMem_empty l)

/-- Update a partial assignment `ρ` by setting variable `v` to Boolean value `b`. -/
def assignVar {n : ℕ} (ρ : PartAssign n) (v : Fin n) (b : Bool) : PartAssign n :=
  fun i => if i = v then some b else ρ i

@[simp]
lemma assignVar_self {n : ℕ} (ρ : PartAssign n) (v : Fin n) (b : Bool) :
    assignVar ρ v b v = some b := by
  simp [assignVar]

lemma assignVar_ne {n : ℕ} (ρ : PartAssign n) {v i : Fin n} (b : Bool) (h : i ≠ v) :
    assignVar ρ v b i = ρ i := by
  simp [assignVar, h]

lemma assignVar_eq_self {n : ℕ} {ρ : PartAssign n} {v : Fin n} {b : Bool} (h : ρ v = some b) :
    assignVar ρ v b = ρ := by
  funext i
  by_cases hi : i = v
  · subst hi; simp [assignVar, h]
  · simp [assignVar, hi]

lemma falsifiesClause_left_of_none {n : ℕ} {ρ : PartAssign n} {c₁ c₂ : Clause n} {v : Fin n}
    (hv : ρ v = none)
    (hfal : falsifiesClause ρ ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)))) :
    falsifiesClause (assignVar ρ v false) c₁ := by
  intro l hl
  by_cases hlv : l = Lit.mk v true
  · subst hlv
    simp [falsifiesLit, assignVar]
  · have hl' : l ∈ (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)) :=
      Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hl⟩)
    have hfl : falsifiesLit ρ l := hfal l hl'
    have hne : l.var ≠ v := by
      intro heq
      rw [falsifiesLit, heq, hv] at hfl
      cases hfl
    simp [falsifiesLit, assignVar, hne]
    exact hfl

lemma falsifiesClause_right_of_none {n : ℕ} {ρ : PartAssign n} {c₁ c₂ : Clause n} {v : Fin n}
    (hv : ρ v = none)
    (hfal : falsifiesClause ρ ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)))) :
    falsifiesClause (assignVar ρ v true) c₂ := by
  intro l hl
  by_cases hlv : l = Lit.mk v false
  · subst hlv
    simp [falsifiesLit, assignVar]
  · have hl' : l ∈ (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)) :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hl⟩)
    have hfl : falsifiesLit ρ l := hfal l hl'
    have hne : l.var ≠ v := by
      intro heq
      rw [falsifiesLit, heq, hv] at hfl
      cases hfl
    simp [falsifiesLit, assignVar, hne]
    exact hfl

lemma falsifiesClause_left_of_false {n : ℕ} {ρ : PartAssign n} {c₁ c₂ : Clause n} {v : Fin n}
    (hv : ρ v = some false)
    (hfal : falsifiesClause ρ ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)))) :
    falsifiesClause ρ c₁ := by
  intro l hl
  by_cases hlv : l = Lit.mk v true
  · subst hlv
    simpa [falsifiesLit] using hv
  · exact hfal l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hl⟩))

lemma falsifiesClause_right_of_true {n : ℕ} {ρ : PartAssign n} {c₁ c₂ : Clause n} {v : Fin n}
    (hv : ρ v = some true)
    (hfal : falsifiesClause ρ ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)))) :
    falsifiesClause ρ c₂ := by
  intro l hl
  by_cases hlv : l = Lit.mk v false
  · subst hlv
    simpa [falsifiesLit] using hv
  · exact hfal l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hl⟩))

/-! ### Prover–Delayer game and Delayer strategies -/

/-- Delayer's response when Prover queries a variable: either force a Boolean value (scoring `0`)
or defer the choice to Prover (scoring `1`). -/
inductive DelayerResponse
  | force (b : Bool)
  | defer
  deriving DecidableEq

/-- A Delayer strategy chooses a `DelayerResponse` given the current partial assignment and the
queried variable. -/
abbrev DelayerStrategy (n : ℕ) := PartAssign n → Fin n → DelayerResponse

/-- A Delayer strategy is consistent if it forces every already-assigned variable to its existing
value. -/
def ConsistentStrategy {n : ℕ} (S : DelayerStrategy n) : Prop :=
  ∀ (ρ : PartAssign n) (v : Fin n) (b : Bool), ρ v = some b → S ρ v = .force b

/-- The minimum score Delayer guarantees under strategy `S` starting from partial assignment `ρ`
on a tree-like resolution proof `T`. -/
def minScore {n : ℕ} {φ : CNF n} (S : DelayerStrategy n) :
    PartAssign n → ∀ {c : Clause n}, ResTree φ c → ℕ
  | _, _, .axiom_clause _ => 0
  | ρ, _, .resolve v _ _ t₁ t₂ =>
    match S ρ v with
    | .force false => minScore S (assignVar ρ v false) t₁
    | .force true => minScore S (assignVar ρ v true) t₂
    | .defer =>
      1 + min (minScore S (assignVar ρ v false) t₁) (minScore S (assignVar ρ v true) t₂)

/-! ### Main Theorem 1: Exponential size lower bound from game score -/

/-- **Pudlák–Impagliazzo Size Lower Bound**: For any tree-like resolution proof `T`, Delayer
strategy `S`, and initial partial assignment `ρ`, `2 ^ minScore S ρ T ≤ T.size`. -/
theorem prover_delayer_size_lower_bound {n : ℕ} {φ : CNF n}
    (S : DelayerStrategy n) (ρ : PartAssign n) :
    ∀ {c : Clause n} (T : ResTree φ c), 2 ^ minScore S ρ T ≤ T.size
  | _, .axiom_clause _ => by
    simp [minScore, ResTree.size]
  | _, .resolve v _ _ t₁ t₂ => by
    have ih₁ := prover_delayer_size_lower_bound S (assignVar ρ v false) t₁
    have ih₂ := prover_delayer_size_lower_bound S (assignVar ρ v true) t₂
    simp only [minScore, ResTree.size]
    cases hSv : S ρ v with
    | force b =>
      cases b with
      | false =>
        exact le_trans ih₁ (Nat.le_add_right _ _)
      | true =>
        exact le_trans ih₂ (Nat.le_add_left _ _)
    | defer =>
      set s₁ := minScore S (assignVar ρ v false) t₁
      set s₂ := minScore S (assignVar ρ v true) t₂
      have hpow₁ : 2 ^ min s₁ s₂ ≤ 2 ^ s₁ :=
        Nat.pow_le_pow_right (by omega) (Nat.min_le_left s₁ s₂)
      have hpow₂ : 2 ^ min s₁ s₂ ≤ 2 ^ s₂ :=
        Nat.pow_le_pow_right (by omega) (Nat.min_le_right s₁ s₂)
      calc
        2 ^ (1 + min s₁ s₂)
            = 2 ^ min s₁ s₂ + 2 ^ min s₁ s₂ := by
              rw [Nat.add_comm, Nat.pow_succ, Nat.mul_two]
        _ ≤ 2 ^ s₁ + 2 ^ s₂ := Nat.add_le_add hpow₁ hpow₂
        _ ≤ t₁.size + t₂.size := Nat.add_le_add ih₁ ih₂

/-! ### Main Theorem 2: Semantic adversary score guarantee -/

/-- Semantic game invariant asserting that starting from partial assignment `ρ`, Delayer playing
strategy `S` earns at least `k` points along every play before reaching an axiom clause in `φ`
falsified by the current assignment. -/
inductive ScoresAtLeast {n : ℕ} (S : DelayerStrategy n) (φ : CNF n) :
    ℕ → PartAssign n → Prop
  | zero (ρ : PartAssign n) : ScoresAtLeast S φ 0 ρ
  | step {k : ℕ} {ρ : PartAssign n}
      (hno : ∀ c ∈ φ, ¬ falsifiesClause ρ c)
      (hforce : ∀ (v : Fin n) (b : Bool),
        ρ v = none → S ρ v = .force b → ScoresAtLeast S φ k (assignVar ρ v b))
      (hdefer : ∀ (v : Fin n) (b : Bool),
        ρ v = none → S ρ v = .defer → ScoresAtLeast S φ (k - 1) (assignVar ρ v b)) :
      ScoresAtLeast S φ k ρ

/-- If `S` is consistent, `ρ` falsifies `c`, and `ScoresAtLeast S φ k ρ`, then `S` guarantees
score at least `k` on every tree-like resolution proof `T : ResTree φ c`. -/
theorem minScore_ge_of_scoresAtLeast {n : ℕ} {φ : CNF n}
    {S : DelayerStrategy n} (hS : ConsistentStrategy S) :
    ∀ {c : Clause n} (T : ResTree φ c) {k : ℕ} {ρ : PartAssign n},
      falsifiesClause ρ c → ScoresAtLeast S φ k ρ → k ≤ minScore S ρ T
  | c, .axiom_clause hc, k, ρ, hfal, hs => by
    cases hs with
    | zero _ => exact Nat.zero_le _
    | step hno _ _ => exact absurd hfal (hno c hc)
  | _, .resolve v _ _ t₁ t₂, k, ρ, hfal, hs => by
    cases hv : ρ v with
    | some b =>
      have hSv : S ρ v = .force b := hS ρ v b hv
      have hassign : assignVar ρ v b = ρ := assignVar_eq_self hv
      cases b with
      | false =>
        simp only [minScore, hSv, hassign]
        exact minScore_ge_of_scoresAtLeast hS t₁ (falsifiesClause_left_of_false hv hfal) hs
      | true =>
        simp only [minScore, hSv, hassign]
        exact minScore_ge_of_scoresAtLeast hS t₂ (falsifiesClause_right_of_true hv hfal) hs
    | none =>
      cases hs with
      | zero _ => exact Nat.zero_le _
      | step _ hforce hdefer =>
        simp only [minScore]
        cases hSv : S ρ v with
        | force b =>
          cases b with
          | false =>
            exact minScore_ge_of_scoresAtLeast hS t₁
              (falsifiesClause_left_of_none hv hfal) (hforce v false hv hSv)
          | true =>
            exact minScore_ge_of_scoresAtLeast hS t₂
              (falsifiesClause_right_of_none hv hfal) (hforce v true hv hSv)
        | defer =>
          have h₁ := minScore_ge_of_scoresAtLeast hS t₁
            (falsifiesClause_left_of_none hv hfal) (hdefer v false hv hSv)
          have h₂ := minScore_ge_of_scoresAtLeast hS t₂
            (falsifiesClause_right_of_none hv hfal) (hdefer v true hv hSv)
          dsimp only
          omega

/-- **Adversary Size Lower Bound**: If a consistent Delayer strategy `S` guarantees score at least
`k` from `ρ` against `φ`, then every tree-like resolution refutation `T : ResTree φ ∅` has size
at least `2 ^ k`. -/
theorem size_lower_bound_of_adversary {n : ℕ} {φ : CNF n}
    {S : DelayerStrategy n} (hS : ConsistentStrategy S)
    {k : ℕ} {ρ : PartAssign n} (hs : ScoresAtLeast S φ k ρ)
    (T : ResTree φ ∅) : 2 ^ k ≤ T.size := by
  have hscore : k ≤ minScore S ρ T :=
    minScore_ge_of_scoresAtLeast hS T (falsifiesClause_empty ρ) hs
  exact le_trans (Nat.pow_le_pow_right (by omega) hscore)
    (prover_delayer_size_lower_bound S ρ T)

/-! ### Explicit exponential instance: complete full-width CNF -/

/-- The full-width clause over `n` variables with polarities given by `f : Fin n → Bool`. -/
def fullClause {n : ℕ} (f : Fin n → Bool) : Clause n :=
  Finset.univ.image (fun v => Lit.mk v (f v))

/-- The complete unsatisfiable CNF formula consisting of all `2 ^ n` full-width clauses over `n`
variables. -/
def allClauses (n : ℕ) : CNF n :=
  Finset.univ.image (fun f : Fin n → Bool => fullClause f)

lemma fullClause_injective {n : ℕ} : Function.Injective (@fullClause n) := by
  intro f g hfg
  funext v
  have hv : Lit.mk v (f v) ∈ fullClause g := by
    rw [← hfg]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ v)
  rw [fullClause, Finset.mem_image] at hv
  obtain ⟨w, _, hw⟩ := hv
  have hvw : w = v := congrArg Lit.var hw
  subst hvw
  exact (congrArg Lit.pol hw).symm

/-- `allClauses n` contains exactly `2 ^ n` distinct full-width clauses. -/
lemma allClauses_card (n : ℕ) : (allClauses n).card = 2 ^ n := by
  rw [allClauses, Finset.card_image_of_injective _ fullClause_injective]
  simp

/-- The Delayer strategy that defers every unassigned variable and respects assigned variables. -/
def deferUnassigned {n : ℕ} : DelayerStrategy n :=
  fun ρ v =>
    match ρ v with
    | some b => .force b
    | none => .defer

lemma deferUnassigned_consistent {n : ℕ} : ConsistentStrategy (@deferUnassigned n) := by
  intro ρ v b hv
  simp [deferUnassigned, hv]

/-- The set of variables left unassigned by `ρ`. -/
def unassignedVars {n : ℕ} (ρ : PartAssign n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ρ v = none)

/-- The number of variables left unassigned by `ρ`. -/
def unassignedCount {n : ℕ} (ρ : PartAssign n) : ℕ :=
  (unassignedVars ρ).card

lemma unassignedCount_empty (n : ℕ) : unassignedCount (emptyAssign n) = n := by
  simp [unassignedCount, unassignedVars, emptyAssign]

lemma unassignedVars_assignVar {n : ℕ} (ρ : PartAssign n) (v : Fin n) (b : Bool) :
    unassignedVars (assignVar ρ v b) = (unassignedVars ρ).erase v := by
  ext i
  rw [unassignedVars, unassignedVars, Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
  by_cases hi : i = v
  · subst hi; simp [assignVar]
  · simp [assignVar, hi]

lemma unassignedCount_assignVar {n : ℕ} {ρ : PartAssign n} {v : Fin n} (b : Bool)
    (hv : ρ v = none) : unassignedCount (assignVar ρ v b) + 1 = unassignedCount ρ := by
  rw [unassignedCount, unassignedCount, unassignedVars_assignVar]
  have hmem : v ∈ unassignedVars ρ := by
    simp [unassignedVars, hv]
  exact Finset.card_erase_add_one hmem

lemma not_falsifiesClause_allClauses_of_unassigned {n : ℕ} {ρ : PartAssign n} {v : Fin n}
    (hv : ρ v = none) {c : Clause n} (hc : c ∈ allClauses n) : ¬ falsifiesClause ρ c := by
  intro hfal
  rw [allClauses, Finset.mem_image] at hc
  obtain ⟨f, _, rfl⟩ := hc
  have hl : Lit.mk v (f v) ∈ fullClause f := Finset.mem_image_of_mem _ (Finset.mem_univ v)
  have hfl : falsifiesLit ρ (Lit.mk v (f v)) := hfal _ hl
  rw [falsifiesLit] at hfl
  simp only at hfl
  rw [hv] at hfl
  cases hfl

/-- Under `deferUnassigned`, Delayer earns at least `unassignedCount ρ` points on
`allClauses n`. -/
lemma scoresAtLeast_allClauses {n : ℕ} :
    ∀ (m : ℕ) (ρ : PartAssign n),
      unassignedCount ρ = m → ScoresAtLeast deferUnassigned (allClauses n) m ρ
  | 0, ρ, _ => ScoresAtLeast.zero ρ
  | m + 1, ρ, hm => by
    refine ScoresAtLeast.step ?_ ?_ ?_
    · intro c hc
      have hpos : 0 < (unassignedVars ρ).card := by
        rw [← unassignedCount, hm]
        exact Nat.succ_pos m
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      have hv' : ρ v = none := (Finset.mem_filter.mp hv).2
      exact not_falsifiesClause_allClauses_of_unassigned hv' hc
    · intro v b hv hSv
      simp [deferUnassigned, hv] at hSv
    · intro v b hv _
      have hdec : unassignedCount (assignVar ρ v b) = m := by
        have h := unassignedCount_assignVar b hv
        omega
      exact scoresAtLeast_allClauses m (assignVar ρ v b) hdec

/-- **Explicit Exponential Tree-like Resolution Lower Bound**: Every tree-like resolution
refutation of the complete `n`-variable CNF `allClauses n` has size at least `2 ^ n`. -/
theorem allClauses_size_lower_bound (n : ℕ) (T : ResTree (allClauses n) ∅) :
    2 ^ n ≤ T.size :=
  size_lower_bound_of_adversary deferUnassigned_consistent
    (scoresAtLeast_allClauses n (emptyAssign n) (unassignedCount_empty n)) T

end Mathmatica.ProverDelayer
