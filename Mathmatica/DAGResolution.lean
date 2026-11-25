/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.BSWTradeoff
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-!
# General DAG Resolution and Ben-Sasson–Wigderson Fat-Clause Decay

This module formalizes general DAG-like propositional resolution (the proof-theoretic model
underlying CDCL SAT solvers) together with the combinatorial core of the Ben-Sasson–Wigderson
(2001) width–size tradeoff for general resolution: the double-counting averaging lemma for fat
clauses and the resulting geometric decay under single-literal restrictions.

## Main definitions

* `IsResolvent c₁ c₂ c`: `c` is obtained by resolving `c₁` and `c₂` on some variable `v : Fin n`.
* `IsDAGProof φ π`: A clause sequence `π` in which every clause is either an axiom from `φ` or a
  resolvent of two earlier clauses in `π`.
* `dagSize π` and `dagWidth π`: The length and maximum clause cardinality of a DAG proof `π`.
* `IsDAGRefutation φ π`: A DAG proof from `φ` containing the empty clause `∅`.
* `fatClauses F k`: The subset of clauses in `F` with cardinality strictly greater than `k`.

## Main results

* `exists_popular_lit_in_fatClauses`: Double-counting averaging lemma (BSW 2001, Lemma 3.5): if
  every clause in `B` has width at least `k` and `0 < n`, there exists a literal `l : Lit n` such
  that `k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card`.
* `restrict_shrinks_fatClauses`: Removing clauses satisfied by such a popular literal shrinks `B`
  by a factor of `(2 * n - k) / (2 * n)` in exact integer form:
  `2 * n * (B.filter (fun c => l ∉ c)).card ≤ (2 * n - k) * B.card`.
* `restrict_strictly_shrinks_fatClauses`: For nonempty `B` and `0 < k ≤ 2 * n`, the number of
  surviving fat clauses strictly decreases.
* `geometric_decay_fatClauses`: Iterating the single-step shrinking bound `r` times yields the
  exact exponential decay `(2 * n) ^ r * b r ≤ (2 * n - k) ^ r * b 0`.

## References

* E. Ben-Sasson and A. Wigderson, *Short proofs are narrow — resolution made simple*,
  Journal of the ACM 48 (2001), no. 2, 149–169.
-/

namespace Mathmatica.DAGResolution

open Mathmatica.BSWTradeoff

/-! ### General DAG resolution (CDCL proof system) -/

/-- A clause `c` is the resolvent of `c₁` and `c₂` if there exists a pivot variable `v : Fin n`
such that `⟨v, true⟩ ∈ c₁`, `⟨v, false⟩ ∈ c₂`, and
`c = (c₁.erase ⟨v, true⟩) ∪ (c₂.erase ⟨v, false⟩)`. -/
def IsResolvent {n : ℕ} (c₁ c₂ c : Clause n) : Prop :=
  ∃ v : Fin n,
    Lit.mk v true ∈ c₁ ∧
    Lit.mk v false ∈ c₂ ∧
    c = (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))

/-- A general DAG resolution proof from a CNF formula `φ`: a finite sequence `π` of clauses in
which each clause `π[i]` is either an input clause of `φ` or the resolvent of two earlier clauses
`π[j]` and `π[k]` (`j < i`, `k < i`). -/
def IsDAGProof {n : ℕ} (φ : CNF n) (π : List (Clause n)) : Prop :=
  ∀ (i : ℕ) (hi : i < π.length),
    π[i] ∈ φ ∨
      ∃ (j k : ℕ) (hj : j < i) (hk : k < i),
        IsResolvent (π[j]'(lt_trans hj hi)) (π[k]'(lt_trans hk hi)) π[i]

/-- The size of a DAG resolution proof, defined as the number of clauses in the sequence. -/
def dagSize {n : ℕ} (π : List (Clause n)) : ℕ :=
  π.length

/-- The width of a DAG resolution proof, defined as the maximum cardinality of any clause in the
sequence (or `0` for the empty sequence). -/
def dagWidth {n : ℕ} (π : List (Clause n)) : ℕ :=
  π.foldr (fun c acc => max c.card acc) 0

@[simp]
lemma dagWidth_nil {n : ℕ} : dagWidth ([] : List (Clause n)) = 0 := rfl

@[simp]
lemma dagWidth_cons {n : ℕ} (c : Clause n) (π : List (Clause n)) :
    dagWidth (c :: π) = max c.card (dagWidth π) := rfl

/-- Every clause appearing in `π` has cardinality at most `dagWidth π`. -/
lemma card_le_dagWidth {n : ℕ} {c : Clause n} {π : List (Clause n)} (hc : c ∈ π) :
    c.card ≤ dagWidth π := by
  induction π with
  | nil => simp at hc
  | cons d tl ih =>
    simp only [List.mem_cons] at hc
    rw [dagWidth_cons]
    rcases hc with rfl | htl
    · exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

/-- The width of a DAG proof is at most `w` if and only if every clause in it has width at most
`w`. -/
lemma dagWidth_le_iff {n : ℕ} {π : List (Clause n)} {w : ℕ} :
    dagWidth π ≤ w ↔ ∀ c ∈ π, c.card ≤ w := by
  induction π with
  | nil => simp
  | cons d tl ih =>
    simp only [dagWidth_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

/-- A general DAG resolution refutation of `φ` is a DAG resolution proof from `φ` that derives the
empty clause `∅`. -/
def IsDAGRefutation {n : ℕ} (φ : CNF n) (π : List (Clause n)) : Prop :=
  IsDAGProof φ π ∧ ∅ ∈ π

/-! ### Finiteness of literals and fat clauses -/

/-- Equivalence between `Lit n` and `Fin n × Bool`. -/
def litEquivProd (n : ℕ) : Lit n ≃ Fin n × Bool where
  toFun l := (l.var, l.pol)
  invFun p := ⟨p.1, p.2⟩
  left_inv l := by cases l; rfl
  right_inv p := by cases p; rfl

instance instFintypeLit (n : ℕ) : Fintype (Lit n) :=
  Fintype.ofEquiv (Fin n × Bool) (litEquivProd n).symm

/-- There are exactly `2 * n` literals over `n` Boolean variables. -/
@[simp]
lemma card_lit (n : ℕ) : Fintype.card (Lit n) = 2 * n := by
  rw [Fintype.card_congr (litEquivProd n), Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, mul_comm]

/-- The set of *fat clauses* in `F` with respect to width threshold `k`: all clauses in `F` whose
cardinality is strictly greater than `k`. -/
def fatClauses {n : ℕ} (F : Finset (Clause n)) (k : ℕ) : Finset (Clause n) :=
  F.filter (fun c => k < c.card)

lemma mem_fatClauses {n : ℕ} {F : Finset (Clause n)} {k : ℕ} {c : Clause n} :
    c ∈ fatClauses F k ↔ c ∈ F ∧ k < c.card :=
  Finset.mem_filter

lemma fatClauses_eq_empty_iff {n : ℕ} {F : Finset (Clause n)} {k : ℕ} :
    fatClauses F k = ∅ ↔ ∀ c ∈ F, c.card ≤ k := by
  simp [fatClauses, Finset.filter_eq_empty_iff]

/-- A DAG proof `π` has width at most `k` if and only if its clause set contains no fat clauses
of width strictly greater than `k`. -/
lemma fatClauses_toFinset_eq_empty_iff {n : ℕ} {π : List (Clause n)} {k : ℕ} :
    fatClauses π.toFinset k = ∅ ↔ dagWidth π ≤ k := by
  rw [fatClauses_eq_empty_iff, dagWidth_le_iff]
  simp

/-! ### Double counting and the BSW averaging lemma -/

/-- Double counting of literal–clause incidences: the sum of clause cardinalities over `B` equals
the sum over all literals `l` of the number of clauses in `B` containing `l`. -/
lemma sum_card_eq_sum_filter_card {n : ℕ} (B : Finset (Clause n)) :
    ∑ c ∈ B, c.card = ∑ l : Lit n, (B.filter (fun c => l ∈ c)).card := by
  calc
    ∑ c ∈ B, c.card
        = ∑ c ∈ B, ∑ l : Lit n, if l ∈ c then (1 : ℕ) else 0 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const_nat (fun _ _ => rfl), mul_one]
          congr 1
          ext l
          simp
    _ = ∑ l : Lit n, ∑ c ∈ B, if l ∈ c then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ l : Lit n, (B.filter (fun c => l ∈ c)).card := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const_nat (fun _ _ => rfl), mul_one]

/-- **Ben-Sasson–Wigderson (2001) Fat-Clause Averaging Lemma (Lemma 3.5)**:
If `0 < n` and every clause in `B : Finset (Clause n)` has cardinality at least `k`, then there
exists a literal `l : Lit n` occurring in at least a `k / (2 * n)` fraction of the clauses in `B`,
expressed in exact integer form as `k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card`. -/
theorem exists_popular_lit_in_fatClauses {n k : ℕ} (hn : 0 < n) (B : Finset (Clause n))
    (hB : ∀ c ∈ B, k ≤ c.card) :
    ∃ l : Lit n, k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card := by
  have huniv : (Finset.univ : Finset (Lit n)).Nonempty :=
    ⟨Lit.mk ⟨0, hn⟩ true, Finset.mem_univ _⟩
  obtain ⟨l₀, _, hl₀_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Lit n))
      (fun l => (B.filter (fun c => l ∈ c)).card) huniv
  refine ⟨l₀, ?_⟩
  have hlow : k * B.card ≤ ∑ c ∈ B, c.card := by
    calc
      k * B.card = ∑ _c ∈ B, k := by
            rw [Finset.sum_const_nat (fun _ _ => rfl), mul_comm]
      _ ≤ ∑ c ∈ B, c.card := Finset.sum_le_sum fun c hc => hB c hc
  have hup : ∑ l : Lit n, (B.filter (fun c => l ∈ c)).card ≤
      2 * n * (B.filter (fun c => l₀ ∈ c)).card := by
    calc
      ∑ l : Lit n, (B.filter (fun c => l ∈ c)).card
          ≤ ∑ _l : Lit n, (B.filter (fun c => l₀ ∈ c)).card :=
            Finset.sum_le_sum fun l _ => hl₀_max l (Finset.mem_univ l)
      _ = Fintype.card (Lit n) * (B.filter (fun c => l₀ ∈ c)).card := by
            rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
      _ = 2 * n * (B.filter (fun c => l₀ ∈ c)).card := by rw [card_lit]
  exact le_trans hlow (by rw [sum_card_eq_sum_filter_card]; exact hup)

/-! ### Single-step restriction decay and geometric decay -/

/-- **Single-Step Fat-Clause Shrinking Theorem**:
If `k ≤ 2 * n` and `l` satisfies the averaging bound
`k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card`, then deleting all clauses containing `l`
leaves `B' := B.filter (fun c => l ∉ c)` satisfying the exact integer contraction inequality
`2 * n * B'.card ≤ (2 * n - k) * B.card`. -/
theorem restrict_shrinks_fatClauses {n k : ℕ} (hk : k ≤ 2 * n)
    (B : Finset (Clause n)) (l : Lit n)
    (hl : k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card) :
    2 * n * (B.filter (fun c => l ∉ c)).card ≤ (2 * n - k) * B.card := by
  have hpart :
      (B.filter (fun c => l ∈ c)).card + (B.filter (fun c => l ∉ c)).card = B.card :=
    Finset.card_filter_add_card_filter_not (fun c => l ∈ c)
  have hmul :
      2 * n * (B.filter (fun c => l ∈ c)).card + 2 * n * (B.filter (fun c => l ∉ c)).card =
        2 * n * B.card := by
    rw [← Nat.mul_add, hpart]
  have hsub : (2 * n - k) * B.card + k * B.card = 2 * n * B.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hk]
  omega

/-- Combined single-step fat-clause contraction: whenever `0 < n`, `k ≤ 2 * n`, and every clause in
`B` has width at least `k`, there exists a literal `l : Lit n` whose elimination contracts `B` by
at least the factor `(2 * n - k) / (2 * n)`. -/
theorem exists_lit_restrict_shrinks_fatClauses {n k : ℕ} (hn : 0 < n) (hk : k ≤ 2 * n)
    (B : Finset (Clause n)) (hB : ∀ c ∈ B, k ≤ c.card) :
    ∃ l : Lit n, 2 * n * (B.filter (fun c => l ∉ c)).card ≤ (2 * n - k) * B.card := by
  obtain ⟨l, hl⟩ := exists_popular_lit_in_fatClauses hn B hB
  exact ⟨l, restrict_shrinks_fatClauses hk B l hl⟩

/-- Restricting a CNF formula `F` by a literal `l` yields at most as many fat clauses (of width
`> k`) as the number of fat clauses of `F` that do not contain `l`. -/
lemma card_fatClauses_restrictCNF_le {n k : ℕ} (l : Lit n) (F : CNF n) :
    (fatClauses (restrictCNF l F) k).card ≤
      ((fatClauses F k).filter (fun c => l ∉ c)).card := by
  have hsub :
      fatClauses (restrictCNF l F) k ⊆
        ((fatClauses F k).filter (fun c => l ∉ c)).image (fun c => c.erase l.neg) := by
    intro c hc
    rw [mem_fatClauses, mem_restrictCNF] at hc
    obtain ⟨⟨d, hdF, hnd, rfl⟩, hkcard⟩ := hc
    rw [Finset.mem_image]
    refine ⟨d, ?_, rfl⟩
    rw [Finset.mem_filter, mem_fatClauses]
    exact ⟨⟨hdF, lt_of_lt_of_le hkcard Finset.card_erase_le⟩, hnd⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- **Strict Monotonicity Corollary**:
If `0 < k ≤ 2 * n`, `B` is nonempty, and `l` satisfies the averaging bound, then eliminating
clauses containing `l` strictly reduces the number of fat clauses. -/
theorem restrict_strictly_shrinks_fatClauses {n k : ℕ} (hk_pos : 0 < k)
    (hk : k ≤ 2 * n) (B : Finset (Clause n)) (hBne : B.Nonempty) (l : Lit n)
    (hl : k * B.card ≤ 2 * n * (B.filter (fun c => l ∈ c)).card) :
    (B.filter (fun c => l ∉ c)).card < B.card := by
  have hshrink := restrict_shrinks_fatClauses hk B l hl
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  have hlt : (2 * n - k) * B.card < 2 * n * B.card :=
    Nat.mul_lt_mul_of_pos_right (by omega) hBpos
  have hmul_lt : 2 * n * (B.filter (fun c => l ∉ c)).card < 2 * n * B.card :=
    lt_of_le_of_lt hshrink hlt
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

/-- **Iterated Geometric Decay Theorem**:
If a sequence `b : ℕ → ℕ` satisfies the single-step contraction inequality
`2 * n * b (t + 1) ≤ (2 * n - k) * b t` for all `t < r`, then after `r` steps it obeys the exact
exponential decay bound `(2 * n) ^ r * b r ≤ (2 * n - k) ^ r * b 0`. -/
theorem geometric_decay_fatClauses {n k : ℕ} (b : ℕ → ℕ) :
    ∀ r : ℕ,
      (∀ t < r, 2 * n * b (t + 1) ≤ (2 * n - k) * b t) →
      (2 * n) ^ r * b r ≤ (2 * n - k) ^ r * b 0
  | 0, _ => by simp
  | r + 1, hstep => by
    have ih := geometric_decay_fatClauses b r fun t ht => hstep t (Nat.lt_succ_of_lt ht)
    have hlast := hstep r (Nat.lt_succ_self r)
    calc
      (2 * n) ^ (r + 1) * b (r + 1)
          = (2 * n) ^ r * (2 * n * b (r + 1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (2 * n) ^ r * ((2 * n - k) * b r) := Nat.mul_le_mul_left _ hlast
      _ = (2 * n - k) * ((2 * n) ^ r * b r) := by
            rw [← Nat.mul_assoc, Nat.mul_comm ((2 * n) ^ r), Nat.mul_assoc]
      _ ≤ (2 * n - k) * ((2 * n - k) ^ r * b 0) := Nat.mul_le_mul_left _ ih
      _ = (2 * n - k) ^ (r + 1) * b 0 := by
            rw [← Nat.mul_assoc, Nat.mul_comm (2 * n - k), ← Nat.pow_succ]

end Mathmatica.DAGResolution
