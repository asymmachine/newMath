/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sum

/-!
# Boolean Circuits, Counting Lower Bounds, and the Natural Proofs Barrier

This module formalizes foundational circuit complexity models and the Razborov–Rudich natural
proofs barrier in a self-contained combinatorial setting:

1. **Boolean Functions and Bounded-Size Circuits (DAG / Straight-Line Programs)**:
   - `BoolFn n := (Fin n → Bool) → Bool` and exact cardinality
     `card_boolFn : Fintype.card (BoolFn n) = 2 ^ (2 ^ n)`.
   - `GateOp` (`not`, `and`, `or`), `Gate n i`, and `Circuit n s` representing straight-line
     Boolean circuits with `s` gates where gate `i` reads from inputs `Fin n` or earlier gates
     `Fin i`.
   - `Circuit.eval : Circuit n s → BoolFn n`, `HasCircuitSize`, and exact/upper cardinality
     bounds on `Circuit n s`.

2. **Counting Lower Bounds (Abstract Shannon Existence Theorem)**:
   - `exists_hard_boolFn_of_card_lt`: any `Small : Finset (BoolFn n)` with
     `Small.card < 2 ^ (2 ^ n)` omits at least one Boolean function.
   - `exists_hard_boolFn_of_circuit_card_lt` and `exists_hard_boolFn_of_bound_lt`: explicit
     circuit-size lower-bound corollaries whenever the circuit count is strictly below
     `2 ^ (2 ^ n)`.

3. **Razborov–Rudich Natural Proofs Barrier (`NaturalProperty`)**:
   - `Property n`, `IsUseful`, `IsLarge`, `IsNaturalAgainst`, and `NaturalProperty`.
   - `PRFamily n s` (pseudorandom function families computable by size-`s` circuits) and
     `Distinguishes P F den`.
   - `natural_property_hits_prg_barrier`: any property satisfying usefulness and largeness
     vanishes identically on every size-`s` circuit family while accepting at least a `1 / den`
     fraction of all Boolean functions, thereby distinguishing every size-`s` PRF family from
     uniform random functions with advantage at least `1 / den`.
-/

namespace Mathmatica.ComplexityBarriers

/-! ## 1. Boolean Functions and Straight-Line Boolean Circuits -/

/-- The type of `n`-variable Boolean functions `(Fin n → Bool) → Bool`. -/
abbrev BoolFn (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- There are exactly `2 ^ (2 ^ n)` Boolean functions on `n` variables. -/
theorem card_boolFn (n : ℕ) : Fintype.card (BoolFn n) = 2 ^ (2 ^ n) := by
  simp [BoolFn, Fintype.card_bool, Fintype.card_fin]

/-- Elementary Boolean gate operations. -/
inductive GateOp : Type
  | not
  | and
  | or
  deriving DecidableEq, Repr

/-- Equivalence between `GateOp` and `Fin 3`. -/
def gateOpEquivFin3 : GateOp ≃ Fin 3 where
  toFun
    | .not => ⟨0, by decide⟩
    | .and => ⟨1, by decide⟩
    | .or => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .not
    | ⟨1, _⟩ => .and
    | ⟨2, _⟩ => .or
  left_inv g := by cases g <;> rfl
  right_inv
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

instance : Fintype GateOp :=
  Fintype.ofEquiv (Fin 3) gateOpEquivFin3.symm

/-- There are exactly 3 elementary gate operations (`not`, `and`, `or`). -/
theorem card_gateOp : Fintype.card GateOp = 3 := by
  rw [Fintype.card_congr gateOpEquivFin3, Fintype.card_fin]

/-- A single gate at topological index `i` in an `n`-input straight-line circuit.
Each operand wire selects either an input (`Sum.inl`) or an earlier gate (`Sum.inr`).
Unary `GateOp.not` reads `left` and ignores `right`. -/
structure Gate (n i : ℕ) where
  op : GateOp
  left : Fin n ⊕ Fin i
  right : Fin n ⊕ Fin i
  deriving DecidableEq

/-- Equivalence unpacking `Gate n i` into its operation and two input wires. -/
def gateEquiv (n i : ℕ) : Gate n i ≃ GateOp × (Fin n ⊕ Fin i) × (Fin n ⊕ Fin i) where
  toFun g := (g.op, g.left, g.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv g := by cases g; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance (n i : ℕ) : Fintype (Gate n i) :=
  Fintype.ofEquiv _ (gateEquiv n i).symm

/-- Exact count of possible gates at index `i` in an `n`-input circuit. -/
theorem card_gate (n i : ℕ) : Fintype.card (Gate n i) = 3 * (n + i) ^ 2 := by
  rw [Fintype.card_congr (gateEquiv n i)]
  simp [card_gateOp, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, sq]

/-- A straight-line (DAG) Boolean circuit on `n` inputs with `s` gates and a designated output
wire (either an input or one of the `s` gates). -/
structure Circuit (n s : ℕ) where
  gates : (i : Fin s) → Gate n i.val
  output : Fin n ⊕ Fin s

/-- Equivalence unpacking `Circuit n s` into its gate sequence and output wire. -/
def circuitEquiv (n s : ℕ) :
    Circuit n s ≃ ((i : Fin s) → Gate n i.val) × (Fin n ⊕ Fin s) where
  toFun C := (C.gates, C.output)
  invFun p := ⟨p.1, p.2⟩
  left_inv C := by cases C; rfl
  right_inv p := by rcases p with ⟨_, _⟩; rfl

instance (n s : ℕ) : Fintype (Circuit n s) :=
  Fintype.ofEquiv _ (circuitEquiv n s).symm

/-- Exact cardinality of the space of `n`-input, `s`-gate circuits. -/
theorem card_circuit (n s : ℕ) :
    Fintype.card (Circuit n s) = (∏ i : Fin s, 3 * (n + i.val) ^ 2) * (n + s) := by
  rw [Fintype.card_congr (circuitEquiv n s), Fintype.card_prod, Fintype.card_pi,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  congr 1
  exact Finset.prod_congr rfl fun i _ => card_gate n i.val

/-- Elementary closed-form upper bound on the number of `n`-input, `s`-gate circuits. -/
theorem card_circuit_le (n s : ℕ) :
    Fintype.card (Circuit n s) ≤ (3 * (n + s) ^ 2) ^ s * (n + s) := by
  rw [card_circuit]
  apply Nat.mul_le_mul_right
  have hprod :
      (∏ i : Fin s, 3 * (n + i.val) ^ 2) ≤ ∏ _i : Fin s, 3 * (n + s) ^ 2 := by
    have h : ∀ (t : Finset (Fin s)),
        (∏ i ∈ t, 3 * (n + i.val) ^ 2) ≤ ∏ _i ∈ t, 3 * (n + s) ^ 2 := by
      intro t
      induction t using Finset.cons_induction with
      | empty => simp
      | cons a t ha ih =>
        rw [Finset.prod_cons, Finset.prod_cons]
        apply Nat.mul_le_mul _ ih
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (Nat.add_le_add_left (Nat.le_of_lt a.isLt) n) 2
    exact h Finset.univ
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

/-- Evaluate gate `k` (with `k < s`) of circuit `C` on input `x` by well-founded recursion
on the topological gate index `k`. -/
def Circuit.evalGate {n s : ℕ} (C : Circuit n s) (x : Fin n → Bool) :
    (k : ℕ) → k < s → Bool
  | k, hk =>
    let g := C.gates ⟨k, hk⟩
    let evalW : Fin n ⊕ Fin k → Bool
      | Sum.inl idx => x idx
      | Sum.inr prev => C.evalGate x prev.val (Nat.lt_trans prev.isLt hk)
    match g.op with
    | .not => !(evalW g.left)
    | .and => evalW g.left && evalW g.right
    | .or => evalW g.left || evalW g.right

/-- Evaluate an `n`-input, `s`-gate circuit to the Boolean function it computes. -/
def Circuit.eval {n s : ℕ} (C : Circuit n s) : BoolFn n :=
  fun x =>
    match C.output with
    | Sum.inl idx => x idx
    | Sum.inr gateIdx => C.evalGate x gateIdx.val gateIdx.isLt

/-- A Boolean function `f : BoolFn n` has circuit size `s` if it is computed by some
`s`-gate circuit `C : Circuit n s`. -/
def HasCircuitSize {n : ℕ} (f : BoolFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit n s, C.eval = f

/-! ## 2. Counting Lower Bounds (Abstract Shannon Existence Theorem) -/

/-- Abstract Shannon counting lemma: any finite set `Small` of `n`-variable Boolean functions
of cardinality strictly less than `2 ^ (2 ^ n)` misses at least one Boolean function. -/
theorem exists_hard_boolFn_of_card_lt {n : ℕ} (Small : Finset (BoolFn n))
    (hcard : Small.card < 2 ^ (2 ^ n)) :
    ∃ f : BoolFn n, f ∉ Small := by
  by_contra h
  have hmem : ∀ f : BoolFn n, f ∈ Small := fun f =>
    Classical.byContradiction fun hf => h ⟨f, hf⟩
  have huniv : Small = Finset.univ := Finset.eq_univ_iff_forall.mpr hmem
  rw [huniv, Finset.card_univ, card_boolFn] at hcard
  exact Nat.lt_irrefl _ hcard

/-- General model-counting corollary: any finite model class `α` with evaluation map
`eval : α → BoolFn n` and `Fintype.card α < 2 ^ (2 ^ n)` fails to compute at least one
`n`-variable Boolean function. -/
theorem exists_not_in_range_of_card_lt {n : ℕ} {α : Type*} [Fintype α]
    (eval : α → BoolFn n) (hcard : Fintype.card α < 2 ^ (2 ^ n)) :
    ∃ f : BoolFn n, ∀ a : α, eval a ≠ f := by
  classical
  have himg : (Finset.univ.image eval).card < 2 ^ (2 ^ n) :=
    lt_of_le_of_lt Finset.card_image_le (by simpa using hcard)
  obtain ⟨f, hf⟩ := exists_hard_boolFn_of_card_lt (Finset.univ.image eval) himg
  refine ⟨f, fun a ha => hf ?_⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩

/-- Concrete circuit-size counting lower bound: whenever `Fintype.card (Circuit n s) < 2 ^ (2 ^ n)`,
there exists an `n`-variable Boolean function with no `s`-gate circuit. -/
theorem exists_hard_boolFn_of_circuit_card_lt {n s : ℕ}
    (hcard : Fintype.card (Circuit n s) < 2 ^ (2 ^ n)) :
    ∃ f : BoolFn n, ¬ HasCircuitSize f s := by
  obtain ⟨f, hf⟩ := exists_not_in_range_of_card_lt (Circuit.eval (n := n) (s := s)) hcard
  exact ⟨f, fun ⟨C, hC⟩ => hf C hC⟩

/-- Explicit closed-form Shannon lower-bound corollary: if
`(3 * (n + s) ^ 2) ^ s * (n + s) < 2 ^ (2 ^ n)`, then some `n`-variable Boolean function
cannot be computed by any `s`-gate circuit. -/
theorem exists_hard_boolFn_of_bound_lt {n s : ℕ}
    (hbound : (3 * (n + s) ^ 2) ^ s * (n + s) < 2 ^ (2 ^ n)) :
    ∃ f : BoolFn n, ¬ HasCircuitSize f s :=
  exists_hard_boolFn_of_circuit_card_lt (lt_of_le_of_lt (card_circuit_le n s) hbound)

/-- Concrete sanity check: on `n = 2` inputs, there is a Boolean function not computable
by any 0-gate (projection-only) circuit. -/
theorem exists_hard_boolFn_two_zero : ∃ f : BoolFn 2, ¬ HasCircuitSize f 0 :=
  exists_hard_boolFn_of_bound_lt (by decide)

/-! ## 3. Razborov–Rudich Natural Proofs Barrier -/

/-- A combinatorial property of `n`-variable Boolean functions. -/
abbrev Property (n : ℕ) : Type := BoolFn n → Prop

/-- **Usefulness**: property `P` is useful against size-`s` circuits if every function
satisfying `P` lacks a size-`s` circuit. -/
def IsUseful {n : ℕ} (P : Property n) (s : ℕ) : Prop :=
  ∀ f : BoolFn n, P f → ¬ HasCircuitSize f s

/-- **Largeness**: property `P` is `1 / den`-large if at least a `1 / den` fraction of all
`2 ^ (2 ^ n)` Boolean functions satisfy `P`. -/
def IsLarge {n : ℕ} (P : Property n) [DecidablePred P] (den : ℕ) : Prop :=
  2 ^ (2 ^ n) ≤ den * (Finset.univ.filter P).card

/-- A property `P` is **natural** (useful + large) against size-`s` circuits with density
denominator `den`. -/
def IsNaturalAgainst {n : ℕ} (P : Property n) [DecidablePred P] (s den : ℕ) : Prop :=
  IsUseful P s ∧ IsLarge P den

/-- Bundled Razborov–Rudich natural property against size-`s` circuits with largeness
denominator `den`. -/
structure NaturalProperty (n s den : ℕ) where
  pred : Property n
  [decPred : DecidablePred pred]
  useful : IsUseful pred s
  large : IsLarge pred den

attribute [instance] NaturalProperty.decPred

/-- A bundled `NaturalProperty` satisfies `IsNaturalAgainst`. -/
theorem NaturalProperty.isNaturalAgainst {n s den : ℕ} (N : NaturalProperty n s den) :
    IsNaturalAgainst N.pred s den :=
  ⟨N.useful, N.large⟩

/-- A `1 / den`-large property (with `den > 0`) is satisfied by at least one Boolean function. -/
theorem IsLarge.exists_witness {n den : ℕ} {P : Property n} [DecidablePred P]
    (hlarge : IsLarge P den) : ∃ f : BoolFn n, P f := by
  unfold IsLarge at hlarge
  have hpos : 0 < (Finset.univ.filter P).card := by
    by_contra hzero
    have hcard : (Finset.univ.filter P).card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hcard, Nat.mul_zero] at hlarge
    have hpow : 0 < 2 ^ (2 ^ n) := Nat.pow_pos (by decide)
    exact Nat.not_lt_of_ge hlarge hpow
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
  exact ⟨f, (Finset.mem_filter.mp hf).2⟩

/-- Any natural property against size-`s` circuits witnesses the existence of a hard Boolean
function outside `HasCircuitSize · s`. -/
theorem IsNaturalAgainst.exists_hard_boolFn {n s den : ℕ} {P : Property n} [DecidablePred P]
    (hnat : IsNaturalAgainst P s den) : ∃ f : BoolFn n, ¬ HasCircuitSize f s := by
  obtain ⟨f, hf⟩ := hnat.2.exists_witness
  exact ⟨f, hnat.1 f hf⟩

/-- A pseudorandom function family computable by size-`s` Boolean circuits. -/
structure PRFamily (n s : ℕ) where
  Key : Type
  eval : Key → BoolFn n
  small_size : ∀ k : Key, HasCircuitSize (eval k) s

/-- Property `P` **distinguishes** a circuit family `F` from uniform random Boolean functions
with advantage at least `1 / den` when `P` is identically false on `F` while holding on at
least a `1 / den` fraction of all `BoolFn n`. -/
def Distinguishes {n s : ℕ} (P : Property n) [DecidablePred P]
    (F : PRFamily n s) (den : ℕ) : Prop :=
  (∀ k : F.Key, ¬ P (F.eval k)) ∧
  2 ^ (2 ^ n) ≤ den * (Finset.univ.filter P).card

/-- **Razborov–Rudich Natural Proofs Barrier**:
Every property `P` that is useful against size-`s` circuits and `1 / den`-large vanishes
identically on every size-`s` circuit family `F : PRFamily n s`, and therefore distinguishes
`F` from uniform random Boolean functions with advantage at least `1 / den`. -/
theorem natural_property_hits_prg_barrier {n s den : ℕ}
    (P : Property n) [DecidablePred P]
    (hnat : IsNaturalAgainst P s den)
    (F : PRFamily n s) :
    Distinguishes P F den := by
  refine ⟨?_, hnat.2⟩
  intro k hP
  exact hnat.1 (F.eval k) hP (F.small_size k)

/-- Bundled version of `natural_property_hits_prg_barrier` for `NaturalProperty`. -/
theorem NaturalProperty.hits_prg_barrier {n s den : ℕ}
    (N : NaturalProperty n s den) (F : PRFamily n s) :
    Distinguishes N.pred F den :=
  natural_property_hits_prg_barrier N.pred N.isNaturalAgainst F

/-- Contrapositive form of the Razborov–Rudich barrier: if a size-`s` pseudorandom function
family `F` cannot be `1 / den`-distinguished by `P`, then `P` cannot be natural against
size-`s` circuits with largeness denominator `den`. -/
theorem not_natural_of_undistinguished_prg {n s den : ℕ}
    (P : Property n) [DecidablePred P] (F : PRFamily n s)
    (hsec : ¬ Distinguishes P F den) :
    ¬ IsNaturalAgainst P s den :=
  fun hnat => hsec (natural_property_hits_prg_barrier P hnat F)

/-- Density separation induced by a natural property: the set of size-`s` computable Boolean
functions and the set of functions satisfying `P` are disjoint, so `s`-gate circuits cover
at most a `1 - 1 / den` fraction of all Boolean functions. -/
theorem natural_property_circuit_density_bound {n s den : ℕ}
    (P : Property n) [DecidablePred P]
    (hnat : IsNaturalAgainst P s den) :
    den * (Finset.univ.image (Circuit.eval (n := n) (s := s))).card + 2 ^ (2 ^ n) ≤
      den * 2 ^ (2 ^ n) := by
  classical
  let Small : Finset (BoolFn n) := Finset.univ.image (Circuit.eval (n := n) (s := s))
  let Good : Finset (BoolFn n) := Finset.univ.filter P
  have hdisj : Disjoint Small Good := by
    rw [Finset.disjoint_left]
    intro f hfS hfG
    rcases Finset.mem_image.mp hfS with ⟨C, _, rfl⟩
    exact hnat.1 C.eval (Finset.mem_filter.mp hfG).2 ⟨C, rfl⟩
  have hsum : Small.card + Good.card ≤ 2 ^ (2 ^ n) := by
    calc
      Small.card + Good.card = (Small ∪ Good).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Finset.univ.card := Finset.card_le_univ _
      _ = 2 ^ (2 ^ n) := by rw [Finset.card_univ, card_boolFn]
  calc
    den * Small.card + 2 ^ (2 ^ n)
      ≤ den * Small.card + den * Good.card := Nat.add_le_add_left hnat.2 _
    _ = den * (Small.card + Good.card) := (Nat.mul_add den Small.card Good.card).symm
    _ ≤ den * 2 ^ (2 ^ n) := Nat.mul_le_mul_left den hsum

end Mathmatica.ComplexityBarriers
