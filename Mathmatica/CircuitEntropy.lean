/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.DynamicalComplexity
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Card

/-!
# Orbit Entropy and Information-Compression Barriers

This module formalizes a combinatorial information-theoretic bridge between the **branching /
orbit separation** of a discrete-time dynamical system and **bounded-memory coarse-graining /
renormalization lower bounds**:

1. **Bounded-Memory Coarse-Grainer (`CoarseGrainer`)**:
   A compression map `encode : Micro → Macro` from a microscopic state space `Micro` to a
   macroscopic effective state space `Macro`, together with semantic distinguishability
   (`SemanticallyDistinguishable`, `PairwiseDistinguishable`) and lossless semantic preservation
   (`CoarseGrainer.IsFaithful`) with respect to a family of Boolean tests
   `Tests : Set (Micro → Bool)`.

2. **Information-Theoretic Pigeonhole Compression Barrier (`compression_pigeonhole_barrier`)**:
   Any faithful coarse-grainer on a finite macroscopic space `Macro` must satisfy
   `S.card ≤ Fintype.card Macro` for every pairwise semantically distinguishable finite set
   `S : Finset Micro`. As a corollary (`compression_bitwidth_lower_bound` and
   `compression_bitwidth_strict_lower_bound`), any `b`-bit representation (`Macro = Fin b → Bool`)
   requires `d ≤ b` (resp. `d < b`) whenever `2 ^ d ≤ S.card` (resp. `2 ^ d < S.card`).

3. **Positive Combinatorial Entropy Forces Exponential Macro Space
   (`positive_entropy_forces_exponential_macro`)**:
   For a `SolverDynamics M` with Boolean observable `obs : M → Bool`, define the `T`-step orbit
   signature `orbitSig D obs T x : Fin T → Bool`. If `D` exhibits positive combinatorial entropy
   (`HasPositiveCombinatorialEntropy D obs T k`), meaning at least `2 ^ k` initial states produce
   pairwise distinct `T`-step orbit signatures (corresponding to topological entropy
   `h_top ≥ k / T > 0`), then any orbit-faithful coarse-grainer `G : CoarseGrainer M Macro` must
   satisfy the exponential state-space lower bound `2 ^ k ≤ Fintype.card Macro` (and hence
   bitwidth `k ≤ b` for `b`-bit encoders).
-/

namespace Mathmatica.CircuitEntropy

open Mathmatica.DynamicalComplexity

/-! ## 1. Bounded-Memory Coarse-Grainer and Semantic Faithfulness -/

/-- A bounded-memory coarse-grainer (renormalization encoder) mapping a microscopic state space
`Micro` into a macroscopic effective state space `Macro`. -/
structure CoarseGrainer (Micro Macro : Type*) where
  /-- Compression map sending each microscopic state to its macroscopic representative. -/
  encode : Micro → Macro

/-- Two microscopic states `x₁` and `x₂` are **semantically distinguishable** with respect to a
family of Boolean tests `Tests` if some test in `Tests` separates them. -/
def SemanticallyDistinguishable {Micro : Type*} (Tests : Set (Micro → Bool))
    (x₁ x₂ : Micro) : Prop :=
  ∃ t ∈ Tests, t x₁ ≠ t x₂

/-- A finite set `S : Finset Micro` is **pairwise semantically distinguishable** under `Tests`
if every pair of distinct elements in `S` is separated by at least one test in `Tests`. -/
def PairwiseDistinguishable {Micro : Type*} (Tests : Set (Micro → Bool))
    (S : Finset Micro) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → SemanticallyDistinguishable Tests x y

/-- A coarse-grainer `G` is **faithful** (losslessly preserves semantics) with respect to `Tests`
if any two microscopic states mapped to the same macroscopic state agree on all tests in `Tests`. -/
def CoarseGrainer.IsFaithful {Micro Macro : Type*} (G : CoarseGrainer Micro Macro)
    (Tests : Set (Micro → Bool)) : Prop :=
  ∀ x₁ x₂ : Micro, G.encode x₁ = G.encode x₂ → ∀ t ∈ Tests, t x₁ = t x₂

/-- A faithful coarse-grainer is injective on any pairwise semantically distinguishable set `S`. -/
lemma CoarseGrainer.injective_on_distinguishable {Micro Macro : Type*}
    (G : CoarseGrainer Micro Macro) {Tests : Set (Micro → Bool)} {S : Finset Micro}
    (hFaith : G.IsFaithful Tests) (hDist : PairwiseDistinguishable Tests S) :
    Function.Injective (fun x : {y : Micro // y ∈ S} => G.encode x.val) := by
  intro x y hEq
  by_contra hne
  have hValNe : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  rcases hDist x.val x.property y.val y.property hValNe with ⟨t, ht, hSep⟩
  exact hSep (hFaith x.val y.val hEq t ht)

/-! ## 2. Main Theorem 1: Information-Theoretic Pigeonhole Compression Barrier -/

/-- **Main Theorem 1 (Information-Theoretic Pigeonhole Compression Barrier)**:
If `S : Finset Micro` is pairwise semantically distinguishable with respect to `Tests`, then any
faithful coarse-grainer `G : CoarseGrainer Micro Macro` into a finite macroscopic space `Macro`
must satisfy `S.card ≤ Fintype.card Macro`. -/
theorem compression_pigeonhole_barrier {Micro Macro : Type*} [Fintype Macro]
    (G : CoarseGrainer Micro Macro) (Tests : Set (Micro → Bool)) (S : Finset Micro)
    (hFaith : G.IsFaithful Tests) (hDist : PairwiseDistinguishable Tests S) :
    S.card ≤ Fintype.card Macro := by
  have hInj := G.injective_on_distinguishable hFaith hDist
  have hCard := Fintype.card_le_of_injective _ hInj
  simpa [Fintype.card_coe] using hCard

/-- Contrapositive form of the pigeonhole barrier: if `Fintype.card Macro < S.card`, then every
coarse-grainer `G : CoarseGrainer Micro Macro` collides on two distinct states of `S`, and hence
cannot be faithful on `Tests`. -/
theorem compression_collision_of_card_lt {Micro Macro : Type*} [Fintype Macro]
    (G : CoarseGrainer Micro Macro) (Tests : Set (Micro → Bool)) (S : Finset Micro)
    (hDist : PairwiseDistinguishable Tests S) (hLt : Fintype.card Macro < S.card) :
    ¬ G.IsFaithful Tests := by
  intro hFaith
  exact Nat.not_le_of_gt hLt (compression_pigeonhole_barrier G Tests S hFaith hDist)

/-- **Corollary 1a (Bitwidth / Log-Space Lower Bound)**:
If the macroscopic state is encoded in `b` bits (`Macro = Fin b → Bool`) and there exists a
pairwise semantically distinguishable set `S` with `2 ^ d ≤ S.card`, then any faithful
coarse-grainer requires at least `d` bits (`d ≤ b`). -/
theorem compression_bitwidth_lower_bound {Micro : Type*} {b d : ℕ}
    (G : CoarseGrainer Micro (Fin b → Bool)) (Tests : Set (Micro → Bool)) (S : Finset Micro)
    (hFaith : G.IsFaithful Tests) (hDist : PairwiseDistinguishable Tests S)
    (hSize : 2 ^ d ≤ S.card) :
    d ≤ b := by
  have hBar : S.card ≤ Fintype.card (Fin b → Bool) :=
    compression_pigeonhole_barrier G Tests S hFaith hDist
  have hPow : 2 ^ d ≤ 2 ^ b := by
    calc
      2 ^ d ≤ S.card := hSize
      _ ≤ Fintype.card (Fin b → Bool) := hBar
      _ = 2 ^ b := by simp
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hPow

/-- **Corollary 1b (Strict Bitwidth Lower Bound)**:
If `2 ^ d < S.card` for a pairwise semantically distinguishable set `S`, then any faithful
`b`-bit coarse-grainer strictly requires `d < b`. -/
theorem compression_bitwidth_strict_lower_bound {Micro : Type*} {b d : ℕ}
    (G : CoarseGrainer Micro (Fin b → Bool)) (Tests : Set (Micro → Bool)) (S : Finset Micro)
    (hFaith : G.IsFaithful Tests) (hDist : PairwiseDistinguishable Tests S)
    (hSize : 2 ^ d < S.card) :
    d < b := by
  have hBar : S.card ≤ Fintype.card (Fin b → Bool) :=
    compression_pigeonhole_barrier G Tests S hFaith hDist
  have hPow : 2 ^ d < 2 ^ b := by
    calc
      2 ^ d < S.card := hSize
      _ ≤ Fintype.card (Fin b → Bool) := hBar
      _ = 2 ^ b := by simp
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hPow

/-! ## 3. Main Theorem 2: Positive Dynamical Entropy Forces Exponential Macro Space -/

/-- The finite-time **orbit signature** of an initial state `x : M` under solver dynamics `D`
and Boolean observable `obs : M → Bool` over time horizon `T`. -/
def orbitSig {M : Type*} (D : SolverDynamics M) (obs : M → Bool) (T : ℕ) (x : M) :
    Fin T → Bool :=
  fun t => obs (D.orbit x t.val)

/-- The family of `T`-step observational test predicates induced by `(D, obs, T)`. -/
def orbitTests {M : Type*} (D : SolverDynamics M) (obs : M → Bool) (T : ℕ) :
    Set (M → Bool) :=
  {p | ∃ t : Fin T, p = fun x => obs (D.orbit x t.val)}

/-- A coarse-grainer `G : CoarseGrainer M Macro` is **orbit-faithful** for `(D, obs, T)` if
macroscopic equality implies identical `T`-step observation orbit signatures. -/
def CoarseGrainer.IsOrbitFaithful {M Macro : Type*} (G : CoarseGrainer M Macro)
    (D : SolverDynamics M) (obs : M → Bool) (T : ℕ) : Prop :=
  ∀ x₁ x₂ : M, G.encode x₁ = G.encode x₂ → orbitSig D obs T x₁ = orbitSig D obs T x₂

/-- Orbit-faithfulness is equivalent to semantic faithfulness with respect to `orbitTests`. -/
lemma CoarseGrainer.isOrbitFaithful_iff_isFaithful {M Macro : Type*}
    (G : CoarseGrainer M Macro) (D : SolverDynamics M) (obs : M → Bool) (T : ℕ) :
    G.IsOrbitFaithful D obs T ↔ G.IsFaithful (orbitTests D obs T) := by
  constructor
  · intro hOrb x₁ x₂ hEq p hp
    rcases hp with ⟨t, rfl⟩
    exact congrFun (hOrb x₁ x₂ hEq) t
  · intro hFaith x₁ x₂ hEq
    funext t
    exact hFaith x₁ x₂ hEq (fun x => obs (D.orbit x t.val)) ⟨t, rfl⟩

/-- Distinct `T`-step orbit signatures witness semantic distinguishability under `orbitTests`. -/
lemma semanticallyDistinguishable_orbitTests_of_ne {M : Type*} (D : SolverDynamics M)
    (obs : M → Bool) (T : ℕ) {x₁ x₂ : M}
    (hne : orbitSig D obs T x₁ ≠ orbitSig D obs T x₂) :
    SemanticallyDistinguishable (orbitTests D obs T) x₁ x₂ := by
  by_contra hNot
  apply hne
  funext t
  by_contra hDiff
  exact hNot ⟨fun x => obs (D.orbit x t.val), ⟨t, rfl⟩, hDiff⟩

/-- A discrete dynamical system `(D, obs)` exhibits **positive combinatorial entropy** with
exponent `k` at horizon `T` (corresponding to topological entropy `h_top ≥ k / T`) if there
exists a finite set `S` of at least `2 ^ k` initial states whose `T`-step observation orbit
signatures are pairwise distinct. -/
def HasPositiveCombinatorialEntropy {M : Type*} (D : SolverDynamics M)
    (obs : M → Bool) (T k : ℕ) : Prop :=
  ∃ S : Finset M, 2 ^ k ≤ S.card ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → orbitSig D obs T x ≠ orbitSig D obs T y

/-- **Main Theorem 2 (Positive Combinatorial Entropy Forces Exponential Macro Space)**:
If a dynamical system `(D, obs)` has positive combinatorial entropy with exponent `k` over
horizon `T`, then any orbit-faithful coarse-grainer `G : CoarseGrainer M Macro` into a finite
macroscopic space `Macro` must satisfy the exponential lower bound `2 ^ k ≤ Fintype.card Macro`. -/
theorem positive_entropy_forces_exponential_macro {M Macro : Type*} [Fintype Macro]
    (D : SolverDynamics M) (obs : M → Bool) (T k : ℕ)
    (G : CoarseGrainer M Macro)
    (hEnt : HasPositiveCombinatorialEntropy D obs T k)
    (hFaith : G.IsOrbitFaithful D obs T) :
    2 ^ k ≤ Fintype.card Macro := by
  rcases hEnt with ⟨S, hCard, hSep⟩
  have hDist : PairwiseDistinguishable (orbitTests D obs T) S := by
    intro x hx y hy hxy
    exact semanticallyDistinguishable_orbitTests_of_ne D obs T (hSep x hx y hy hxy)
  have hFaithTests : G.IsFaithful (orbitTests D obs T) :=
    (G.isOrbitFaithful_iff_isFaithful D obs T).mp hFaith
  exact le_trans hCard (compression_pigeonhole_barrier G (orbitTests D obs T) S hFaithTests hDist)

/-- **Corollary 2a (Positive Entropy Forces Linear Bitwidth Memory Barrier)**:
Under `HasPositiveCombinatorialEntropy D obs T k`, any orbit-faithful `b`-bit coarse-grainer
`G : CoarseGrainer M (Fin b → Bool)` requires at least `k` bits of macroscopic memory (`k ≤ b`). -/
theorem positive_entropy_bitwidth_lower_bound {M : Type*} {b T k : ℕ}
    (D : SolverDynamics M) (obs : M → Bool)
    (G : CoarseGrainer M (Fin b → Bool))
    (hEnt : HasPositiveCombinatorialEntropy D obs T k)
    (hFaith : G.IsOrbitFaithful D obs T) :
    k ≤ b := by
  have hExp : 2 ^ k ≤ Fintype.card (Fin b → Bool) :=
    positive_entropy_forces_exponential_macro D obs T k G hEnt hFaith
  have hPow : 2 ^ k ≤ 2 ^ b := by
    simpa using hExp
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hPow

/-- **Corollary 2b (Impossibility of Sub-Exponential Lossless Compression)**:
No orbit-faithful coarse-grainer into a finite space `Macro` with `Fintype.card Macro < 2 ^ k`
can exist when `HasPositiveCombinatorialEntropy D obs T k` holds. -/
theorem positive_entropy_no_small_compressor {M Macro : Type*} [Fintype Macro]
    (D : SolverDynamics M) (obs : M → Bool) (T k : ℕ)
    (hEnt : HasPositiveCombinatorialEntropy D obs T k)
    (hSmall : Fintype.card Macro < 2 ^ k) :
    ∀ G : CoarseGrainer M Macro, ¬ G.IsOrbitFaithful D obs T := by
  intro G hFaith
  exact Nat.not_le_of_gt hSmall
    (positive_entropy_forces_exponential_macro D obs T k G hEnt hFaith)

end Mathmatica.CircuitEntropy
