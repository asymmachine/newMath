/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Residual Quotient Entropy and Ordered Branching Program Lower Bounds

This module formalizes the semantic residual-subproblem quotient dynamical system along a fixed
variable order `π : Equiv.Perm (Fin n)`, its log-free entropy predicate, and non-circular width
and memory-bitwidth lower bounds for deterministic layered ordered branching programs.

> **Scope disclaimer**: All lower bounds in this module are **strictly restricted to fixed-order
> deterministic models** (layered read-once ordered branching programs, OBDDs, and fixed-order
> deterministic decision models with semantic caching). They do **not** apply to general algorithms,
> variable-reordering or basis-switching procedures, randomized or nondeterministic models, general
> DPLL/CDCL solvers, or `P ≠ NP`.

## Main definitions

* `BoolFn n`: Boolean functions `(Fin n → Bool) → Bool`.
* `glue π t ht ρ τ`: Lossless concatenation of a length-`t` prefix assignment `ρ` and a
  length-`(n - t)` suffix assignment `τ` along variable order `π`.
* `residualFn`, `residualEquivalent`, `residualSetoid`, `ResidualQuotient`: The Myhill–Nerode
  residual subfunction equivalence relation and quotient space `Q_{F,π}(t)`.
* `snoc`, `quotientStep`: Prefix extension and the induced deterministic quotient transition
  operator `Q_{F,π}(t) → Bool → Q_{F,π}(t + 1)`.
* `residualClassCount`, `EntropyBitsAtLeast`, `peakResidualClasses`: Exact count of semantically
  distinct residual subproblems, log-free bit-entropy lower bound, and peak count across layers.
* `OrderedProgram n`, `OrderedProgram.runPrefix`, `OrderedProgram.runFrom`,
  `CorrectOrderedProgram`: Deterministic layered ordered branching programs and their semantics.
* `parityFn`, `innerProductFn`, `eqFn`, `interleavePerm`: Three concrete Boolean function families
  for sanity-checking, exponential width separation, and order-sensitivity separation.

## Main results

* `residualEquivalent_snoc`: Congruence of semantic residual equivalence under one-bit prefix
  extension, making `quotientStep` well-defined.
* `ordered_program_layer_injective_on_residual_classes` and `layerQuotientMap_injective`:
  Bridge Theorem 1 (injectivity of layer states on the residual quotient).
* `ordered_program_width_ge_residual_classes` and `ordered_program_size_ge_peak`:
  Bridge Theorem 2 (layer width and total size lower bounds).
* `ordered_program_bitwidth_ge_of_entropy`: Bridge Theorem 3 (memory bitwidth lower bound).
* `parity_residualClassCount_le_two`: Sanity baseline — `parityFn n` has at most `2` residual
  classes under any variable order `π` and any depth `t ≤ n`.
* `innerProduct_residualClassCount_eq`, `innerProduct_ordered_program_width_ge`, and
  `innerProduct_ordered_program_bitwidth_ge`: Explicit distinguishing-suffix witness showing
  `N_{IP_m, id}(m) = 2 ^ m`, forcing layer-`m` width `≥ 2 ^ m` and memory `≥ m` bits.
* `eq_split_residualClassCount_eq` and `eq_interleaved_residualClassCount_le`: Order-sensitivity
  separation on `eqFn m` (`2 ^ m` under split order vs. `≤ 3` at every layer under interleaved
  order).
-/

namespace Mathmatica.ResidualEntropy

/-! ### 1. Residual Quotient Dynamics and Log-Free Entropy -/

/-- A Boolean function on `n` variables. -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

/-- Glue a prefix assignment `ρ` (the first `t` variables under `π`) and a suffix assignment `τ`
(the remaining `n - t` variables under `π`) into a full assignment on `Fin n`. -/
def glue {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) (τ : Fin (n - t) → Bool) : Fin n → Bool :=
  fun i =>
    let k := (π.symm i).val
    if h : k < t then ρ ⟨k, h⟩ else τ ⟨k - t, by have := (π.symm i).isLt; omega⟩

/-- Evaluating `glue π t ht ρ τ` at the `i`-th variable in order `π` reads from `ρ` when
`i.val < t` and from `τ` otherwise. -/
@[simp]
theorem glue_apply_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) (τ : Fin (n - t) → Bool) (i : Fin n) :
    glue π t ht ρ τ (π i) =
      if h : i.val < t then ρ ⟨i.val, h⟩ else τ ⟨i.val - t, by omega⟩ := by
  simp [glue]

/-- Residual Boolean function obtained by fixing the first `t` variables under `π` to `ρ`. -/
def residualFn {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) : (Fin (n - t) → Bool) → Bool :=
  fun τ => F (glue π t ht ρ τ)

/-- Semantic residual equivalence (Myhill–Nerode equivalence at layer `t`). -/
def residualEquivalent {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ₁ ρ₂ : Fin t → Bool) : Prop :=
  ∀ τ : Fin (n - t) → Bool, residualFn F π t ht ρ₁ τ = residualFn F π t ht ρ₂ τ

theorem residualEquivalent_iff_residualFn_eq {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) {ρ₁ ρ₂ : Fin t → Bool} :
    residualEquivalent F π t ht ρ₁ ρ₂ ↔
      residualFn F π t ht ρ₁ = residualFn F π t ht ρ₂ :=
  ⟨fun h => funext h, fun h τ => congrFun h τ⟩

/-- Setoid of semantic residual equivalence on length-`t` prefixes. -/
def residualSetoid {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n) :
    Setoid (Fin t → Bool) where
  r := residualEquivalent F π t ht
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h τ => (h τ).symm
      trans := fun h₁ h₂ τ => (h₁ τ).trans (h₂ τ) }

/-- Quotient space `Q_{F,π}(t)` of semantically distinct residual subproblems at depth `t`. -/
def ResidualQuotient {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n) :
    Type :=
  Quotient (residualSetoid F π t ht)

/-- Exact count `N_{F,π}(t)` of semantically distinct residual subproblems at depth `t`. -/
noncomputable def residualClassCount {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) : ℕ :=
  open Classical in (Finset.univ.image (residualFn F π t ht)).card

/-- Log-free entropy lower bound: `2 ^ b ≤ N_{F,π}(t)`. -/
def EntropyBitsAtLeast {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) (b : ℕ) : Prop :=
  2 ^ b ≤ residualClassCount F π t ht

/-- Peak residual class count across all layers `0 ≤ t ≤ n`. -/
noncomputable def peakResidualClasses {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ : Finset (Fin (n + 1))).sup
    (fun t => residualClassCount F π t.val (Nat.le_of_lt_succ t.isLt))

/-- Append a single Boolean value `b` to the end of a length-`t` prefix `ρ`. -/
def snoc {t : ℕ} (ρ : Fin t → Bool) (b : Bool) : Fin (t + 1) → Bool :=
  fun i => if h : i.val < t then ρ ⟨i.val, h⟩ else b

/-- Prepend a single Boolean value `b` to the front of a length-`(n - (t + 1))` suffix `τ`. -/
def consSuffix {n t : ℕ} (ht : t + 1 ≤ n) (b : Bool)
    (τ : Fin (n - (t + 1)) → Bool) : Fin (n - t) → Bool :=
  fun j => if h : j.val = 0 then b else τ ⟨j.val - 1, by omega⟩

/-- Gluing `(snoc ρ b)` with `τ` agrees with gluing `ρ` with `(consSuffix ht b τ)`. -/
theorem glue_snoc {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t + 1 ≤ n)
    (ρ : Fin t → Bool) (b : Bool) (τ : Fin (n - (t + 1)) → Bool) :
    glue π (t + 1) ht (snoc ρ b) τ =
      glue π t (Nat.le_of_succ_le ht) ρ (consSuffix ht b τ) := by
  funext i
  simp only [glue, snoc, consSuffix]
  by_cases hlt : (π.symm i).val < t
  · have hlt' : (π.symm i).val < t + 1 := Nat.lt_succ_of_lt hlt
    simp [hlt, hlt']
  · by_cases heq : (π.symm i).val = t
    · have hlt' : (π.symm i).val < t + 1 := by omega
      have hsub : (π.symm i).val - t = 0 := by omega
      simp [hlt, hlt', hsub]
    · have hlt' : ¬ ((π.symm i).val < t + 1) := by omega
      have hsub : (π.symm i).val - t ≠ 0 := by omega
      simp only [hlt, hlt', hsub, ↓reduceDIte]
      congr 1

/-- Congruence of semantic residual equivalence under appending one bit `b`. -/
theorem residualEquivalent_snoc {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t + 1 ≤ n) {ρ₁ ρ₂ : Fin t → Bool} (b : Bool)
    (hEq : residualEquivalent F π t (Nat.le_of_succ_le ht) ρ₁ ρ₂) :
    residualEquivalent F π (t + 1) ht (snoc ρ₁ b) (snoc ρ₂ b) := by
  intro τ
  simp only [residualFn, glue_snoc]
  exact hEq (consSuffix ht b τ)

/-- Induced deterministic transition operator on the residual quotient space `Q_{F,π}(t)`. -/
def quotientStep {n : ℕ} (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t + 1 ≤ n) :
    ResidualQuotient F π t (Nat.le_of_succ_le ht) → Bool → ResidualQuotient F π (t + 1) ht :=
  fun q b =>
    Quotient.liftOn q
      (fun ρ => Quotient.mk (residualSetoid F π (t + 1) ht) (snoc ρ b))
      (fun _ _ h => Quotient.sound (residualEquivalent_snoc F π t ht b h))

/-- General cardinality bound: if `residualFn` factors through a map `g : (Fin t → Bool) → α`,
then `residualClassCount F π t ht ≤ Fintype.card α`. -/
theorem residualClassCount_le_card_of_factor {n : ℕ} {α : Type*} [Fintype α]
    (F : BoolFn n) (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (g : (Fin t → Bool) → α)
    (hFactor : ∀ ρ₁ ρ₂, g ρ₁ = g ρ₂ → residualEquivalent F π t ht ρ₁ ρ₂) :
    residualClassCount F π t ht ≤ Fintype.card α := by
  classical
  unfold residualClassCount
  let h : α → (Fin (n - t) → Bool) → Bool := fun a =>
    if hex : ∃ ρ : Fin t → Bool, g ρ = a then
      residualFn F π t ht (Classical.choose hex)
    else
      fun _ => false
  have hSub :
      Finset.univ.image (residualFn F π t ht) ⊆ (Finset.univ : Finset α).image h := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨ρ, _, rfl⟩
    refine Finset.mem_image.mpr ⟨g ρ, Finset.mem_univ _, ?_⟩
    have hex : ∃ ρ' : Fin t → Bool, g ρ' = g ρ := ⟨ρ, rfl⟩
    simp only [h, hex, ↓reduceDIte]
    exact (residualEquivalent_iff_residualFn_eq F π t ht).mp
      (hFactor _ _ (Classical.choose_spec hex))
  calc
    (Finset.univ.image (residualFn F π t ht)).card
        ≤ ((Finset.univ : Finset α).image h).card := Finset.card_le_card hSub
    _ ≤ (Finset.univ : Finset α).card := Finset.card_image_le
    _ = Fintype.card α := Finset.card_univ

/-! ### 2. Deterministic Layered Ordered Branching Programs and Bridge Theorems -/

/-- A deterministic layered ordered branching program (OBP / fixed-order cached decision model)
on `n` Boolean variables. -/
structure OrderedProgram (n : ℕ) where
  /-- State space at each layer `0 ≤ t ≤ n`. -/
  State : Fin (n + 1) → Type
  /-- Finiteness of each layer's state space. -/
  [fintypeState : ∀ t, Fintype (State t)]
  /-- Initial state at layer `0`. -/
  init : State ⟨0, Nat.zero_lt_succ n⟩
  /-- Deterministic transition from layer `t` to layer `t + 1` on reading a Boolean bit. -/
  trans : ∀ (t : Fin n), State ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ → Bool →
    State ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩
  /-- Output readout at the final layer `n`. -/
  output : State ⟨n, Nat.lt_succ_self n⟩ → Bool

attribute [instance] OrderedProgram.fintypeState

/-- Run `P` through the first `t` layers on prefix `ρ`. -/
def OrderedProgram.runPrefix {n : ℕ} (P : OrderedProgram n) :
    ∀ (t : ℕ) (ht : t ≤ n), (Fin t → Bool) → P.State ⟨t, Nat.lt_succ_of_le ht⟩
  | 0, _, _ => P.init
  | t + 1, ht, ρ =>
      P.trans ⟨t, ht⟩
        (P.runPrefix t (Nat.le_of_succ_le ht) (fun i => ρ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (ρ ⟨t, Nat.lt_succ_self t⟩)

/-- Run `P` for `k` steps starting from state `s` at layer `t` using bits `τ`. -/
def OrderedProgram.runSteps {n : ℕ} (P : OrderedProgram n) :
    ∀ (t k : ℕ) (htk : t + k ≤ n),
    P.State ⟨t, by omega⟩ → (Fin k → Bool) → P.State ⟨t + k, by omega⟩
  | _, 0, _, s, _ => s
  | t, k + 1, htk, s, τ =>
      P.trans ⟨t + k, by omega⟩
        (P.runSteps t k (by omega) s (fun i => τ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (τ ⟨k, Nat.lt_succ_self k⟩)

/-- Run `P` from a layer-`t` state `s` through the remaining `n - t` layers on suffix `τ`. -/
def OrderedProgram.runFrom {n : ℕ} (P : OrderedProgram n) (t : ℕ) (ht : t ≤ n)
    (s : P.State ⟨t, Nat.lt_succ_of_le ht⟩) (τ : Fin (n - t) → Bool) :
    P.State ⟨n, Nat.lt_succ_self n⟩ :=
  cast (congrArg P.State (Fin.ext (Nat.add_sub_of_le ht)))
    (P.runSteps t (n - t) (by omega) s τ)

theorem OrderedProgram.runPrefix_add {n : ℕ} (P : OrderedProgram n)
    (t k : ℕ) (htk : t + k ≤ n) (ρ : Fin (t + k) → Bool) :
    P.runPrefix (t + k) htk ρ =
      P.runSteps t k htk
        (P.runPrefix t (by omega) (fun i => ρ ⟨i.val, by omega⟩))
        (fun j => ρ ⟨t + j.val, by omega⟩) := by
  induction k with
  | zero =>
      simp only [runSteps]
      congr 1
  | succ k ih =>
      simp only [runPrefix, runSteps]
      congr 1
      exact ih (by omega) (fun i => ρ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

theorem OrderedProgram.runPrefix_cast {n m : ℕ} (P : OrderedProgram n)
    (hm : m ≤ n) (heq : m = n) (ρ : Fin m → Bool) :
    cast (congrArg P.State (Fin.ext heq)) (P.runPrefix m hm ρ) =
      P.runPrefix n le_rfl (fun i => ρ ⟨i.val, by omega⟩) := by
  subst heq
  rfl

/-- Composition decomposition: running `P` on the full glued input `(ρ, τ)` equals running
`P` on the prefix `ρ` to layer `t` and then continuing with `runFrom` on `τ`. -/
theorem OrderedProgram.runPrefix_full_eq_runFrom {n : ℕ} (P : OrderedProgram n)
    (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) (τ : Fin (n - t) → Bool) :
    P.runPrefix n le_rfl (fun i => glue π t ht ρ τ (π i)) =
      P.runFrom t ht (P.runPrefix t ht ρ) τ := by
  have hsum : t + (n - t) = n := Nat.add_sub_of_le ht
  let f : Fin (t + (n - t)) → Bool :=
    fun i => glue π t ht ρ τ (π ⟨i.val, by omega⟩)
  have hcast :
      cast (congrArg P.State (Fin.ext hsum)) (P.runPrefix (t + (n - t)) (by omega) f) =
        P.runPrefix n le_rfl (fun i => glue π t ht ρ τ (π i)) := by
    simpa [f] using P.runPrefix_cast (m := t + (n - t)) (by omega) hsum f
  rw [← hcast]
  unfold OrderedProgram.runFrom
  congr 1
  rw [P.runPrefix_add t (n - t) (by omega) f]
  have hρ : (fun i : Fin t => f ⟨i.val, by omega⟩) = ρ := by
    funext i
    simp [f, i.isLt]
  have hτ : (fun j : Fin (n - t) => f ⟨t + j.val, by omega⟩) = τ := by
    funext j
    have hnot : ¬ (t + j.val < t) := by omega
    simp only [f, glue_apply_perm, hnot, ↓reduceDIte]
    congr 1
    ext
    dsimp
    omega
  rw [hρ, hτ]

/-- Correctness of `P` for computing `F` under variable order `π`. -/
def CorrectOrderedProgram {n : ℕ} (P : OrderedProgram n) (F : BoolFn n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, P.output (P.runPrefix n le_rfl (fun i => x (π i))) = F x

/-- **Bridge Theorem 1 (Injectivity on Residual Classes)**:
If `P` correctly computes `F` under `π`, then any two prefixes reaching the same layer-`t`
state must be semantically residual-equivalent. -/
theorem ordered_program_layer_injective_on_residual_classes {n : ℕ}
    (P : OrderedProgram n) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectOrderedProgram P F π) (t : ℕ) (ht : t ≤ n)
    {ρ₁ ρ₂ : Fin t → Bool}
    (hEq : P.runPrefix t ht ρ₁ = P.runPrefix t ht ρ₂) :
    residualEquivalent F π t ht ρ₁ ρ₂ := by
  intro τ
  unfold residualFn
  rw [← hCorr (glue π t ht ρ₁ τ), ← hCorr (glue π t ht ρ₂ τ)]
  rw [P.runPrefix_full_eq_runFrom π t ht ρ₁ τ, P.runPrefix_full_eq_runFrom π t ht ρ₂ τ]
  rw [hEq]

/-- Representative map from the residual quotient space `Q_{F,π}(t)` into layer `t` of `P`. -/
noncomputable def layerQuotientMap {n : ℕ} (P : OrderedProgram n) (F : BoolFn n)
    (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n) :
    ResidualQuotient F π t ht → P.State ⟨t, Nat.lt_succ_of_le ht⟩ :=
  fun q => P.runPrefix t ht (Quotient.out q)

/-- The induced map `layerQuotientMap` from `ResidualQuotient F π t ht` into `P.State t` is
injective whenever `P` correctly computes `F` under `π`. -/
theorem layerQuotientMap_injective {n : ℕ} (P : OrderedProgram n) (F : BoolFn n)
    (π : Equiv.Perm (Fin n)) (hCorr : CorrectOrderedProgram P F π) (t : ℕ) (ht : t ≤ n) :
    Function.Injective (layerQuotientMap P F π t ht) := by
  intro q₁ q₂ hEq
  have hEquiv : residualEquivalent F π t ht (Quotient.out q₁) (Quotient.out q₂) :=
    ordered_program_layer_injective_on_residual_classes P F π hCorr t ht hEq
  rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
  exact Quotient.sound hEquiv

/-- **Bridge Theorem 2 (Layer Width Lower Bound)**:
Any correct deterministic layered ordered program respecting `π` has layer-`t` width at least
`residualClassCount F π t ht`. -/
theorem ordered_program_width_ge_residual_classes {n : ℕ}
    (P : OrderedProgram n) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectOrderedProgram P F π) (t : ℕ) (ht : t ≤ n) :
    residualClassCount F π t ht ≤ Fintype.card (P.State ⟨t, Nat.lt_succ_of_le ht⟩) :=
  residualClassCount_le_card_of_factor F π t ht (P.runPrefix t ht) (fun _ _ hEq =>
    ordered_program_layer_injective_on_residual_classes P F π hCorr t ht hEq)

/-- Total-size corollary of Bridge Theorem 2: the sum of layer widths of any correct ordered
program is at least `peakResidualClasses F π`. -/
theorem ordered_program_size_ge_peak {n : ℕ}
    (P : OrderedProgram n) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectOrderedProgram P F π) :
    peakResidualClasses F π ≤ ∑ t : Fin (n + 1), Fintype.card (P.State t) := by
  unfold peakResidualClasses
  refine Finset.sup_le (fun t _ => ?_)
  have hLayer :
      residualClassCount F π t.val (Nat.le_of_lt_succ t.isLt) ≤ Fintype.card (P.State t) :=
    ordered_program_width_ge_residual_classes P F π hCorr t.val (Nat.le_of_lt_succ t.isLt)
  exact le_trans hLayer
    (Finset.single_le_sum (f := fun s : Fin (n + 1) => Fintype.card (P.State s))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))

/-- **Bridge Theorem 3 (Memory Bitwidth Lower Bound)**:
If `EntropyBitsAtLeast F π t ht b` holds and layer `t` has at most `2 ^ k` states,
then `b ≤ k`. -/
theorem ordered_program_bitwidth_ge_of_entropy {n b k : ℕ}
    (P : OrderedProgram n) (F : BoolFn n) (π : Equiv.Perm (Fin n))
    (hCorr : CorrectOrderedProgram P F π) (t : ℕ) (ht : t ≤ n)
    (hEnt : EntropyBitsAtLeast F π t ht b)
    (hCard : Fintype.card (P.State ⟨t, Nat.lt_succ_of_le ht⟩) ≤ 2 ^ k) :
    b ≤ k := by
  have hPow : 2 ^ b ≤ 2 ^ k :=
    le_trans hEnt (le_trans (ordered_program_width_ge_residual_classes P F π hCorr t ht) hCard)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hPow

/-! ### 3. Concrete Natural Instances with Explicit Distinguishing Suffixes -/

/-! #### 3.1 Sanity Check: Parity (`parityFn`) -/

local instance : Std.Commutative xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative xor := ⟨Bool.xor_assoc⟩

/-- Parity function on `n` Boolean variables: XOR of all coordinates. -/
def parityFn (n : ℕ) : BoolFn n :=
  fun x => Finset.univ.fold xor false x

private theorem fold_xor_false_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.fold xor false (fun _ => false) = false := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.fold_insert ha, ih]
      rfl

private theorem fold_xor_disjUnion {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α)
    (hdisj : Disjoint s₁ s₂) (f : α → Bool) :
    (s₁ ∪ s₂).fold xor false f = xor (s₁.fold xor false f) (s₂.fold xor false f) := by
  induction s₁ using Finset.induction with
  | empty => simp
  | @insert a s₁ ha ih =>
      have hdisj' : Disjoint s₁ s₂ := Disjoint.mono_left (Finset.subset_insert a s₁) hdisj
      have ha₂ : a ∉ s₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a s₁)
      have ha₁₂ : a ∉ s₁ ∪ s₂ := by simp [ha, ha₂]
      rw [Finset.insert_union, Finset.fold_insert ha₁₂, Finset.fold_insert ha, ih hdisj']
      cases f a <;> cases s₁.fold xor false f <;> cases s₂.fold xor false f <;> rfl

private theorem parity_glue_split {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t ≤ n)
    (ρ : Fin t → Bool) (τ : Fin (n - t) → Bool) :
    parityFn n (glue π t ht ρ τ) =
      xor (Finset.univ.fold xor false ρ) (Finset.univ.fold xor false τ) := by
  unfold parityFn
  have hmap : (Finset.univ : Finset (Fin n)).map π.toEmbedding = Finset.univ := by
    ext i
    simp
  have hperm :
      Finset.univ.fold xor false (glue π t ht ρ τ) =
        Finset.univ.fold xor false (fun i : Fin n => glue π t ht ρ τ (π i)) := by
    calc
      Finset.univ.fold xor false (glue π t ht ρ τ)
          = ((Finset.univ : Finset (Fin n)).map π.toEmbedding).fold xor false
              (glue π t ht ρ τ) := by
            rw [hmap]
      _ = Finset.univ.fold xor false (fun i : Fin n => glue π t ht ρ τ (π i)) := by
            rw [Finset.fold_map]
            rfl
  rw [hperm]
  let s₁ : Finset (Fin n) := Finset.univ.filter (fun i => i.val < t)
  let s₂ : Finset (Fin n) := Finset.univ.filter (fun i => ¬ (i.val < t))
  have hunion : s₁ ∪ s₂ = Finset.univ := by
    ext i
    simp only [s₁, s₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (em (i.val < t))
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_filter]
    intro i _ h₁ h₂
    exact h₂ h₁
  rw [← hunion, fold_xor_disjUnion s₁ s₂ hdisj]
  have hs₁ : s₁.fold xor false (fun i => glue π t ht ρ τ (π i)) =
      Finset.univ.fold xor false ρ := by
    let emb : Fin t ↪ Fin n :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt ht⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
    have hs₁_eq : s₁ = (Finset.univ : Finset (Fin t)).map emb := by
      ext i
      simp only [s₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb]
      constructor
      · intro hi
        exact ⟨⟨i.val, hi⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.isLt
    rw [hs₁_eq, Finset.fold_map]
    refine Finset.fold_congr (fun j _ => ?_)
    change glue π t ht ρ τ (π ⟨j.val, lt_of_lt_of_le j.isLt ht⟩) = ρ j
    simp [j.isLt]
  have hs₂ : s₂.fold xor false (fun i => glue π t ht ρ τ (π i)) =
      Finset.univ.fold xor false τ := by
    let emb : Fin (n - t) ↪ Fin n :=
      ⟨fun j => ⟨t + j.val, by omega⟩, fun _ _ h =>
        Fin.ext (by have hval := Fin.mk.inj h; omega)⟩
    have hs₂_eq : s₂ = (Finset.univ : Finset (Fin (n - t))).map emb := by
      ext i
      simp only [s₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb]
      constructor
      · intro hi
        refine ⟨⟨i.val - t, by omega⟩, ?_⟩
        ext
        exact Nat.add_sub_of_le (Nat.le_of_not_lt hi)
      · rintro ⟨j, rfl⟩
        exact Nat.not_lt.mpr (Nat.le_add_right t j.val)
    rw [hs₂_eq, Finset.fold_map]
    refine Finset.fold_congr (fun j _ => ?_)
    change glue π t ht ρ τ (π ⟨t + j.val, by omega⟩) = τ j
    have hnot : ¬ (t + j.val < t) := by omega
    simp only [glue_apply_perm, hnot, ↓reduceDIte]
    congr 1
    ext
    dsimp
    omega
  rw [hs₁, hs₂]

/-- **Sanity Check (Parity)**: Under *any* variable order `π` and *any* depth `t ≤ n`,
`parityFn n` has at most `2` semantically distinct residual classes. -/
theorem parity_residualClassCount_le_two (n : ℕ) (π : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ n) :
    residualClassCount (parityFn n) π t ht ≤ 2 := by
  have hle :=
    residualClassCount_le_card_of_factor (parityFn n) π t ht
      (fun ρ => Finset.univ.fold xor false ρ) (fun ρ₁ ρ₂ hEq τ => by
        simp only [residualFn, parity_glue_split, hEq])
  exact le_trans hle (by decide)

/-! #### 3.2 Exponential Witness: Inner Product mod 2 (`innerProductFn`) -/

/-- Inner product modulo `2` on `2 * m` variables: `⊕_{i < m} (x_i ∧ y_i)`. -/
def innerProductFn (m : ℕ) : BoolFn (2 * m) :=
  fun x => Finset.univ.fold xor false
    (fun i : Fin m => x ⟨i.val, by omega⟩ && x ⟨m + i.val, by omega⟩)

/-- Indicator suffix with a single `true` at coordinate `i`. -/
def indicator (m : ℕ) (i : Fin m) : Fin (2 * m - m) → Bool :=
  fun j => decide (j.val = i.val)

private theorem innerProduct_residual_indicator (m : ℕ) (ρ : Fin m → Bool) (i : Fin m) :
    residualFn (innerProductFn m) (Equiv.refl (Fin (2 * m))) m (by omega) ρ (indicator m i) =
      ρ i := by
  unfold residualFn innerProductFn
  have hterm :
      (fun k : Fin m =>
        glue (Equiv.refl (Fin (2 * m))) m (by omega) ρ (indicator m i) ⟨k.val, by omega⟩ &&
        glue (Equiv.refl (Fin (2 * m))) m (by omega) ρ (indicator m i) ⟨m + k.val, by omega⟩) =
      (fun k : Fin m => ρ k && decide (k.val = i.val)) := by
    funext k
    have hnot : ¬ (m + k.val < m) := by omega
    have hsub : m + k.val - m = k.val := by omega
    simp [glue, k.isLt, hnot, indicator, hsub]
  rw [hterm]
  have hmem : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
  rw [← Finset.insert_erase hmem, Finset.fold_insert (Finset.notMem_erase i Finset.univ)]
  have herase :
      (Finset.univ.erase i).fold xor false (fun k : Fin m => ρ k && decide (k.val = i.val)) =
        false := by
    have hzero :
        (Finset.univ.erase i).fold xor false (fun k : Fin m => ρ k && decide (k.val = i.val)) =
          (Finset.univ.erase i).fold xor false (fun _ => false) := by
      refine Finset.fold_congr (fun k hk => ?_)
      have hne : k.val ≠ i.val := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
      simp [hne]
    rw [hzero, fold_xor_false_eq]
  rw [herase]
  simp

/-- **Explicit Exponential Witness (`innerProductFn`)**: Under the split variable order
`Equiv.refl (Fin (2 * m))`, `innerProductFn m` has exactly `2 ^ m` residual classes at layer `m`. -/
theorem innerProduct_residualClassCount_eq (m : ℕ) :
    residualClassCount (innerProductFn m) (Equiv.refl (Fin (2 * m))) m (by omega) = 2 ^ m := by
  classical
  unfold residualClassCount
  have hinj :
      Function.Injective (residualFn (innerProductFn m) (Equiv.refl (Fin (2 * m))) m (by omega)) :=
    fun ρ₁ ρ₂ hEq => by
      funext i
      have h := congrFun hEq (indicator m i)
      simpa [innerProduct_residual_indicator] using h
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp

/-- Layer-`m` width lower bound for `innerProductFn m` under the split variable order. -/
theorem innerProduct_ordered_program_width_ge (m : ℕ)
    (P : OrderedProgram (2 * m))
    (hCorr : CorrectOrderedProgram P (innerProductFn m) (Equiv.refl (Fin (2 * m)))) :
    2 ^ m ≤ Fintype.card (P.State ⟨m, by omega⟩) := by
  have h :=
    ordered_program_width_ge_residual_classes P (innerProductFn m)
      (Equiv.refl (Fin (2 * m))) hCorr m (by omega)
  rwa [innerProduct_residualClassCount_eq m] at h

/-- Layer-`m` memory bitwidth lower bound for `innerProductFn m` under the split variable order. -/
theorem innerProduct_ordered_program_bitwidth_ge (m k : ℕ)
    (P : OrderedProgram (2 * m))
    (hCorr : CorrectOrderedProgram P (innerProductFn m) (Equiv.refl (Fin (2 * m))))
    (hCard : Fintype.card (P.State ⟨m, by omega⟩) ≤ 2 ^ k) :
    m ≤ k := by
  have hEnt :
      EntropyBitsAtLeast (innerProductFn m) (Equiv.refl (Fin (2 * m))) m (by omega) m := by
    unfold EntropyBitsAtLeast
    rw [innerProduct_residualClassCount_eq m]
  exact ordered_program_bitwidth_ge_of_entropy P (innerProductFn m)
    (Equiv.refl (Fin (2 * m))) hCorr m (by omega) hEnt hCard

/-! #### 3.3 Order-Sensitive Contrast Instance: Equality (`eqFn`) -/

/-- Equality function on `2 * m` variables: `true` iff `x_i = y_i` for all `i < m`. -/
def eqFn (m : ℕ) : BoolFn (2 * m) :=
  fun x => decide (∀ i : Fin m, x ⟨i.val, by omega⟩ = x ⟨m + i.val, by omega⟩)

/-- **Explicit Split-Order Witness (`eqFn`)**: Under split order `Equiv.refl (Fin (2 * m))`,
`eqFn m` has exactly `2 ^ m` residual classes at layer `m`. -/
theorem eq_split_residualClassCount_eq (m : ℕ) :
    residualClassCount (eqFn m) (Equiv.refl (Fin (2 * m))) m (by omega) = 2 ^ m := by
  classical
  unfold residualClassCount
  have hinj :
      Function.Injective (residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) m (by omega)) :=
    fun ρ₁ ρ₂ hEq => by
      let τ : Fin (2 * m - m) → Bool := fun j => ρ₁ ⟨j.val, by omega⟩
      have h₁ :
          residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) m (by omega) ρ₁ τ = true := by
        unfold residualFn eqFn
        rw [decide_eq_true_iff]
        intro i
        have hnot : ¬ (m + i.val < m) := by omega
        have hsub : m + i.val - m = i.val := by omega
        simp [glue, i.isLt, hnot, τ, hsub]
      have h₂ :
          residualFn (eqFn m) (Equiv.refl (Fin (2 * m))) m (by omega) ρ₂ τ = true := by
        rw [← congrFun hEq τ, h₁]
      unfold residualFn eqFn at h₂
      rw [decide_eq_true_iff] at h₂
      funext i
      have hi := h₂ i
      have hnot : ¬ (m + i.val < m) := by omega
      have hsub : m + i.val - m = i.val := by omega
      simp only [glue, Equiv.refl_symm, Equiv.refl_apply, i.isLt, hnot,
        ↓reduceDIte, τ, hsub] at hi
      exact hi.symm
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp

/-- Interleaved variable order on `2 * m` variables: step `2 * j` reads `x_j` (index `j`) and
step `2 * j + 1` reads `y_j` (index `m + j`). -/
def interleavePerm (m : ℕ) : Equiv.Perm (Fin (2 * m)) where
  toFun k :=
    if h : k.val % 2 = 0 then ⟨k.val / 2, by omega⟩
    else ⟨m + k.val / 2, by omega⟩
  invFun i :=
    if h : i.val < m then ⟨2 * i.val, by omega⟩
    else ⟨2 * (i.val - m) + 1, by omega⟩
  left_inv k := by
    ext
    by_cases h : k.val % 2 = 0
    · simp only [h, ↓reduceDIte]
      have hlt : k.val / 2 < m := by omega
      simp only [hlt, ↓reduceDIte]
      omega
    · simp only [h, ↓reduceDIte]
      have hnot : ¬ (m + k.val / 2 < m) := by omega
      simp only [hnot, ↓reduceDIte]
      omega
  right_inv i := by
    ext
    by_cases h : i.val < m
    · simp only [h, ↓reduceDIte]
      have hmod : 2 * i.val % 2 = 0 := by omega
      simp only [hmod, ↓reduceDIte]
      omega
    · simp only [h, ↓reduceDIte]
      have hmod : (2 * (i.val - m) + 1) % 2 ≠ 0 := by omega
      simp only [hmod, ↓reduceDIte]
      omega

private theorem interleavePerm_symm_left (m : ℕ) (i : Fin m) :
    (interleavePerm m).symm ⟨i.val, by omega⟩ = ⟨2 * i.val, by omega⟩ := by
  ext
  simp [interleavePerm, i.isLt]

private theorem interleavePerm_symm_right (m : ℕ) (i : Fin m) :
    (interleavePerm m).symm ⟨m + i.val, by omega⟩ = ⟨2 * i.val + 1, by omega⟩ := by
  ext
  have hnot : ¬ (m + i.val < m) := by omega
  simp [interleavePerm, hnot]

/-- Three-state summary of a prefix `ρ` under `interleavePerm m`:
`none` if some completed pair already disagreed; `some b` if all completed pairs agreed and
`b` is the pending unpaired bit (or `false` at even layers). -/
private def eqInterleaveSummary (m t : ℕ) (ρ : Fin t → Bool) : Option Bool :=
  if ∃ j : Fin m, ∃ h₁ : 2 * j.val < t, ∃ h₂ : 2 * j.val + 1 < t,
      ρ ⟨2 * j.val, h₁⟩ ≠ ρ ⟨2 * j.val + 1, h₂⟩ then
    none
  else if hodd : t % 2 = 1 then
    some (ρ ⟨t - 1, by omega⟩)
  else
    some false

/-- **Order-Sensitivity Upper Bound (`eqFn`)**: Under the interleaved variable order
`interleavePerm m`, `eqFn m` has at most `3` residual classes at every layer `t ≤ 2 * m`. -/
theorem eq_interleaved_residualClassCount_le (m : ℕ) (t : ℕ) (ht : t ≤ 2 * m) :
    residualClassCount (eqFn m) (interleavePerm m) t ht ≤ 3 := by
  have hle :=
    residualClassCount_le_card_of_factor (eqFn m) (interleavePerm m) t ht
      (eqInterleaveSummary m t) (fun ρ₁ ρ₂ hEq τ => by
        unfold residualFn eqFn
        suffices hiff :
            (∀ i : Fin m,
              glue (interleavePerm m) t ht ρ₁ τ ⟨i.val, by omega⟩ =
                glue (interleavePerm m) t ht ρ₁ τ ⟨m + i.val, by omega⟩) ↔
            (∀ i : Fin m,
              glue (interleavePerm m) t ht ρ₂ τ ⟨i.val, by omega⟩ =
                glue (interleavePerm m) t ht ρ₂ τ ⟨m + i.val, by omega⟩) by
          simp [hiff]
        have hbad_iff :
            (∃ j : Fin m, ∃ h₁ : 2 * j.val < t, ∃ h₂ : 2 * j.val + 1 < t,
              ρ₁ ⟨2 * j.val, h₁⟩ ≠ ρ₁ ⟨2 * j.val + 1, h₂⟩) ↔
            (∃ j : Fin m, ∃ h₁ : 2 * j.val < t, ∃ h₂ : 2 * j.val + 1 < t,
              ρ₂ ⟨2 * j.val, h₁⟩ ≠ ρ₂ ⟨2 * j.val + 1, h₂⟩) := by
          constructor <;> intro h
          · have h1 : eqInterleaveSummary m t ρ₁ = none := by
              simp [eqInterleaveSummary, h]
            rw [hEq] at h1
            by_contra h2
            simp only [eqInterleaveSummary, h2, ↓reduceIte] at h1
            split_ifs at h1
          · have h2 : eqInterleaveSummary m t ρ₂ = none := by
              simp [eqInterleaveSummary, h]
            rw [← hEq] at h2
            by_contra h1
            simp only [eqInterleaveSummary, h1, ↓reduceIte] at h2
            split_ifs at h2
        have hstep : ∀ ρ : Fin t → Bool, ∀ i : Fin m,
            glue (interleavePerm m) t ht ρ τ ⟨i.val, by omega⟩ =
              glue (interleavePerm m) t ht ρ τ ⟨m + i.val, by omega⟩ ↔
            (if h₁ : 2 * i.val < t then ρ ⟨2 * i.val, h₁⟩
              else τ ⟨2 * i.val - t, by omega⟩) =
            (if h₂ : 2 * i.val + 1 < t then ρ ⟨2 * i.val + 1, h₂⟩
              else τ ⟨2 * i.val + 1 - t, by omega⟩) := by
          intro ρ i
          simp [glue, interleavePerm_symm_left, interleavePerm_symm_right]
        by_cases hbad :
            ∃ j : Fin m, ∃ h₁ : 2 * j.val < t, ∃ h₂ : 2 * j.val + 1 < t,
              ρ₁ ⟨2 * j.val, h₁⟩ ≠ ρ₁ ⟨2 * j.val + 1, h₂⟩
        · have hbad₂ := hbad_iff.mp hbad
          constructor
          · intro hall
            rcases hbad with ⟨j, h₁, h₂, hne⟩
            have hj := (hstep ρ₁ j).mp (hall j)
            simp [h₁, h₂] at hj
            exact absurd hj hne
          · intro hall
            rcases hbad₂ with ⟨j, h₁, h₂, hne⟩
            have hj := (hstep ρ₂ j).mp (hall j)
            simp [h₁, h₂] at hj
            exact absurd hj hne
        · have hbad₂ : ¬ ∃ j : Fin m, ∃ h₁ : 2 * j.val < t, ∃ h₂ : 2 * j.val + 1 < t,
              ρ₂ ⟨2 * j.val, h₁⟩ ≠ ρ₂ ⟨2 * j.val + 1, h₂⟩ :=
            fun h => hbad (hbad_iff.mpr h)
          have hodd_eq : ∀ hodd : t % 2 = 1,
              ρ₁ ⟨t - 1, by omega⟩ = ρ₂ ⟨t - 1, by omega⟩ := by
            intro hodd
            have h1 : eqInterleaveSummary m t ρ₁ = some (ρ₁ ⟨t - 1, by omega⟩) := by
              simp [eqInterleaveSummary, hbad, hodd]
            have h2 : eqInterleaveSummary m t ρ₂ = some (ρ₂ ⟨t - 1, by omega⟩) := by
              simp [eqInterleaveSummary, hbad₂, hodd]
            exact Option.some.inj (h1.symm.trans (hEq.trans h2))
          have hcoord : ∀ i : Fin m,
              (glue (interleavePerm m) t ht ρ₁ τ ⟨i.val, by omega⟩ =
                glue (interleavePerm m) t ht ρ₁ τ ⟨m + i.val, by omega⟩) ↔
              (glue (interleavePerm m) t ht ρ₂ τ ⟨i.val, by omega⟩ =
                glue (interleavePerm m) t ht ρ₂ τ ⟨m + i.val, by omega⟩) := by
            intro i
            rw [hstep ρ₁ i, hstep ρ₂ i]
            by_cases h₂ : 2 * i.val + 1 < t
            · have h₁ : 2 * i.val < t := by omega
              have hEq₁ : ρ₁ ⟨2 * i.val, h₁⟩ = ρ₁ ⟨2 * i.val + 1, h₂⟩ := by
                by_contra hne
                exact hbad ⟨i, h₁, h₂, hne⟩
              have hEq₂ : ρ₂ ⟨2 * i.val, h₁⟩ = ρ₂ ⟨2 * i.val + 1, h₂⟩ := by
                by_contra hne
                exact hbad₂ ⟨i, h₁, h₂, hne⟩
              simp [h₁, h₂, hEq₁, hEq₂]
            · by_cases h₁ : 2 * i.val < t
              · have hodd : t % 2 = 1 := by omega
                have hidx : (⟨2 * i.val, h₁⟩ : Fin t) = ⟨t - 1, by omega⟩ := by
                  ext; dsimp; omega
                simp only [h₁, h₂, ↓reduceDIte, hidx, hodd_eq hodd]
              · simp [h₁, h₂]
          exact ⟨fun h i => (hcoord i).mp (h i), fun h i => (hcoord i).mpr (h i)⟩)
  simpa using hle

end Mathmatica.ResidualEntropy
