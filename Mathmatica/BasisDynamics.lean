/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.TseitinExpander

/-!
# Unified Elimination Dynamics and Dual-Basis Separation on Tseitin Expanders

This module formalizes a unified `(Basis, ElimDynamics)` abstraction for variable-elimination
dynamics across algebraic bases, instantiating it on both the Boolean CNF basis (Davis–Putnam
resolution `dpDynamics`) and the `GF(2)`-linear basis (pivot Gaussian elimination `xorDynamics`),
and establishes a conditional parameterized basis-dynamics separation on Tseitin formulas over
bounded-degree edge expanders.

## Main definitions

* `Basis`: An algebraic representation basis (`Rep : ℕ → Type`) equipped with Boolean
  satisfaction semantics (`Models`).
* `ElimDynamics B n`: A variable-elimination dynamical system on `B.Rep n` equipped with a
  single-variable elimination step `elimStep`, representation size `size`, and clause/equation
  width `width`.
* `elimTrace D vs F₀ t`: The state of `D` after `t` elimination steps along `vs` (freezing at the
  final state once `t ≥ vs.length`).
* `maxWidthTrace D vs F₀`: The peak width along the elimination trajectory `0, …, vs.length`.
* `cumulativeAction D vs F₀`: The cumulative size action `∑ t ∈ Finset.range (vs.length + 1),
  D.size (elimTrace D vs F₀ t)` along the elimination trajectory.
* `dpStep v φ`: Exact Davis–Putnam variable elimination on `CNF n`.
* `cnfBasis`, `dpDynamics`, `f2Basis`, `xorDynamics`: Concrete instantiations for CNF and
  `GF(2)`-linear systems.
* `dpTraceClauses vs φ`: The clause sequence accumulated along a Davis–Putnam elimination trace.
* `OddTotalCharge χ`: Predicate asserting that the total XOR charge over all vertices is `true`.

## Main results

* `dpStep_elim`: Eliminating `v` removes both polarities of `v` from every clause.
* `satCNF_of_satCNF_dpStep`: Satisfiability lifting across a single Davis–Putnam step.
* `dpTrace_isDAGRefutation`: Along any full variable order `vs` on an unsatisfiable CNF `φ`,
  `dpTraceClauses vs φ` is a general DAG resolution refutation whose width is bounded by
  `maxWidthTrace dpDynamics vs φ` and whose size equals `cumulativeAction dpDynamics vs φ`.
* `fold_xor_evalXor_incidentEdges` and `tseitinCNF_unsat_of_oddCharge`: Handshaking parity
  identity for loopless graphs and unsatisfiability of odd-charge Tseitin CNF formulas.
* `tseitin_basis_dynamics_separation`: Conditional parameterized separation contrasting zero-bloat
  `GF(2)` Gaussian elimination against width and exponential cumulative-action lower bounds for
  CNF Davis–Putnam elimination (and general DAG resolution) on bounded-degree edge expanders.
-/

namespace Mathmatica.BasisDynamics

open Mathmatica.BSWTradeoff
open Mathmatica.DAGResolution
open Mathmatica.BSWDAGFull
open Mathmatica.ExpanderWidth
open Mathmatica.XORSATBasis
open Mathmatica.TseitinExpander

local instance : Std.Commutative xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative xor := ⟨Bool.xor_assoc⟩

/-! ### Unified basis and elimination dynamics skeleton -/

/-- An algebraic representation basis for Boolean constraint systems over `Fin n → Bool`. -/
structure Basis where
  /-- Representation type for constraint systems on `n` Boolean variables. -/
  Rep : ℕ → Type
  /-- Semantic satisfaction relation between a representation and a Boolean assignment. -/
  Models : ∀ {n : ℕ}, Rep n → (Fin n → Bool) → Prop

/-- A variable-elimination dynamical system over a representation basis `B` on `n` variables. -/
structure ElimDynamics (B : Basis) (n : ℕ) where
  /-- Single-variable elimination operator. -/
  elimStep : Fin n → B.Rep n → B.Rep n
  /-- Size observable of a state (number of clauses or linear equations). -/
  size : B.Rep n → ℕ
  /-- Width observable of a state (maximum clause or equation support cardinality). -/
  width : B.Rep n → ℕ

/-- The state reached by advancing `t` steps along the variable order `vs` from `F₀`.
For `t ≥ vs.length`, the trajectory stays at the terminal state. -/
def elimTrace {B : Basis} {n : ℕ} (D : ElimDynamics B n)
    (vs : List (Fin n)) (F₀ : B.Rep n) : ℕ → B.Rep n
  | 0 => F₀
  | t + 1 =>
    match vs with
    | [] => F₀
    | v :: vs' => elimTrace D vs' (D.elimStep v F₀) t

@[simp]
lemma elimTrace_zero {B : Basis} {n : ℕ} (D : ElimDynamics B n)
    (vs : List (Fin n)) (F₀ : B.Rep n) :
    elimTrace D vs F₀ 0 = F₀ := by
  rw [elimTrace]

@[simp]
lemma elimTrace_nil {B : Basis} {n : ℕ} (D : ElimDynamics B n) (F₀ : B.Rep n) (t : ℕ) :
    elimTrace D [] F₀ t = F₀ := by
  cases t <;> simp [elimTrace]

@[simp]
lemma elimTrace_cons_succ {B : Basis} {n : ℕ} (D : ElimDynamics B n)
    (v : Fin n) (vs : List (Fin n)) (F₀ : B.Rep n) (t : ℕ) :
    elimTrace D (v :: vs) F₀ (t + 1) = elimTrace D vs (D.elimStep v F₀) t := rfl

/-- The peak width attained along the elimination trajectory `0, 1, …, vs.length`. -/
def maxWidthTrace {B : Basis} {n : ℕ} (D : ElimDynamics B n) :
    List (Fin n) → B.Rep n → ℕ
  | [], F₀ => D.width F₀
  | v :: vs, F₀ => max (D.width F₀) (maxWidthTrace D vs (D.elimStep v F₀))

/-- Every state along the elimination trace has width at most `maxWidthTrace D vs F₀`. -/
lemma width_elimTrace_le_maxWidthTrace {B : Basis} {n : ℕ} (D : ElimDynamics B n)
    (vs : List (Fin n)) (F₀ : B.Rep n) (t : ℕ) :
    D.width (elimTrace D vs F₀ t) ≤ maxWidthTrace D vs F₀ := by
  induction vs generalizing F₀ t with
  | nil => simp [maxWidthTrace]
  | cons v vs ih =>
    cases t with
    | zero => exact le_max_left _ _
    | succ t => exact le_trans (ih (D.elimStep v F₀) t) (le_max_right _ _)

/-- The cumulative size action `∑_{t=0}^{|vs|} size(F_t)` along the elimination trajectory. -/
def cumulativeAction {B : Basis} {n : ℕ} (D : ElimDynamics B n) :
    List (Fin n) → B.Rep n → ℕ
  | [], F₀ => D.size F₀
  | v :: vs, F₀ => D.size F₀ + cumulativeAction D vs (D.elimStep v F₀)

/-- `cumulativeAction` equals the explicit finite sum of `D.size (elimTrace D vs F₀ t)` over
`t ∈ Finset.range (vs.length + 1)`. -/
lemma cumulativeAction_eq_sum {B : Basis} {n : ℕ} (D : ElimDynamics B n)
    (vs : List (Fin n)) (F₀ : B.Rep n) :
    cumulativeAction D vs F₀ =
      ∑ t ∈ Finset.range (vs.length + 1), D.size (elimTrace D vs F₀ t) := by
  induction vs generalizing F₀ with
  | nil => simp [cumulativeAction]
  | cons v vs ih =>
    rw [cumulativeAction, List.length_cons, Finset.sum_range_succ']
    simp only [elimTrace_zero, elimTrace_cons_succ]
    rw [ih (D.elimStep v F₀), Nat.add_comm]

/-! ### Exact CNF Davis–Putnam elimination and basis instantiations -/

/-- Exact single-variable Davis–Putnam elimination step on a CNF formula `φ`: retain clauses
not mentioning `v` and add all resolvents between clauses containing `⟨v, true⟩` (and not
`⟨v, false⟩`) and clauses containing `⟨v, false⟩` (and not `⟨v, true⟩`). -/
def dpStep {n : ℕ} (v : Fin n) (φ : CNF n) : CNF n :=
  let rest := φ.filter (fun c => Lit.mk v true ∉ c ∧ Lit.mk v false ∉ c)
  let pos := φ.filter (fun c => Lit.mk v true ∈ c ∧ Lit.mk v false ∉ c)
  let neg := φ.filter (fun c => Lit.mk v true ∉ c ∧ Lit.mk v false ∈ c)
  let res :=
    pos.biUnion (fun c₁ =>
      neg.image (fun c₂ => (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))))
  rest ∪ res

/-- The Boolean CNF representation basis. -/
@[reducible]
def cnfBasis : Basis where
  Rep := CNF
  Models := fun φ σ => SatCNF σ φ

/-- The `GF(2)`-linear representation basis (XOR-SAT). -/
@[reducible]
def f2Basis : Basis where
  Rep := LinSys
  Models := fun sys σ => SatSys σ sys

/-- Davis–Putnam variable-elimination dynamics in the Boolean CNF basis. -/
def dpDynamics {n : ℕ} : ElimDynamics cnfBasis n where
  elimStep := dpStep
  size := Finset.card
  width := fun φ => φ.sup Finset.card

/-- Pivot Gaussian variable-elimination dynamics in the `GF(2)`-linear basis. -/
def xorDynamics {n : ℕ} : ElimDynamics f2Basis n where
  elimStep := gaussElimVar
  size := List.length
  width := fun sys => sys.foldr (fun eq acc => max eq.vars.card acc) 0

/-! ### Properties of `dpStep` and bridge to general DAG resolution -/

/-- After `dpStep v φ`, neither polarity of `v` occurs in any remaining clause. -/
theorem dpStep_elim {n : ℕ} (v : Fin n) (φ : CNF n) :
    ∀ c ∈ dpStep v φ, Lit.mk v true ∉ c ∧ Lit.mk v false ∉ c := by
  intro c hc
  unfold dpStep at hc
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image] at hc
  rcases hc with ⟨_, hnt, hnf⟩ | ⟨c₁, ⟨_, _, h1f⟩, c₂, ⟨_, h2t, _⟩, rfl⟩
  · exact ⟨hnt, hnf⟩
  · constructor
    · simp [Finset.mem_union, Finset.mem_erase, h2t]
    · simp [Finset.mem_union, Finset.mem_erase, h1f]

/-- If a variable `u` does not occur in any clause of `φ`, it also does not occur in `dpStep v φ`.
-/
lemma dpStep_preserves_elim {n : ℕ} {u v : Fin n} {φ : CNF n}
    (hu : ∀ c ∈ φ, Lit.mk u true ∉ c ∧ Lit.mk u false ∉ c) :
    ∀ c ∈ dpStep v φ, Lit.mk u true ∉ c ∧ Lit.mk u false ∉ c := by
  intro c hc
  unfold dpStep at hc
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image] at hc
  rcases hc with ⟨hcφ, _, _⟩ | ⟨c₁, ⟨hc₁, _, _⟩, c₂, ⟨hc₂, _, _⟩, rfl⟩
  · exact hu c hcφ
  · have h1 := hu c₁ hc₁
    have h2 := hu c₂ hc₂
    constructor
    · simp [Finset.mem_union, Finset.mem_erase, h1.1, h2.1]
    · simp [Finset.mem_union, Finset.mem_erase, h1.2, h2.2]

/-- Every clause in `dpStep v φ` is either in `φ` or a resolvent of two clauses in `φ`. -/
lemma dpStep_mem_or_resolvent {n : ℕ} {v : Fin n} {φ : CNF n} {c : Clause n}
    (hc : c ∈ dpStep v φ) :
    c ∈ φ ∨ ∃ c₁ ∈ φ, ∃ c₂ ∈ φ, IsResolvent c₁ c₂ c := by
  unfold dpStep at hc
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image] at hc
  rcases hc with ⟨hcφ, _, _⟩ | ⟨c₁, ⟨hc₁, h1t, _⟩, c₂, ⟨hc₂, _, h2f⟩, rfl⟩
  · exact Or.inl hcφ
  · exact Or.inr ⟨c₁, hc₁, c₂, hc₂, v, h1t, h2f, rfl⟩

/-- Completeness (assignment lifting) of Davis–Putnam elimination: if `dpStep v φ` is
satisfiable, then `φ` is satisfiable. -/
theorem satCNF_of_satCNF_dpStep {n : ℕ} {v : Fin n} {φ : CNF n} {σ : Assign n}
    (hsat : SatCNF σ (dpStep v φ)) :
    ∃ σ' : Assign n, SatCNF σ' φ := by
  let σt : Assign n := updateAssign σ v true
  let σf : Assign n := updateAssign σ v false
  by_cases ht : SatCNF σt φ
  · exact ⟨σt, ht⟩
  · by_cases hf : SatCNF σf φ
    · exact ⟨σf, hf⟩
    · exfalso
      unfold SatCNF at ht hf
      push Not at ht hf
      obtain ⟨c₂, hc₂, hnt₂⟩ := ht
      obtain ⟨c₁, hc₁, hnf₁⟩ := hf
      have hc₂_nt : Lit.mk v true ∉ c₂ := fun hmem =>
        hnt₂ ⟨Lit.mk v true, hmem, by simp [σt, updateAssign]⟩
      have hc₁_nf : Lit.mk v false ∉ c₁ := fun hmem =>
        hnf₁ ⟨Lit.mk v false, hmem, by simp [σf, updateAssign]⟩
      have hc₂_f : Lit.mk v false ∈ c₂ := by
        by_contra hnf₂
        have hmem : c₂ ∈ dpStep v φ := by
          unfold dpStep
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc₂, hc₂_nt, hnf₂⟩)
        obtain ⟨l, hl, hσl⟩ := hsat c₂ hmem
        have hne : l.var ≠ v := by
          intro hvar
          cases l with
          | mk lv lp =>
            dsimp only at hvar
            subst hvar
            cases lp
            · exact hnf₂ hl
            · exact hc₂_nt hl
        exact hnt₂ ⟨l, hl, by simpa [σt, updateAssign, hne] using hσl⟩
      have hc₁_t : Lit.mk v true ∈ c₁ := by
        by_contra hnt₁
        have hmem : c₁ ∈ dpStep v φ := by
          unfold dpStep
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc₁, hnt₁, hc₁_nf⟩)
        obtain ⟨l, hl, hσl⟩ := hsat c₁ hmem
        have hne : l.var ≠ v := by
          intro hvar
          cases l with
          | mk lv lp =>
            dsimp only at hvar
            subst hvar
            cases lp
            · exact hc₁_nf hl
            · exact hnt₁ hl
        exact hnf₁ ⟨l, hl, by simpa [σf, updateAssign, hne] using hσl⟩
      let cres : Clause n := (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))
      have hcres : cres ∈ dpStep v φ := by
        unfold dpStep
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_biUnion.mpr
          ⟨c₁, Finset.mem_filter.mpr ⟨hc₁, hc₁_t, hc₁_nf⟩, ?_⟩
        exact Finset.mem_image.mpr
          ⟨c₂, Finset.mem_filter.mpr ⟨hc₂, hc₂_nt, hc₂_f⟩, rfl⟩
      obtain ⟨l, hl, hσl⟩ := hsat cres hcres
      rcases Finset.mem_union.mp hl with hl₁ | hl₂
      · obtain ⟨hlne, hlc₁⟩ := Finset.mem_erase.mp hl₁
        have hne : l.var ≠ v := by
          intro hvar
          cases l with
          | mk lv lp =>
            dsimp only at hvar
            subst hvar
            cases lp
            · exact hc₁_nf hlc₁
            · exact hlne rfl
        exact hnf₁ ⟨l, hlc₁, by simpa [σf, updateAssign, hne] using hσl⟩
      · obtain ⟨hlne, hlc₂⟩ := Finset.mem_erase.mp hl₂
        have hne : l.var ≠ v := by
          intro hvar
          cases l with
          | mk lv lp =>
            dsimp only at hvar
            subst hvar
            cases lp
            · exact hlne rfl
            · exact hc₂_nt hlc₂
        exact hnt₂ ⟨l, hlc₂, by simpa [σt, updateAssign, hne] using hσl⟩

/-- The clause sequence accumulated along a Davis–Putnam elimination trace `vs` from `φ`.
Each layer `φ.toList` precedes all subsequent layers derived from `dpStep v φ`. -/
noncomputable def dpTraceClauses {n : ℕ} : List (Fin n) → CNF n → List (Clause n)
  | [], φ => φ.toList
  | v :: vs, φ => φ.toList ++ dpTraceClauses vs (dpStep v φ)

/-- The length of `dpTraceClauses vs φ` equals the cumulative size action
`cumulativeAction dpDynamics vs φ`. -/
lemma dpTraceClauses_length {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    dagSize (dpTraceClauses vs φ) = cumulativeAction dpDynamics vs φ := by
  induction vs generalizing φ with
  | nil =>
    simp [dpTraceClauses, dagSize, cumulativeAction, dpDynamics]
  | cons v vs ih =>
    simp only [dpTraceClauses, dagSize, List.length_append, Finset.length_toList,
      cumulativeAction, dpDynamics]
    exact congrArg (φ.card + ·) (ih (dpStep v φ))

/-- The width of `dpTraceClauses vs φ` is bounded by `maxWidthTrace dpDynamics vs φ`. -/
lemma dagWidth_dpTraceClauses_le {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    dagWidth (dpTraceClauses vs φ) ≤ maxWidthTrace dpDynamics vs φ := by
  rw [dagWidth_le_iff]
  induction vs generalizing φ with
  | nil =>
    intro c hc
    rw [dpTraceClauses, Finset.mem_toList] at hc
    exact Finset.le_sup (f := Finset.card) hc
  | cons v vs ih =>
    intro c hc
    rw [dpTraceClauses, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [Finset.mem_toList] at hc
      exact le_trans (Finset.le_sup (f := Finset.card) hc) (le_max_left _ _)
    · exact le_trans (ih (dpStep v φ) c hc) (le_max_right _ _)

/-- Every clause in the terminal state `elimTrace dpDynamics vs φ vs.length` appears in
`dpTraceClauses vs φ`. -/
private lemma mem_dpTraceClauses_of_mem_final {n : ℕ} (vs : List (Fin n)) (φ : CNF n)
    {c : Clause n} (hc : c ∈ elimTrace dpDynamics vs φ vs.length) :
    c ∈ dpTraceClauses vs φ := by
  induction vs generalizing φ with
  | nil =>
    simpa [dpTraceClauses, Finset.mem_toList] using hc
  | cons v vs ih =>
    rw [dpTraceClauses, List.mem_append]
    exact Or.inr (ih (dpStep v φ) hc)

/-- If a variable `u` does not occur in `φ`, it does not occur in the terminal state of
`dpDynamics` along any `vs`. -/
private lemma dpTrace_preserves_elim {n : ℕ} (vs : List (Fin n)) (φ : CNF n) {u : Fin n}
    (hu : ∀ c ∈ φ, Lit.mk u true ∉ c ∧ Lit.mk u false ∉ c) :
    ∀ c ∈ elimTrace dpDynamics vs φ vs.length,
      Lit.mk u true ∉ c ∧ Lit.mk u false ∉ c := by
  induction vs generalizing φ with
  | nil => exact hu
  | cons w ws ih => exact ih (dpStep w φ) (dpStep_preserves_elim hu)

/-- Iterated Davis–Putnam elimination eliminates every variable appearing in `vs`. -/
private lemma dpTrace_final_elim {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    ∀ v ∈ vs, ∀ c ∈ elimTrace dpDynamics vs φ vs.length,
      Lit.mk v true ∉ c ∧ Lit.mk v false ∉ c := by
  induction vs generalizing φ with
  | nil =>
    intro v hv
    simp at hv
  | cons u vs ih =>
    intro v hv c hc
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact dpTrace_preserves_elim vs (dpStep v φ) (dpStep_elim v φ) c hc
    · exact ih (dpStep u φ) v hv c hc

/-- Satisfiability lifts across the entire Davis–Putnam elimination trace. -/
private lemma satCNF_of_satCNF_final {n : ℕ} (vs : List (Fin n)) (φ : CNF n) {σ : Assign n}
    (hsat : SatCNF σ (elimTrace dpDynamics vs φ vs.length)) :
    ∃ σ' : Assign n, SatCNF σ' φ := by
  induction vs generalizing φ σ with
  | nil => exact ⟨σ, hsat⟩
  | cons v vs ih =>
    obtain ⟨σ₁, hσ₁⟩ := ih (dpStep v φ) hsat
    exact satCNF_of_satCNF_dpStep hσ₁

/-- Every Davis–Putnam trace `dpTraceClauses vs φ` is a valid general DAG resolution proof from
`φ`. -/
theorem dpTraceClauses_isDAGProof {n : ℕ} (vs : List (Fin n)) (φ : CNF n) :
    IsDAGProof φ (dpTraceClauses vs φ) := by
  induction vs generalizing φ with
  | nil =>
    intro i hi
    left
    exact Finset.mem_toList.mp (List.getElem_mem hi)
  | cons v vs ih =>
    change IsDAGProof φ (φ.toList ++ dpTraceClauses vs (dpStep v φ))
    set L₁ := φ.toList
    set L₂ := dpTraceClauses vs (dpStep v φ)
    intro i hi
    by_cases hlt : i < L₁.length
    · left
      rw [List.getElem_append_left hlt]
      exact Finset.mem_toList.mp (List.getElem_mem hlt)
    · have hle : L₁.length ≤ i := Nat.le_of_not_lt hlt
      have hi' : i - L₁.length < L₂.length := by
        rw [List.length_append] at hi
        omega
      have hget : (L₁ ++ L₂)[i]'hi = L₂[i - L₁.length]'hi' := List.getElem_append_right hle
      rcases ih (dpStep v φ) (i - L₁.length) hi' with hax | ⟨j', k', hj', hk', hres⟩
      · rcases dpStep_mem_or_resolvent hax with hφ | ⟨c₁, hc₁, c₂, hc₂, hres⟩
        · left
          rw [hget]
          exact hφ
        · right
          obtain ⟨j, hjL, hjEq⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hc₁)
          obtain ⟨k, hkL, hkEq⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hc₂)
          have hji : j < i := lt_of_lt_of_le hjL hle
          have hki : k < i := lt_of_lt_of_le hkL hle
          refine ⟨j, k, hji, hki, ?_⟩
          have hjget : (L₁ ++ L₂)[j]'(lt_trans hji hi) = c₁ := by
            rw [List.getElem_append_left hjL]
            exact hjEq
          have hkget : (L₁ ++ L₂)[k]'(lt_trans hki hi) = c₂ := by
            rw [List.getElem_append_left hkL]
            exact hkEq
          rw [hjget, hkget, hget]
          exact hres
      · right
        have hj : L₁.length + j' < i := by omega
        have hk : L₁.length + k' < i := by omega
        refine ⟨L₁.length + j', L₁.length + k', hj, hk, ?_⟩
        have hjget :
            (L₁ ++ L₂)[L₁.length + j']'(lt_trans hj hi) = L₂[j']'(lt_trans hj' hi') := by
          rw [List.getElem_append_right (Nat.le_add_right L₁.length j')]
          simp
        have hkget :
            (L₁ ++ L₂)[L₁.length + k']'(lt_trans hk hi) = L₂[k']'(lt_trans hk' hi') := by
          rw [List.getElem_append_right (Nat.le_add_right L₁.length k')]
          simp
        rw [hjget, hkget, hget]
        exact hres

/-- **Bridge Theorem (`dpTrace_isDAGRefutation`)**:
Along any variable order `vs` covering all variables `Fin n`, the Davis–Putnam elimination trace
of an unsatisfiable CNF formula `φ` yields a general DAG resolution refutation whose width is at
most `maxWidthTrace dpDynamics vs φ` and whose size is at most `cumulativeAction dpDynamics vs φ`.
-/
theorem dpTrace_isDAGRefutation {n : ℕ} (vs : List (Fin n)) (φ : CNF n)
    (hcov : ∀ v : Fin n, v ∈ vs) (hunsat : ∀ σ : Assign n, ¬ SatCNF σ φ) :
    IsDAGRefutation φ (dpTraceClauses vs φ) ∧
      dagWidth (dpTraceClauses vs φ) ≤ maxWidthTrace dpDynamics vs φ ∧
      dagSize (dpTraceClauses vs φ) ≤ cumulativeAction dpDynamics vs φ := by
  refine ⟨⟨dpTraceClauses_isDAGProof vs φ, ?_⟩, dagWidth_dpTraceClauses_le vs φ,
    (dpTraceClauses_length vs φ).le⟩
  have hne : (elimTrace dpDynamics vs φ vs.length).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsat_final : SatCNF (fun _ => false) (elimTrace dpDynamics vs φ vs.length) := by
      rw [hemp]
      intro c hc
      exact (Finset.notMem_empty c hc).elim
    obtain ⟨σ', hσ'⟩ := satCNF_of_satCNF_final vs φ hsat_final
    exact hunsat σ' hσ'
  obtain ⟨c, hc⟩ := hne
  have hc_empty : c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro l hl
    have helim := dpTrace_final_elim vs φ l.var (hcov l.var) c hc
    cases l with
    | mk lv lp =>
      cases lp
      · exact helim.2 hl
      · exact helim.1 hl
  subst hc_empty
  exact mem_dpTraceClauses_of_mem_final vs φ hc

/-! ### Handshaking parity identity and unsatisfiability of odd-charge Tseitin formulas -/

/-- A vertex charge assignment `χ : Fin V → Bool` has odd total charge if the XOR parity of all
vertex charges is `true`. -/
def OddTotalCharge {V : ℕ} (χ : Fin V → Bool) : Prop :=
  (Finset.univ : Finset (Fin V)).fold xor false χ = true

private lemma fold_xor_const_false {α : Type*} [DecidableEq α] (s : Finset α) :
    s.fold xor false (fun _ => false) = false := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.fold_insert ha, ih]
    rfl

private lemma fold_xor_xor {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → Bool) :
    s.fold xor false (fun x => xor (f x) (g x)) =
      xor (s.fold xor false f) (s.fold xor false g) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.fold_insert ha, Finset.fold_insert ha, Finset.fold_insert ha, ih]
    cases f a <;> cases g a <;> cases s.fold xor false f <;> cases s.fold xor false g <;> rfl

private lemma fold_xor_two_points {V : ℕ} {u₁ u₂ : Fin V} (hne : u₁ ≠ u₂) (b : Bool) :
    (Finset.univ : Finset (Fin V)).fold xor false
      (fun v => if v = u₁ ∨ v = u₂ then b else false) = false := by
  have h1 : (Finset.univ : Finset (Fin V)) = insert u₁ (Finset.univ.erase u₁) :=
    (Finset.insert_erase (Finset.mem_univ u₁)).symm
  have hu₂ : u₂ ∈ (Finset.univ : Finset (Fin V)).erase u₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ u₂⟩
  have h2 : (Finset.univ : Finset (Fin V)).erase u₁ =
      insert u₂ (((Finset.univ : Finset (Fin V)).erase u₁).erase u₂) :=
    (Finset.insert_erase hu₂).symm
  set rest := ((Finset.univ : Finset (Fin V)).erase u₁).erase u₂
  have hrest_eq :
      rest.fold xor false (fun v => if v = u₁ ∨ v = u₂ then b else false) =
        rest.fold xor false (fun _ => false) := by
    refine Finset.fold_congr fun v hv => ?_
    have hv₂ : v ≠ u₂ := (Finset.mem_erase.mp hv).1
    have hv₁ : v ≠ u₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    simp [hv₁, hv₂]
  rw [h1, Finset.fold_insert (Finset.notMem_erase u₁ _), h2,
    Finset.fold_insert (Finset.notMem_erase u₂ _), hrest_eq, fold_xor_const_false]
  simp

private lemma fold_xor_evalXor_filter {V E : ℕ} (G : IndexedGraph V E) (σ : Assign E)
    (S : Finset (Fin E)) :
    (Finset.univ : Finset (Fin V)).fold xor false
      (fun v => evalXor σ (S.filter (fun e => (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v))) =
      false := by
  induction S using Finset.induction_on with
  | empty =>
    simpa [evalXor_empty] using (fold_xor_const_false (Finset.univ : Finset (Fin V)))
  | @insert e S he ih =>
    set u₁ := (G.endpoints e).1
    set u₂ := (G.endpoints e).2
    have hpoint :
        ∀ v : Fin V,
          evalXor σ ((insert e S).filter (fun e' => (G.endpoints e').1 = v ∨
            (G.endpoints e').2 = v)) =
          xor (if v = u₁ ∨ v = u₂ then σ e else false)
            (evalXor σ (S.filter (fun e' => (G.endpoints e').1 = v ∨
              (G.endpoints e').2 = v))) := by
      intro v
      by_cases hv : v = u₁ ∨ v = u₂
      · have hcond : (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v := by
          rcases hv with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hnotmem :
            e ∉ S.filter (fun e' => (G.endpoints e').1 = v ∨ (G.endpoints e').2 = v) :=
          fun h => he (Finset.mem_filter.mp h).1
        rw [Finset.filter_insert]
        simp only [hcond, hv, ↓reduceIte]
        exact evalXor_insert σ hnotmem
      · have hcond : ¬ ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v) := by
          intro h
          rcases h with h | h
          · exact hv (Or.inl h.symm)
          · exact hv (Or.inr h.symm)
        rw [Finset.filter_insert]
        simp only [hcond, hv, ↓reduceIte, Bool.false_xor]
    have hfun :
        (fun v : Fin V =>
          evalXor σ ((insert e S).filter (fun e' => (G.endpoints e').1 = v ∨
            (G.endpoints e').2 = v))) =
        (fun v : Fin V =>
          xor (if v = u₁ ∨ v = u₂ then σ e else false)
            (evalXor σ (S.filter (fun e' => (G.endpoints e').1 = v ∨
              (G.endpoints e').2 = v)))) :=
      funext hpoint
    rw [hfun, fold_xor_xor, fold_xor_two_points (G.loopless e) (σ e), ih]
    rfl

/-- **Handshaking Parity Identity**: In any loopless graph `G`, every edge is incident to two
distinct vertices, so the XOR sum of vertex parities vanishes identically for every edge
assignment `σ`. -/
theorem fold_xor_evalXor_incidentEdges {V E : ℕ} (G : IndexedGraph V E) (σ : Assign E) :
    (Finset.univ : Finset (Fin V)).fold xor false (fun v => evalXor σ (incidentEdges G v)) =
      false :=
  fold_xor_evalXor_filter G σ Finset.univ

/-- **Unsatisfiability of Odd-Charge Tseitin Formulas**:
Whenever `OddTotalCharge χ` holds on a loopless graph `G`, `tseitinCNF G χ` is unsatisfiable. -/
theorem tseitinCNF_unsat_of_oddCharge {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (hodd : OddTotalCharge χ) :
    ∀ σ : Assign E, ¬ SatCNF σ (tseitinCNF G χ) := by
  intro σ hsat
  have hlin : SatSys σ (tseitinLinSys G χ) := (satCNF_iff_satLinSys G χ σ).mp hsat
  have heq : ∀ v : Fin V, evalXor σ (incidentEdges G v) = χ v := fun v =>
    hlin (tseitinLinEq G χ v) (List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩)
  have hfold :
      (Finset.univ : Finset (Fin V)).fold xor false χ =
        (Finset.univ : Finset (Fin V)).fold xor false
          (fun v => evalXor σ (incidentEdges G v)) := by
    congr 1
    funext v
    exact (heq v).symm
  rw [fold_xor_evalXor_incidentEdges G σ] at hfold
  rw [OddTotalCharge, hfold] at hodd
  exact Bool.false_ne_true hodd

/-! ### Conditional parameterized basis-dynamics separation on Tseitin expanders -/

/-- Every state along a `GF(2)` Gaussian elimination trace has at most as many equations as the
initial system. -/
lemma xorDynamics_elimTrace_length_le {n : ℕ} (vs : List (Fin n)) (sys : LinSys n) (t : ℕ) :
    (elimTrace xorDynamics vs sys t).length ≤ sys.length := by
  induction vs generalizing sys t with
  | nil => simp
  | cons v vs ih =>
    cases t with
    | zero => exact le_rfl
    | succ t =>
      exact le_trans (ih (gaussElimVar v sys) t) (gaussElimVar_length_le v sys)

/-- The cumulative size action of `GF(2)` Gaussian elimination along `vs` is at most
`(vs.length + 1) * sys.length`. -/
lemma xorDynamics_cumulativeAction_le {n : ℕ} (vs : List (Fin n)) (sys : LinSys n) :
    cumulativeAction xorDynamics vs sys ≤ (vs.length + 1) * sys.length := by
  induction vs generalizing sys with
  | nil =>
    simp [cumulativeAction, xorDynamics]
  | cons v vs ih =>
    rw [cumulativeAction, List.length_cons]
    change sys.length + cumulativeAction xorDynamics vs (gaussElimVar v sys) ≤
      (vs.length + 1 + 1) * sys.length
    have h1 : cumulativeAction xorDynamics vs (gaussElimVar v sys) ≤
        (vs.length + 1) * (gaussElimVar v sys).length := ih (gaussElimVar v sys)
    have h2 : (vs.length + 1) * (gaussElimVar v sys).length ≤ (vs.length + 1) * sys.length :=
      Nat.mul_le_mul_left (vs.length + 1) (gaussElimVar_length_le v sys)
    have hstep := le_trans h1 h2
    have hmul : (vs.length + 1 + 1) * sys.length = sys.length + (vs.length + 1) * sys.length := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

/-- **Conditional Parameterized Basis-Dynamics Separation on Tseitin Expanders**:
For any bounded-degree `(c_exp / q)`-edge expander `G` (`0 < c_exp`, maximum degree `≤ Δ`) with
an odd-charge assignment `χ` and any full edge elimination order `vs`, the exact same Tseitin
constraints exhibit an algebraic basis separation under variable-elimination dynamics:

1. In the `GF(2)`-linear basis (`xorDynamics`), every intermediate system along the trace has at
   most `V` equations and the cumulative action is at most `(vs.length + 1) * V`.
2. In the Boolean CNF basis (`dpDynamics`, and hence general DAG resolution), the elimination trace
   attains peak width at least `max Δ k + r + 1`.
3. In the Boolean CNF basis (`dpDynamics`), the cumulative size action satisfies the exponential
   lower bound `(2 * E) ^ r ≤ (2 * E - k) ^ r * cumulativeAction dpDynamics vs (tseitinCNF G χ)`.
-/
theorem tseitin_basis_dynamics_separation {V E Δ c_exp q k r T : ℕ}
    (hE : 0 < E) (hk_pos : 0 < k) (hk : k ≤ 2 * E)
    (G : IndexedGraph V E) (χ : Fin V → Bool)
    (hodd : OddTotalCharge χ)
    (hdeg : ∀ v : Fin V, (incidentEdges G v).card ≤ Δ)
    (hexp : IsEdgeExpander G c_exp q) (hc_pos : 0 < c_exp)
    (hT : 1 ≤ T) (hTV : 3 * T ≤ V)
    (hW : q * (max Δ k + r + 1) ≤ c_exp * T)
    (vs : List (Fin E)) (hcov : ∀ e : Fin E, e ∈ vs) :
    ((∀ t : ℕ, (elimTrace xorDynamics vs (tseitinLinSys G χ) t).length ≤ V) ∧
      cumulativeAction xorDynamics vs (tseitinLinSys G χ) ≤ (vs.length + 1) * V) ∧
    max Δ k + r + 1 ≤ maxWidthTrace dpDynamics vs (tseitinCNF G χ) ∧
    (2 * E) ^ r ≤ (2 * E - k) ^ r * cumulativeAction dpDynamics vs (tseitinCNF G χ) := by
  have hlen : (tseitinLinSys G χ).length = V := by simp [tseitinLinSys]
  have hxor_trace : ∀ t : ℕ, (elimTrace xorDynamics vs (tseitinLinSys G χ) t).length ≤ V :=
    fun t => le_trans (xorDynamics_elimTrace_length_le vs (tseitinLinSys G χ) t) hlen.le
  have hxor_act : cumulativeAction xorDynamics vs (tseitinLinSys G χ) ≤ (vs.length + 1) * V := by
    calc
      cumulativeAction xorDynamics vs (tseitinLinSys G χ)
          ≤ (vs.length + 1) * (tseitinLinSys G χ).length :=
            xorDynamics_cumulativeAction_le vs (tseitinLinSys G χ)
      _ = (vs.length + 1) * V := by rw [hlen]
  have hunsat : ∀ σ : Assign E, ¬ SatCNF σ (tseitinCNF G χ) :=
    tseitinCNF_unsat_of_oddCharge G χ hodd
  obtain ⟨href, hwidth, hsize⟩ := dpTrace_isDAGRefutation vs (tseitinCNF G χ) hcov hunsat
  have hEmpty : T < (tseitinMeasure G χ).μ ∅ :=
    lt_of_lt_of_le (by omega) (tseitinMeasure_empty_ge χ hexp hc_pos)
  have hbe : HasBoundaryExpansion (tseitinMeasure G χ) T (max Δ k + r + 1) :=
    tseitin_hasBoundaryExpansion χ hexp hTV hW
  have hdag_width : max Δ k + r + 1 ≤ dagWidth (dpTraceClauses vs (tseitinCNF G χ)) :=
    dagWidth_ge_of_boundary_expansion (tseitinMeasure G χ) hT hEmpty hbe
      (IsDAGRefutation.toWeak href)
  have hdag_size :
      (2 * E) ^ r ≤ (2 * E - k) ^ r * dagSize (dpTraceClauses vs (tseitinCNF G χ)) :=
    tseitin_expander_cdcl_lower_bound hE hk_pos hk G χ hdeg hexp hc_pos hT hTV hW _ href
  exact ⟨⟨hxor_trace, hxor_act⟩, le_trans hdag_width hwidth,
    le_trans hdag_size (Nat.mul_le_mul_left ((2 * E - k) ^ r) hsize)⟩

end Mathmatica.BasisDynamics
