/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Nat.Prime.Defs

/-!
# Hybrid CNF + F₂-Linear Basis Covers and Elimination Dynamics Lower Bounds

This module formalizes the static and dynamic complexity of hybrid Boolean representations
combining a bounded budget `r` of `F₂`-linear constraints (either conjunctive affine equations
`kappaConj` or disjunctive linear clauses `kappaLin`) with a CNF clause cover, over `Fin k → ZMod 2`.

## Epistemic Classification (6-Tier Status)

* **Tier 1 (Machine-verified in this module, zero `sorry`, standard axioms only)**:
  - Core hybrid cover definitions (`IsConjCover`, `IsLinCover`, `kappaConj`, `kappaLin`, `kappa0`)
    and non-vacuous existence bounds (`≤ 2 ^ k`).
  - **Theorem A (`kappaConj_linear_code_plateau` & `kappaConj_linear_code_at_rank`)**:
    Dual-distance XOR-budget plateau for `R = orthComp C_perp` via the Singleton bound:
    `2 ^ d_min * (2 ^ (m - r) - 1) ≤ 2 ^ (m - r) * kappaConj R r` and `2 ^ (d_min - 1) ≤ kappaConj R r`
    for all `r < m` (when `1 ≤ d_min`), collapsing to `kappaConj R m = 0` at `r = m`.
  - **Theorem B (`kappaLin_product_lower_bound`, `kappaLin_parity_product_exact`,
    `kappaLin_orParity_exact`, `kappaConj_orParity_blind`)**:
    Product budget-allocation theorem for disjunctive linear clauses `kappaLin` via `F₂` rank-nullity,
    exact evaluations on parity products `parityProd s d` and coupled parity-lifted disjunctions
    `orParityProd s w d`, and strict separation showing conjunctive `F₂` blindness
    (`kappaConj (orParityProd s w d) r = s * 2 ^ (w * (d - 1))` for all `r` when `2 ≤ w, 1 ≤ d`).
  - **Theorem C (`hybridElim_size_ge_kappaConj`)**:
    For any exact hybrid elimination state `HybridElimState n r Φ` and any projection-cylindrical
    component `Cstar`, the CNF component satisfies `kappaConj (projOn Cstar emb Φ) r ≤ S.F.card`.
* **Tier 2 (Standard proof-complexity context, not formalized here)**:
  - Connections to `Res(⊕)` / Gaussian-augmented CDCL heuristics on structured benchmarks.
* **Tier 3–6 (Explicitly NOT claimed)**:
  - General DAG `Res(⊕)` lower bounds remain open and are NOT proved here.
  - Extension variables (Extended Resolution / Extended Frege) are forbidden in this representation model.
  - No claim of `P ≠ NP` or `NP ≠ coNP` is made.
-/

namespace Mathmatica.HybridBasisCover

open scoped BigOperators Classical
open Matrix

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ### Section 1: Core Definitions over `Fin k → ZMod 2` -/

/-- A Boolean literal over `Fin k → ZMod 2`, asserting `x var = val`. -/
structure CNFLit (k : ℕ) where
  var : Fin k
  val : ZMod 2
  deriving DecidableEq

/-- A CNF clause is a finite set of literals with disjunctive semantics. -/
abbrev CNFClause (k : ℕ) := Finset (CNFLit k)

/-- Disjunctive satisfaction semantics of a CNF clause. -/
def satClause {k : ℕ} (C : CNFClause k) (x : Fin k → ZMod 2) : Prop :=
  ∃ l ∈ C, x l.var = l.val

/-- The falsifying set (subcube) of a CNF clause. -/
def falsifiesClause {k : ℕ} (C : CNFClause k) : Set (Fin k → ZMod 2) :=
  {x | ¬ satClause C x}

/-- The set of variable indices appearing in a CNF clause. -/
def clauseVars {k : ℕ} (C : CNFClause k) : Finset (Fin k) :=
  C.image CNFLit.var

/-- An affine `F₂`-linear equation `dotProduct a x = b`. -/
structure F2Eq (k : ℕ) where
  a : Fin k → ZMod 2
  b : ZMod 2
  deriving DecidableEq

/-- Satisfaction semantics of an affine `F₂`-linear equation. -/
def satEq {k : ℕ} (e : F2Eq k) (x : Fin k → ZMod 2) : Prop :=
  dotProduct e.a x = e.b

/-- A disjunctive `F₂`-linear clause (finite set of affine equations). -/
abbrev F2LinClause (k : ℕ) := Finset (F2Eq k)

/-- Disjunctive satisfaction semantics of an `F₂`-linear clause. -/
def satLinClause {k : ℕ} (L : F2LinClause k) (x : Fin k → ZMod 2) : Prop :=
  ∃ e ∈ L, satEq e x

/-- A valid conjunctive hybrid cover of `R` with at most `r` linear equations `H` and CNF `Ψ`. -/
def IsConjCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ)
    (H : Finset (F2Eq k)) (Ψ : Finset (CNFClause k)) : Prop :=
  H.card ≤ r ∧ ∀ x, x ∈ R ↔ (∀ e ∈ H, satEq e x) ∧ (∀ C ∈ Ψ, satClause C x)

/-- A valid disjunctive linear-clause hybrid cover of `R` with at most `r` linear clauses `Ψ_lin`
and CNF `Ψ_cnf`. -/
def IsLinCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ)
    (Ψ_lin : Finset (F2LinClause k)) (Ψ_cnf : Finset (CNFClause k)) : Prop :=
  Ψ_lin.card ≤ r ∧ ∀ x, x ∈ R ↔ (∀ L ∈ Ψ_lin, satLinClause L x) ∧ (∀ C ∈ Ψ_cnf, satClause C x)

/-! #### Basic `ZMod 2` arithmetic helpers -/

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma zmod2_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert a b h; decide

lemma zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a; decide

lemma zmod2_eq_or_eq (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma zmod2_neg (a : ZMod 2) : -a = a := by
  revert a; decide

lemma zmod2_sub (a b : ZMod 2) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_neg]

lemma card_filter_add_card_filter_not_univ {α : Type*} [Fintype α] (p : α → Prop) :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun x => ¬ p x)).card = Fintype.card α := by
  have hdisj : Disjoint (Finset.univ.filter p) (Finset.univ.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2; exact h2 h1
  have hunion : Finset.univ.filter p ∪ Finset.univ.filter (fun x => ¬ p x) = Finset.univ := by
    ext x
    simp [em]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

/-! #### Trivial point-blocking CNF clauses and cover complexity definitions -/

/-- The full-width CNF clause falsified solely by the assignment `y`. -/
def pointClause {k : ℕ} (y : Fin k → ZMod 2) : CNFClause k :=
  Finset.univ.image (fun i => ⟨i, y i + 1⟩)

lemma satClause_pointClause {k : ℕ} (y x : Fin k → ZMod 2) :
    satClause (pointClause y) x ↔ x ≠ y := by
  constructor
  · rintro ⟨l, hl, hxl⟩ hxy
    rcases Finset.mem_image.mp hl with ⟨i, _, rfl⟩
    subst hxy
    exact zmod2_ne_add_one (x i) hxl
  · intro hne
    have : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    rcases this with ⟨i, hi⟩
    refine ⟨⟨i, y i + 1⟩, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    exact zmod2_eq_add_one_of_ne hi

lemma exists_isConjCover_of_compl {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    ∃ H Ψ, IsConjCover R r H Ψ ∧
      Ψ.card ≤ (Finset.univ.filter (fun y => y ∉ R)).card := by
  let S := Finset.univ.filter (fun y : Fin k → ZMod 2 => y ∉ R)
  refine ⟨∅, S.image pointClause, ⟨Nat.zero_le r, ?_⟩, Finset.card_image_le⟩
  intro x
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satClause_pointClause, S, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx y hy hxy
    exact hy (hxy ▸ hx)
  · intro h
    by_contra hx
    exact h x hx rfl

lemma exists_isConjCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    ∃ H Ψ, IsConjCover R r H Ψ ∧ Ψ.card ≤ 2 ^ k := by
  classical
  rcases exists_isConjCover_of_compl R r with ⟨H, Ψ, hcov, hcard⟩
  refine ⟨H, Ψ, hcov, le_trans hcard ?_⟩
  calc
    (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin k → ZMod 2)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ k := by simp [Fintype.card_pi, ZMod.card]

lemma IsConjCover.to_isLinCover {k : ℕ} {R : Set (Fin k → ZMod 2)} {r : ℕ}
    {H : Finset (F2Eq k)} {Ψ : Finset (CNFClause k)} (h : IsConjCover R r H Ψ) :
    IsLinCover R r (H.image (fun e => ({e} : F2LinClause k))) Ψ := by
  refine ⟨le_trans Finset.card_image_le h.1, fun x => ?_⟩
  rw [h.2 x]
  constructor <;> rintro ⟨hH, hΨ⟩ <;> refine ⟨?_, hΨ⟩
  · intro L hL
    rcases Finset.mem_image.mp hL with ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_singleton_self e, hH e he⟩
  · intro e he
    rcases hH {e} (Finset.mem_image.mpr ⟨e, he, rfl⟩) with ⟨e', he', hsat⟩
    rw [Finset.mem_singleton.mp he'] at hsat
    exact hsat

lemma exists_isLinCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    ∃ Ψ_lin Ψ_cnf, IsLinCover R r Ψ_lin Ψ_cnf ∧ Ψ_cnf.card ≤ 2 ^ k := by
  rcases exists_isConjCover R r with ⟨H, Ψ, hcov, hcard⟩
  exact ⟨_, Ψ, hcov.to_isLinCover, hcard⟩

/-- Minimum CNF clause count in a conjunctive hybrid cover of `R` with at most `r` linear equations. -/
noncomputable def kappaConj {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ H Ψ, IsConjCover R r H Ψ ∧ Ψ.card = m}

/-- Minimum CNF clause count in a disjunctive linear-clause hybrid cover of `R` with at most `r`
linear clauses. -/
noncomputable def kappaLin {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ Ψ_lin Ψ_cnf, IsLinCover R r Ψ_lin Ψ_cnf ∧ Ψ_cnf.card = m}

/-- Pure CNF clause cover complexity (`r = 0`). -/
noncomputable def kappa0 {k : ℕ} (R : Set (Fin k → ZMod 2)) : ℕ :=
  kappaConj R 0

lemma kappaConj_le_card {k : ℕ} {R : Set (Fin k → ZMod 2)} {r : ℕ}
    {H : Finset (F2Eq k)} {Ψ : Finset (CNFClause k)} (h : IsConjCover R r H Ψ) :
    kappaConj R r ≤ Ψ.card :=
  Nat.sInf_le ⟨H, Ψ, h, rfl⟩

lemma kappaLin_le_card {k : ℕ} {R : Set (Fin k → ZMod 2)} {r : ℕ}
    {Ψ_lin : Finset (F2LinClause k)} {Ψ_cnf : Finset (CNFClause k)}
    (h : IsLinCover R r Ψ_lin Ψ_cnf) :
    kappaLin R r ≤ Ψ_cnf.card :=
  Nat.sInf_le ⟨Ψ_lin, Ψ_cnf, h, rfl⟩

lemma exists_min_conjCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    ∃ H Ψ, IsConjCover R r H Ψ ∧ Ψ.card = kappaConj R r := by
  have hne : {m : ℕ | ∃ H Ψ, IsConjCover R r H Ψ ∧ Ψ.card = m}.Nonempty := by
    rcases exists_isConjCover R r with ⟨H, Ψ, hcov, _⟩
    exact ⟨Ψ.card, H, Ψ, hcov, rfl⟩
  exact Nat.sInf_mem hne

lemma exists_min_linCover {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    ∃ Ψ_lin Ψ_cnf, IsLinCover R r Ψ_lin Ψ_cnf ∧ Ψ_cnf.card = kappaLin R r := by
  have hne : {m : ℕ | ∃ Ψ_lin Ψ_cnf, IsLinCover R r Ψ_lin Ψ_cnf ∧ Ψ_cnf.card = m}.Nonempty := by
    rcases exists_isLinCover R r with ⟨Ψ_lin, Ψ_cnf, hcov, _⟩
    exact ⟨Ψ_cnf.card, Ψ_lin, Ψ_cnf, hcov, rfl⟩
  exact Nat.sInf_mem hne

lemma kappaLin_le_kappaConj {k : ℕ} (R : Set (Fin k → ZMod 2)) (r : ℕ) :
    kappaLin R r ≤ kappaConj R r := by
  rcases exists_min_conjCover R r with ⟨H, Ψ, hcov, hcard⟩
  rw [← hcard]
  exact kappaLin_le_card hcov.to_isLinCover

lemma kappaLin_zero_eq_kappaConj_zero {k : ℕ} (R : Set (Fin k → ZMod 2)) :
    kappaLin R 0 = kappaConj R 0 := by
  apply le_antisymm (kappaLin_le_kappaConj R 0)
  rcases exists_min_linCover R 0 with ⟨Ψ_lin, Ψ_cnf, hcov, hcard⟩
  have hEmpty : Ψ_lin = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcov.1)
  rw [← hcard]
  apply kappaConj_le_card (H := ∅)
  refine ⟨le_refl 0, fun x => ?_⟩
  simpa [hEmpty] using hcov.2 x

lemma kappaConj_antitone {k : ℕ} (R : Set (Fin k → ZMod 2)) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    kappaConj R r₂ ≤ kappaConj R r₁ := by
  rcases exists_min_conjCover R r₁ with ⟨H, Ψ, hcov, hcard⟩
  rw [← hcard]
  exact kappaConj_le_card ⟨le_trans hcov.1 h, hcov.2⟩

lemma kappaLin_antitone {k : ℕ} (R : Set (Fin k → ZMod 2)) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    kappaLin R r₂ ≤ kappaLin R r₁ := by
  rcases exists_min_linCover R r₁ with ⟨Ψ_lin, Ψ_cnf, hcov, hcard⟩
  rw [← hcard]
  exact kappaLin_le_card ⟨le_trans hcov.1 h, hcov.2⟩

/-! ### Section 2: `F₂`-Linear Algebra, Singleton Bound, and Theorem A -/

/-- The orthogonal complement of a subspace `U ≤ (Fin k → ZMod 2)` under the standard dot product. -/
def orthComp {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Submodule (ZMod 2) (Fin k → ZMod 2) where
  carrier := {x | ∀ w ∈ U, dotProduct w x = 0}
  zero_mem' := fun w _ => dotProduct_zero w
  add_mem' := fun hx hy w hw => by rw [dotProduct_add, hx w hw, hy w hw, add_zero]
  smul_mem' := fun c x hx w hw => by rw [dotProduct_smul, hx w hw, smul_zero]

lemma mem_orthComp {k : ℕ} {U : Submodule (ZMod 2) (Fin k → ZMod 2)} {x : Fin k → ZMod 2} :
    x ∈ orthComp U ↔ ∀ w ∈ U, dotProduct w x = 0 :=
  Iff.rfl

lemma le_orthComp_orthComp {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    U ≤ orthComp (orthComp U) := by
  intro w hw x hx
  rw [dotProduct_comm]
  exact hx w hw

lemma orthComp_antitone {k : ℕ} {U V : Submodule (ZMod 2) (Fin k → ZMod 2)} (h : U ≤ V) :
    orthComp V ≤ orthComp U :=
  fun _ hx w hw => hx w (h hw)

lemma orthComp_sup {k : ℕ} (U V : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    orthComp (U ⊔ V) = orthComp U ⊓ orthComp V := by
  ext x
  simp only [Submodule.mem_inf, mem_orthComp]
  constructor
  · intro hx
    exact ⟨fun w hw => hx w (Submodule.mem_sup_left hw),
           fun w hw => hx w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨hxU, hxV⟩ w hw
    rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
    rw [add_dotProduct, hxU u hu, hxV v hv, add_zero]

/-- The restriction-pairing linear map from `Fin k → ZMod 2` to `Module.Dual (ZMod 2) U`. -/
def dotDualMap {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) U where
  toFun x :=
    { toFun := fun w => dotProduct w.1 x
      map_add' := fun u v => add_dotProduct u.1 v.1 x
      map_smul' := fun c u => smul_dotProduct c u.1 x }
  map_add' x y := by ext w; exact dotProduct_add w.1 x y
  map_smul' c x := by ext w; exact dotProduct_smul c w.1 x

lemma ker_dotDualMap {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    LinearMap.ker (dotDualMap U) = orthComp U := by
  ext x
  simp only [LinearMap.mem_ker, mem_orthComp]
  constructor
  · intro hx w hw
    exact congrArg (fun f => f ⟨w, hw⟩) hx
  · intro hx
    ext ⟨w, hw⟩
    exact hx w hw

lemma range_dotDualMap {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    LinearMap.range (dotDualMap U) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  -- Extend `f : U →ₗ[ZMod 2] ZMod 2` to `Fin k → ZMod 2` via a complement of `U`.
  rcases Submodule.exists_isCompl U with ⟨W, hUW⟩
  let g : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    f.comp (Submodule.projectionOnto U W hUW)
  refine ⟨fun i => g (Pi.single i 1), ?_⟩
  ext ⟨w, hw⟩
  change dotProduct w (fun i => g (Pi.single i 1)) = f ⟨w, hw⟩
  have hdecomp : w = ∑ i : Fin k, w i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  have hgw : g w = f ⟨w, hw⟩ := by
    change f (Submodule.projectionOnto U W hUW (⟨w, hw⟩ : U).1) = f ⟨w, hw⟩
    rw [Submodule.projectionOnto_apply_left hUW ⟨w, hw⟩]
  rw [← hgw]
  conv_rhs => rw [hdecomp]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]

lemma finrank_orthComp_add_finrank {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Module.finrank (ZMod 2) (orthComp U) + Module.finrank (ZMod 2) U = k := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotDualMap U)
  rw [range_dotDualMap, finrank_top, Subspace.dual_finrank_eq, ker_dotDualMap,
      Module.finrank_fin_fun] at h
  omega

lemma orthComp_orthComp {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    orthComp (orthComp U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orthComp_orthComp U)
  have h1 := finrank_orthComp_add_finrank U
  have h2 := finrank_orthComp_add_finrank (orthComp U)
  omega

lemma orthComp_inf {k : ℕ} (U V : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    orthComp (U ⊓ V) = orthComp U ⊔ orthComp V := by
  have h := orthComp_sup (orthComp U) (orthComp V)
  rw [orthComp_orthComp, orthComp_orthComp] at h
  rw [← h, orthComp_orthComp]

lemma card_submodule_eq_pow_finrank {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
  let b := Module.finBasis (ZMod 2) U
  rw [Fintype.card_congr b.equivFun.toEquiv]
  simp [Fintype.card_pi, ZMod.card]

/-- Hamming weight of a binary vector `w : Fin k → ZMod 2`. -/
def hammingWeight {k : ℕ} (w : Fin k → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => w i ≠ 0)).card

/-- Subspace of vectors supported on `S : Finset (Fin k)`. -/
def supportedOn {k : ℕ} (S : Finset (Fin k)) : Submodule (ZMod 2) (Fin k → ZMod 2) where
  carrier := {w | ∀ i, i ∉ S → w i = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hx hy i hi => by simp [hx i hi, hy i hi]
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

lemma mem_supportedOn {k : ℕ} {S : Finset (Fin k)} {w : Fin k → ZMod 2} :
    w ∈ supportedOn S ↔ ∀ i, i ∉ S → w i = 0 :=
  Iff.rfl

lemma mem_orthComp_supportedOn {k : ℕ} {S : Finset (Fin k)} {z : Fin k → ZMod 2} :
    z ∈ orthComp (supportedOn S) ↔ ∀ i ∈ S, z i = 0 := by
  constructor
  · intro hz i hi
    have hmem : Pi.single i (1 : ZMod 2) ∈ supportedOn S := by
      intro j hj
      exact Pi.single_eq_of_ne (by rintro rfl; exact hj hi) _
    have hdot := hz (Pi.single i 1) hmem
    simpa [dotProduct, Pi.single_apply] using hdot
  · intro hz w hw
    unfold dotProduct
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S
    · simp [hz i hi]
    · simp [hw i hi]

lemma finrank_supportedOn {k : ℕ} (S : Finset (Fin k)) :
    Module.finrank (ZMod 2) (supportedOn S) = S.card := by
  let e : supportedOn S ≃ₗ[ZMod 2] (S → ZMod 2) :=
    { toFun := fun w i => w.1 i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => ⟨fun i => if h : i ∈ S then f ⟨i, h⟩ else 0,
        fun i hi => by simp [hi]⟩
      left_inv := fun ⟨w, hw⟩ => by
        ext i
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi, hw i hi]
      right_inv := fun f => by
        ext ⟨i, hi⟩
        simp [hi] }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- Singleton bound for a nonzero linear code `V ≤ supportedOn S` of minimum Hamming weight `≥ d_min`. -/
lemma singleton_bound {k d_min : ℕ} {S : Finset (Fin k)}
    {V : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (hV_supp : V ≤ supportedOn S)
    (hV_ne : V ≠ ⊥)
    (hdist : ∀ w ∈ V, w ≠ 0 → d_min ≤ hammingWeight w) :
    Module.finrank (ZMod 2) V + d_min ≤ S.card + 1 := by
  -- First obtain `d_min ≤ S.card` from any nonzero codeword in `V`.
  have hd_le_S : d_min ≤ S.card := by
    have : ∃ w ∈ V, w ≠ (0 : Fin k → ZMod 2) := by
      by_contra h
      push Not at h
      apply hV_ne
      rw [Submodule.eq_bot_iff]
      exact h
    rcases this with ⟨w, hwV, hw0⟩
    calc d_min ≤ hammingWeight w := hdist w hwV hw0
      _ ≤ S.card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        by_contra hiS
        exact hi.2 (hV_supp hwV i hiS)
  by_cases hd0 : d_min = 0
  · subst hd0
    have hle := Submodule.finrank_mono hV_supp
    rw [finrank_supportedOn] at hle
    omega
  · -- Pick `T ⊆ S` with `T.card = d_min - 1`; projection onto `S \ T` is injective on `V`.
    have hT_le : d_min - 1 ≤ S.card := by omega
    rcases Finset.exists_subset_card_eq hT_le with ⟨T, hTS, hTcard⟩
    let π : V →ₗ[ZMod 2] ((S \ T : Finset (Fin k)) → ZMod 2) :=
      { toFun := fun v i => v.1 i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hπ_inj : Function.Injective π := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      by_contra hv0
      have hv1_ne : v.1 ≠ 0 := fun h => hv0 (Subtype.ext h)
      have hwt_le : hammingWeight v.1 ≤ T.card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        have hiS : i ∈ S := by
          by_contra hiS
          exact hi.2 (hV_supp v.2 i hiS)
        by_contra hiT
        have hiST : i ∈ S \ T := Finset.mem_sdiff.mpr ⟨hiS, hiT⟩
        have hzero : v.1 i = 0 := congrFun hv ⟨i, hiST⟩
        exact hi.2 hzero
      have hdist_v := hdist v.1 v.2 hv1_ne
      omega
    have hrank := LinearMap.finrank_le_finrank_of_injective hπ_inj
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
        Finset.card_sdiff, Finset.inter_eq_left.mpr hTS, hTcard] at hrank
    omega

/-- Helper: if `x₀` falsifies `C`, then `y` falsifies `C` iff `y - x₀ ∈ orthComp (supportedOn (clauseVars C))`. -/
lemma mem_falsifiesClause_iff {k : ℕ} {C : CNFClause k} {x₀ y : Fin k → ZMod 2}
    (hx₀ : x₀ ∈ falsifiesClause C) :
    y ∈ falsifiesClause C ↔ y - x₀ ∈ orthComp (supportedOn (clauseVars C)) := by
  rw [mem_orthComp_supportedOn]
  simp only [falsifiesClause, Set.mem_ofPred_eq, satClause, not_exists, not_and] at hx₀ ⊢
  constructor
  · intro hy i hi
    rcases Finset.mem_image.mp hi with ⟨l, hl, rfl⟩
    have h1 := zmod2_eq_add_one_of_ne (hy l hl)
    have h2 := zmod2_eq_add_one_of_ne (hx₀ l hl)
    simp [Pi.sub_apply, h1, h2]
  · intro hsub l hl
    have hi : l.var ∈ clauseVars C := Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have heq : y l.var = x₀ l.var := sub_eq_zero.mp (hsub l.var hi)
    rw [heq]
    exact hx₀ l hl

/-- Cardinality of a nonempty coset of a subspace `U ≤ (Fin k → ZMod 2)`. -/
lemma card_coset_eq {k : ℕ} (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (x₀ : Fin k → ZMod 2) :
    (Finset.univ.filter (fun y : Fin k → ZMod 2 => y - x₀ ∈ U)).card =
      2 ^ Module.finrank (ZMod 2) U := by
  classical
  have hcard :
      (Finset.univ.filter (fun y : Fin k → ZMod 2 => y - x₀ ∈ U)).card =
      (Finset.univ.filter (fun z : Fin k → ZMod 2 => z ∈ U)).card := by
    apply Finset.card_bij (fun y _ => y - x₀)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy
    · intro y₁ _ y₂ _ h
      exact sub_left_inj.mp h
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact ⟨z + x₀, by simp [hz], add_sub_cancel_right z x₀⟩
  rw [hcard, ← card_submodule_eq_pow_finrank U]
  rw [Fintype.card_of_subtype (Finset.univ.filter (fun z : Fin k → ZMod 2 => z ∈ U))]
  intro z
  simp

/-- **Theorem A (Dual-Distance XOR-Budget Plateau)**:
Let `C_perp ≤ (Fin k → ZMod 2)` be a linear code of dimension `m = finrank C_perp` and minimum
nonzero Hamming weight `≥ d_min`, and let `R = orthComp C_perp`. Then for every `r < m`,
`2 ^ d_min * (2 ^ (m - r) - 1) ≤ 2 ^ (m - r) * kappaConj R r`. -/
theorem kappaConj_linear_code_plateau {k d_min : ℕ}
    (C_perp : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hdist : ∀ w ∈ C_perp, w ≠ 0 → d_min ≤ hammingWeight w)
    {r : ℕ} (hr : r < Module.finrank (ZMod 2) C_perp) :
    let m := Module.finrank (ZMod 2) C_perp
    let R : Set (Fin k → ZMod 2) := (orthComp C_perp : Set (Fin k → ZMod 2))
    2 ^ d_min * (2 ^ (m - r) - 1) ≤ 2 ^ (m - r) * kappaConj R r := by
  classical
  intro m R
  rcases exists_min_conjCover R r with ⟨H, Ψ, hcov, hcard_eq⟩
  rw [← hcard_eq]
  -- Every `e ∈ H` must vanish on `0 ∈ R`, so `e.b = 0` and `e.a ∈ C_perp`.
  have h0R : (0 : Fin k → ZMod 2) ∈ R := (orthComp C_perp).zero_mem
  have hHb : ∀ e ∈ H, e.b = 0 := by
    intro e he
    have hsat := ((hcov.2 0).mp h0R).1 e he
    unfold satEq at hsat
    rw [dotProduct_zero] at hsat
    exact hsat.symm
  have hHa : ∀ e ∈ H, e.a ∈ C_perp := by
    intro e he
    rw [← orthComp_orthComp C_perp, mem_orthComp]
    intro x hx
    rw [dotProduct_comm]
    have hsat := ((hcov.2 x).mp hx).1 e he
    rw [satEq, hHb e he] at hsat
    exact hsat
  let B_span : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    Submodule.span (ZMod 2) ((H.image F2Eq.a : Finset (Fin k → ZMod 2)) : Set (Fin k → ZMod 2))
  have hB_le : B_span ≤ C_perp := by
    rw [Submodule.span_le]
    rintro v hv
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨e, he, rfl⟩
    exact hHa e he
  let r' := Module.finrank (ZMod 2) B_span
  have hr'_le_r : r' ≤ r := by
    have hfin : r' ≤ (H.image F2Eq.a).card := by
      let S := H.image F2Eq.a
      let φ : (S → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
        { toFun := fun c => ∑ v : S, c v • v.1
          map_add' := fun c₁ c₂ => by simp [add_smul, Finset.sum_add_distrib]
          map_smul' := fun a c => by simp [Finset.smul_sum, mul_smul] }
      have hrange : B_span ≤ LinearMap.range φ := by
        rw [Submodule.span_le]
        intro v hv
        have hvS : v ∈ S := Finset.mem_coe.mp hv
        refine ⟨fun w : S => if w = ⟨v, hvS⟩ then (1 : ZMod 2) else 0, ?_⟩
        change ∑ w : S, (if w = ⟨v, hvS⟩ then (1 : ZMod 2) else 0) • w.1 = v
        rw [Finset.sum_eq_single ⟨v, hvS⟩]
        · simp
        · intro w _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      calc r' ≤ Module.finrank (ZMod 2) (LinearMap.range φ) := Submodule.finrank_mono hrange
        _ ≤ Module.finrank (ZMod 2) (S → ZMod 2) := by
            have := LinearMap.finrank_range_add_finrank_ker φ
            omega
        _ = S.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    calc r' ≤ (H.image F2Eq.a).card := hfin
      _ ≤ H.card := Finset.card_image_le
      _ ≤ r := hcov.1
  have hr'_lt_m : r' < m := lt_of_le_of_lt hr'_le_r hr
  have hm_le_k : m ≤ k := by
    have := finrank_orthComp_add_finrank C_perp
    omega
  -- `H_set` is exactly `orthComp B_span`.
  have hH_iff : ∀ x, (∀ e ∈ H, satEq e x) ↔ x ∈ orthComp B_span := by
    intro x
    constructor
    · intro hx
      rw [mem_orthComp]
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · intro v hv
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨e, he, rfl⟩
        have hsat := hx e he
        rw [satEq, hHb e he] at hsat
        exact hsat
      · exact zero_dotProduct x
      · intro u v _ _ hu hv; rw [add_dotProduct, hu, hv, add_zero]
      · intro c u _ hu; rw [smul_dotProduct, hu, smul_zero]
    · intro hx e he
      rw [satEq, hHb e he]
      apply hx e.a
      exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  -- Key per-clause bound: for every `C ∈ Ψ`, `2 ^ d_min * |F_C ∩ orthComp B_span| ≤ 2 ^ (k - r')`.
  have hclause_bound : ∀ C ∈ Ψ,
      2 ^ d_min * (Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span)).card
        ≤ 2 ^ (k - r') := by
    intro C hC
    by_cases hne : ∃ x₀, x₀ ∈ falsifiesClause C ∧ x₀ ∈ orthComp B_span
    · rcases hne with ⟨x₀, hx₀F, hx₀B⟩
      let S := clauseVars C
      -- `y ∈ F_C ∧ y ∈ orthComp B_span` iff `y - x₀ ∈ orthComp (supportedOn S ⊔ B_span)`.
      have hfilter_eq :
          Finset.univ.filter (fun y : Fin k → ZMod 2 => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span) =
          Finset.univ.filter (fun y : Fin k → ZMod 2 => y - x₀ ∈ orthComp (supportedOn S ⊔ B_span)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, orthComp_sup, Submodule.mem_inf]
        rw [mem_falsifiesClause_iff hx₀F]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (orthComp B_span).sub_mem h2 hx₀B⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (orthComp B_span).add_mem h2 hx₀B
          simpa using this
      rw [hfilter_eq, card_coset_eq]
      -- Show `supportedOn S ⊓ B_span < supportedOn S ⊓ C_perp`.
      have hstrict : supportedOn S ⊓ B_span < supportedOn S ⊓ C_perp := by
        refine lt_of_le_of_ne (inf_le_inf_left _ hB_le) ?_
        intro heq
        have hx₀_in : x₀ ∈ orthComp (supportedOn S ⊓ C_perp) := by
          rw [← heq]
          exact orthComp_antitone inf_le_right hx₀B
        rw [orthComp_inf] at hx₀_in
        rcases Submodule.mem_sup.mp hx₀_in with ⟨u, hu, v, hv, huv⟩
        -- Then `v ∈ R` and `v - x₀ = -u ∈ orthComp (supportedOn S)`, so `v ∈ falsifiesClause C`!
        have hvF : v ∈ falsifiesClause C := by
          rw [mem_falsifiesClause_iff hx₀F]
          have hsub : v - x₀ = -u := by
            rw [← huv]; abel
          rw [hsub]
          exact (orthComp (supportedOn S)).neg_mem hu
        have hvC : satClause C v := ((hcov.2 v).mp hv).2 C hC
        exact hvF hvC
      have hlt_rank := Submodule.finrank_lt_finrank_of_lt hstrict
      have hV_ne : supportedOn S ⊓ C_perp ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hlt_rank
        omega
      have hsing := singleton_bound (d_min := d_min) (S := S) (V := supportedOn S ⊓ C_perp)
        inf_le_left hV_ne (fun w hw hw0 => hdist w hw.2 hw0)
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq (supportedOn S) B_span
      rw [finrank_supportedOn] at hmod
      have hsum_rk := finrank_orthComp_add_finrank (supportedOn S ⊔ B_span)
      have hpow_le : d_min + Module.finrank (ZMod 2) (orthComp (supportedOn S ⊔ B_span)) ≤ k - r' := by
        omega
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) hpow_le
    · push Not at hne
      have hempty :
          Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y _ h
        exact hne y h.1 h.2
      rw [hempty, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
  -- Cover `orthComp B_span \ orthComp C_perp` by `⋃ C ∈ Ψ, (F_C ∩ orthComp B_span)`.
  let A_B := Finset.univ.filter (fun y : Fin k → ZMod 2 => y ∈ orthComp B_span)
  let A_C := Finset.univ.filter (fun y : Fin k → ZMod 2 => y ∈ orthComp C_perp)
  have hAC_sub_AB : A_C ⊆ A_B := by
    intro y hy
    simp only [A_C, A_B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact orthComp_antitone hB_le hy
  have hdiff_sub :
      A_B \ A_C ⊆ Ψ.biUnion (fun C => Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span)) := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    simp only [A_B, A_C, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hyH : ∀ e ∈ H, satEq e y := (hH_iff y).mpr hy.1
    have hy_not_all : ¬ ∀ C ∈ Ψ, satClause C y := by
      intro hall
      exact hy.2 ((hcov.2 y).mpr ⟨hyH, hall⟩)
    push Not at hy_not_all
    rcases hy_not_all with ⟨C, hC, hnotC⟩
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hnotC, hy.1⟩⟩
  have hcard_AB : A_B.card = 2 ^ (k - r') := by
    have h1 : A_B.card = Fintype.card (orthComp B_span) := by
      rw [Fintype.card_of_subtype A_B (by intro y; simp [A_B])]
    rw [h1, card_submodule_eq_pow_finrank]
    have h2 := finrank_orthComp_add_finrank B_span
    congr 1; omega
  have hcard_AC : A_C.card = 2 ^ (k - m) := by
    have h1 : A_C.card = Fintype.card (orthComp C_perp) := by
      rw [Fintype.card_of_subtype A_C (by intro y; simp [A_C])]
    rw [h1, card_submodule_eq_pow_finrank]
    have h2 := finrank_orthComp_add_finrank C_perp
    congr 1; omega
  have hdiff_le : (A_B \ A_C).card ≤
      ∑ C ∈ Ψ, (Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span)).card :=
    le_trans (Finset.card_le_card hdiff_sub) Finset.card_biUnion_le
  have hmul : 2 ^ d_min * (2 ^ (k - r') - 2 ^ (k - m)) ≤ Ψ.card * 2 ^ (k - r') := by
    calc 2 ^ d_min * (2 ^ (k - r') - 2 ^ (k - m))
        = 2 ^ d_min * (A_B \ A_C).card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAC_sub_AB, hcard_AB, hcard_AC]
      _ ≤ 2 ^ d_min * ∑ C ∈ Ψ, (Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span)).card :=
          Nat.mul_le_mul_left _ hdiff_le
      _ = ∑ C ∈ Ψ, 2 ^ d_min * (Finset.univ.filter (fun y => y ∈ falsifiesClause C ∧ y ∈ orthComp B_span)).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _C ∈ Ψ, 2 ^ (k - r') := Finset.sum_le_sum (fun C hC => hclause_bound C hC)
      _ = Ψ.card * 2 ^ (k - r') := by simp
  -- Factor out `2 ^ (k - m)` and apply monotonicity in `r' ≤ r < m`.
  have hpow_split : 2 ^ (k - r') = 2 ^ (k - m) * 2 ^ (m - r') := by
    rw [← Nat.pow_add]; congr 1; omega
  have h1 : 2 ^ d_min * (2 ^ (m - r') - 1) ≤ 2 ^ (m - r') * Ψ.card := by
    have hpos : 0 < 2 ^ (k - m) := Nat.pos_of_ne_zero (by positivity)
    apply Nat.le_of_mul_le_mul_left _ hpos
    have hlhs : 2 ^ (k - m) * (2 ^ d_min * (2 ^ (m - r') - 1)) =
        2 ^ d_min * (2 ^ (k - r') - 2 ^ (k - m)) := by
      rw [hpow_split, Nat.mul_sub_left_distrib, mul_one,
          Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      congr 1 <;> ring
    have hrhs : 2 ^ (k - m) * (2 ^ (m - r') * Ψ.card) = Ψ.card * 2 ^ (k - r') := by
      rw [hpow_split]; ring
    rw [hlhs, hrhs]
    exact hmul
  -- Monotonicity: `(2 ^ (m - r) - 1) * 2 ^ (m - r') ≤ (2 ^ (m - r') - 1) * 2 ^ (m - r)`.
  have hmono : (2 ^ (m - r) - 1) * 2 ^ (m - r') ≤ (2 ^ (m - r') - 1) * 2 ^ (m - r) := by
    have hle : 2 ^ (m - r) ≤ 2 ^ (m - r') := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos1 : 1 ≤ 2 ^ (m - r) := Nat.one_le_pow _ _ (by decide)
    have hpos2 : 1 ≤ 2 ^ (m - r') := Nat.one_le_pow _ _ (by decide)
    zify [hpos1, hpos2]
    nlinarith
  have hpos' : 0 < 2 ^ (m - r') := Nat.pos_of_ne_zero (by positivity)
  apply Nat.le_of_mul_le_mul_right _ hpos'
  calc 2 ^ d_min * (2 ^ (m - r) - 1) * 2 ^ (m - r')
      = 2 ^ d_min * ((2 ^ (m - r) - 1) * 2 ^ (m - r')) := by ring
    _ ≤ 2 ^ d_min * ((2 ^ (m - r') - 1) * 2 ^ (m - r)) := Nat.mul_le_mul_left _ hmono
    _ = 2 ^ (m - r) * (2 ^ d_min * (2 ^ (m - r') - 1)) := by ring
    _ ≤ 2 ^ (m - r) * (2 ^ (m - r') * Ψ.card) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (m - r) * Ψ.card * 2 ^ (m - r') := by ring

/-- Corollary of Theorem A: for `1 ≤ d_min` and `r < m`, `2 ^ (d_min - 1) ≤ kappaConj R r`. -/
theorem kappaConj_linear_code_plateau_cor {k d_min : ℕ}
    (C_perp : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hdist : ∀ w ∈ C_perp, w ≠ 0 → d_min ≤ hammingWeight w)
    (hd : 1 ≤ d_min)
    {r : ℕ} (hr : r < Module.finrank (ZMod 2) C_perp) :
    2 ^ (d_min - 1) ≤ kappaConj (orthComp C_perp : Set (Fin k → ZMod 2)) r := by
  let m := Module.finrank (ZMod 2) C_perp
  have hmain := kappaConj_linear_code_plateau C_perp hdist hr
  have hge2 : 2 ≤ 2 ^ (m - r) := by
    have h1 : 1 ≤ m - r := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - r) := Nat.pow_le_pow_right (by decide) h1
  have hstep : 2 ^ (m - r) ≤ 2 * (2 ^ (m - r) - 1) := by omega
  have hpow : 2 ^ d_min = 2 ^ (d_min - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, Nat.pow_succ]
  have hpos : 0 < 2 ^ (m - r) := Nat.pos_of_ne_zero (by positivity)
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc 2 ^ (m - r) * 2 ^ (d_min - 1)
      = 2 ^ (d_min - 1) * 2 ^ (m - r) := by ring
    _ ≤ 2 ^ (d_min - 1) * (2 * (2 ^ (m - r) - 1)) := Nat.mul_le_mul_left _ hstep
    _ = 2 ^ d_min * (2 ^ (m - r) - 1) := by rw [hpow]; ring
    _ ≤ 2 ^ (m - r) * kappaConj (orthComp C_perp : Set (Fin k → ZMod 2)) r := hmain

/-- Theorem A (threshold collapse): at budget `r = finrank C_perp`, `kappaConj (orthComp C_perp) m = 0`. -/
theorem kappaConj_linear_code_at_rank {k : ℕ}
    (C_perp : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    kappaConj (orthComp C_perp : Set (Fin k → ZMod 2)) (Module.finrank (ZMod 2) C_perp) = 0 := by
  classical
  let m := Module.finrank (ZMod 2) C_perp
  let b := Module.finBasis (ZMod 2) C_perp
  let H : Finset (F2Eq k) := Finset.univ.image (fun j : Fin m => ⟨(b j).1, 0⟩)
  have hcov : IsConjCover (orthComp C_perp : Set (Fin k → ZMod 2)) m H ∅ := by
    refine ⟨le_trans Finset.card_image_le (by simp [m]), fun x => ?_⟩
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
      SetLike.mem_coe, mem_orthComp, H, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, satEq]
    constructor
    · intro hx j
      exact hx (b j).1 (b j).2
    · intro hx w hw
      have hdecomp := b.sum_repr ⟨w, hw⟩
      have hw_eq : w = ∑ j : Fin m, b.repr ⟨w, hw⟩ j • (b j).1 := by
        have hval := congrArg Subtype.val hdecomp.symm
        simpa only [Submodule.coe_sum, SetLike.val_smul] using hval
      rw [hw_eq, sum_dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      rw [smul_dotProduct, hx j, smul_zero]
  exact Nat.eq_zero_of_le_zero (by simpa using kappaConj_le_card hcov)

/-! ### Section 3: Theorem B — Product Budget-Allocation Theorem for `kappaLin` -/

/-- Extract the `i`-th block of length `d` from an assignment on `Fin (s * d)`. -/
def blockOf {s d : ℕ} (x : Fin (s * d) → ZMod 2) (i : Fin s) : Fin d → ZMod 2 :=
  fun j => x (finProdFinEquiv (i, j))

/-- Assemble `s` block assignments of length `d` into an assignment on `Fin (s * d)`. -/
def combineBlocks {s d : ℕ} (xs : Fin s → (Fin d → ZMod 2)) : Fin (s * d) → ZMod 2 :=
  fun p => xs (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

@[simp]
lemma blockOf_combineBlocks {s d : ℕ} (xs : Fin s → (Fin d → ZMod 2)) (i : Fin s) :
    blockOf (combineBlocks xs) i = xs i := by
  ext j
  simp [blockOf, combineBlocks]

@[simp]
lemma combineBlocks_blockOf {s d : ℕ} (x : Fin (s * d) → ZMod 2) :
    combineBlocks (blockOf x) = x := by
  ext p
  change x (finProdFinEquiv (finProdFinEquiv.symm p)) = x p
  rw [finProdFinEquiv.apply_symm_apply]

/-- Product relation `∏_{i=1}^s Rs i` over `Fin (s * d) → ZMod 2`. -/
def prodRel {s d : ℕ} (Rs : Fin s → Set (Fin d → ZMod 2)) : Set (Fin (s * d) → ZMod 2) :=
  {x | ∀ i : Fin s, blockOf x i ∈ Rs i}

/-- Restrict a CNF clause on `Fin (s * d)` to block `i : Fin s`. -/
def restrictClause {s d : ℕ} (C : CNFClause (s * d)) (i : Fin s) : CNFClause d :=
  (C.filter (fun l => (finProdFinEquiv.symm l.var).1 = i)).image
    (fun l => ⟨(finProdFinEquiv.symm l.var).2, l.val⟩)

lemma satClause_iff_exists_restrictClause {s d : ℕ} (C : CNFClause (s * d))
    (x : Fin (s * d) → ZMod 2) :
    satClause C x ↔ ∃ i : Fin s, satClause (restrictClause C i) (blockOf x i) := by
  constructor
  · rintro ⟨l, hl, hxl⟩
    refine ⟨(finProdFinEquiv.symm l.var).1,
      ⟨(finProdFinEquiv.symm l.var).2, l.val⟩, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, rfl⟩, rfl⟩
    · change x (finProdFinEquiv (finProdFinEquiv.symm l.var)) = l.val
      rw [finProdFinEquiv.apply_symm_apply]
      exact hxl
  · rintro ⟨i, l', hl', hxl'⟩
    rcases Finset.mem_image.mp hl' with ⟨l, hl, rfl⟩
    rcases Finset.mem_filter.mp hl with ⟨hlC, hli⟩
    refine ⟨l, hlC, ?_⟩
    have hpair : finProdFinEquiv (i, (finProdFinEquiv.symm l.var).2) = l.var := by
      rw [← hli]
      exact finProdFinEquiv.apply_symm_apply l.var
    change x (finProdFinEquiv (i, (finProdFinEquiv.symm l.var).2)) = l.val at hxl'
    rwa [hpair] at hxl'

/-- Lift a CNF clause on block `i : Fin s` into `Fin (s * d)`. -/
def liftClause {s d : ℕ} (i : Fin s) (C : CNFClause d) : CNFClause (s * d) :=
  C.image (fun l => ⟨finProdFinEquiv (i, l.var), l.val⟩)

lemma satClause_liftClause {s d : ℕ} (i : Fin s) (C : CNFClause d)
    (x : Fin (s * d) → ZMod 2) :
    satClause (liftClause i C) x ↔ satClause C (blockOf x i) := by
  constructor
  · rintro ⟨l, hl, hxl⟩
    rcases Finset.mem_image.mp hl with ⟨l', hl', rfl⟩
    exact ⟨l', hl', hxl⟩
  · rintro ⟨l', hl', hxl'⟩
    exact ⟨⟨finProdFinEquiv (i, l'.var), l'.val⟩,
      Finset.mem_image.mpr ⟨l', hl', rfl⟩, hxl'⟩

/-- **Theorem B (Product Budget-Allocation Theorem for `kappaLin`)**:
For any `s` nonempty relations `Rs : Fin s → Set (Fin d → ZMod 2)` and any budget `r`,
there exists a subset `J : Finset (Fin s)` of cardinality `J.card ≤ r` such that
`∑ i ∈ Finset.univ \ J, kappa0 (Rs i) ≤ kappaLin (prodRel Rs) r`. -/
theorem kappaLin_product_lower_bound {s d : ℕ}
    (Rs : Fin s → Set (Fin d → ZMod 2))
    (hne : ∀ i, (Rs i).Nonempty)
    (r : ℕ) :
    ∃ J : Finset (Fin s), J.card ≤ r ∧
      ∑ i ∈ Finset.univ \ J, kappa0 (Rs i) ≤ kappaLin (prodRel Rs) r := by
  classical
  rcases exists_min_linCover (prodRel Rs) r with ⟨Ψ_lin, Ψ_cnf, hcov, hcard_eq⟩
  -- Pick a valid witness `a i ∈ Rs i` for each block `i`.
  choose a ha using hne
  -- Step 1: Every `C ∈ Ψ_cnf` has an owner block `owner C` where `restrictClause C (owner C)`
  -- is satisfied by all of `Rs (owner C)`.
  have howner_exists : ∀ C ∈ Ψ_cnf, ∃ i : Fin s, ∀ y ∈ Rs i, satClause (restrictClause C i) y := by
    intro C hC
    by_contra h
    push Not at h
    choose z hzR hnotSat using h
    have hz_prod : combineBlocks z ∈ prodRel Rs := by
      intro i; simpa using hzR i
    have hsatC := ((hcov.2 (combineBlocks z)).mp hz_prod).2 C hC
    rw [satClause_iff_exists_restrictClause] at hsatC
    rcases hsatC with ⟨i, hi⟩
    rw [blockOf_combineBlocks] at hi
    exact hnotSat i hi
  -- Handle `s = 0` cleanly first.
  by_cases hs0 : s = 0
  · subst hs0
    exact ⟨∅, Nat.zero_le r, by simp⟩
  have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
  let owner' : CNFClause (s * d) → Fin s := fun C =>
    if hC : C ∈ Ψ_cnf then Classical.choose (howner_exists C hC) else ⟨0, hs_pos⟩
  have howner'_spec : ∀ C ∈ Ψ_cnf, ∀ y ∈ Rs (owner' C),
      satClause (restrictClause C (owner' C)) y := by
    intro C hC
    simp only [owner', hC, ↓reduceDIte]
    exact Classical.choose_spec (howner_exists C hC)
  -- Step 2: Partition `Ψ_cnf` into fibers `Ψ_i` by `owner'`.
  let Ψ_blk : Fin s → Finset (CNFClause (s * d)) := fun i =>
    Ψ_cnf.filter (fun C => owner' C = i)
  -- Define `J` as the blocks where `Ψ_blk i` fails to cover `(Fin d → ZMod 2) \ Rs i`.
  let J : Finset (Fin s) :=
    Finset.univ.filter (fun i =>
      ∃ y : Fin d → ZMod 2, y ∉ Rs i ∧ ∀ C ∈ Ψ_blk i, satClause (restrictClause C i) y)
  -- For `i ∉ J`, `Ψ_blk i` gives a valid pure CNF cover of `Rs i`.
  have hnotJ_le : ∀ i ∈ Finset.univ \ J, kappa0 (Rs i) ≤ (Ψ_blk i).card := by
    intro i hi
    have hi_notJ : i ∉ J := (Finset.mem_sdiff.mp hi).2
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hi_notJ
    let Ψ_i : Finset (CNFClause d) := (Ψ_blk i).image (fun C => restrictClause C i)
    have hcov_i : IsConjCover (Rs i) 0 ∅ Ψ_i := by
      refine ⟨le_refl 0, fun y => ?_⟩
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
        Ψ_i, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      constructor
      · intro hy C hC
        rcases Finset.mem_filter.mp hC with ⟨hCmem, hCown⟩
        rw [← hCown]
        exact howner'_spec C hCmem y (hCown.symm ▸ hy)
      · intro hall
        by_contra hy
        exact hi_notJ y hy hall
    exact le_trans (kappaConj_le_card hcov_i) Finset.card_image_le
  -- Step 3: Prove `J.card ≤ r` via `F₂` rank-nullity.
  have hJ_card : J.card ≤ r := by
    by_contra hgt
    push Not at hgt
    -- Pick an uncovered falsifying witness `y_wit i` for each `i ∈ J`.
    have hy_exists : ∀ i : J, ∃ y : Fin d → ZMod 2,
        y ∉ Rs i.1 ∧ ∀ C ∈ Ψ_blk i.1, satClause (restrictClause C i.1) y := by
      intro ⟨i, hi⟩
      exact (Finset.mem_filter.mp hi).2
    choose y_wit hy_notR hy_sat using hy_exists
    -- Pick one equation `e_of L ∈ L` satisfied by `x₀ = combineBlocks a` for each `L ∈ Ψ_lin`.
    let x₀ : Fin (s * d) → ZMod 2 := combineBlocks a
    have hx₀_mem : x₀ ∈ prodRel Rs := by
      intro i; simpa [x₀] using ha i
    have he_exists : ∀ L : Ψ_lin, ∃ e ∈ L.1, satEq e x₀ := by
      intro ⟨L, hL⟩
      exact ((hcov.2 x₀).mp hx₀_mem).1 L hL
    choose e_of he_mem he_sat using he_exists
    -- Define the perturbation vector `δ i` for each `i : J`.
    let δ : J → (Fin (s * d) → ZMod 2) := fun i =>
      combineBlocks (fun j => if h : j = i.1 then y_wit i - a i.1 else 0)
    -- Linear map `T : (J → ZMod 2) →ₗ[ZMod 2] (Ψ_lin → ZMod 2)`.
    let T : (J → ZMod 2) →ₗ[ZMod 2] (Ψ_lin → ZMod 2) :=
      { toFun := fun u L => ∑ i : J, u i * dotProduct (e_of L).a (δ i)
        map_add' := fun u v => by
          ext L
          simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c u => by
          ext L
          simp [Finset.mul_sum, mul_assoc] }
    have hker_ne : LinearMap.ker T ≠ ⊥ := by
      intro hbot
      have hrank := LinearMap.finrank_range_add_finrank_ker T
      rw [hbot, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrank
      have hle_cod : Module.finrank (ZMod 2) (LinearMap.range T) ≤ Ψ_lin.card := by
        calc Module.finrank (ZMod 2) (LinearMap.range T)
            ≤ Module.finrank (ZMod 2) (Ψ_lin → ZMod 2) := Submodule.finrank_le _
          _ = Ψ_lin.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      have := hcov.1
      omega
    have hex_u : ∃ u : J → ZMod 2, u ≠ 0 ∧ T u = 0 := by
      by_contra h
      push Not at h
      apply hker_ne
      rw [Submodule.eq_bot_iff]
      intro u hu
      by_contra hu0
      exact h u hu0 hu
    rcases hex_u with ⟨u, hu_ne, hu_ker⟩
    -- Build `x_u = x₀ + ∑ i : J, u i • δ i`.
    let x_u : Fin (s * d) → ZMod 2 := x₀ + ∑ i : J, u i • δ i
    have hblock_xu : ∀ j : Fin s,
        blockOf x_u j =
          if hj : j ∈ J then (if u ⟨j, hj⟩ = 0 then a j else y_wit ⟨j, hj⟩) else a j := by
      intro j
      ext t
      have hsum_eval : (∑ i : J, u i • δ i) (finProdFinEquiv (j, t)) =
          ∑ i : J, u i * (if j = i.1 then (y_wit i - a i.1) t else 0) := by
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul, δ, combineBlocks, Equiv.symm_apply_apply]
        split_ifs <;> simp
      change x₀ (finProdFinEquiv (j, t)) + (∑ i : J, u i • δ i) (finProdFinEquiv (j, t)) = _
      rw [hsum_eval]
      have hx0_jt : x₀ (finProdFinEquiv (j, t)) = a j t := by
        simp [x₀, combineBlocks]
      rw [hx0_jt]
      by_cases hj : j ∈ J
      · simp only [hj, ↓reduceDIte]
        have hsingle : (∑ i : J, u i * (if j = i.1 then (y_wit i - a i.1) t else 0)) =
            u ⟨j, hj⟩ * (y_wit ⟨j, hj⟩ - a j) t := by
          rw [Finset.sum_eq_single ⟨j, hj⟩]
          · simp
          · intro i _ hne
            have hne' : j ≠ i.1 := fun h => hne (Subtype.ext h.symm)
            simp [hne']
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsingle]
        rcases zmod2_eq_or_eq (u ⟨j, hj⟩) with h0 | h1
        · simp [h0]
        · simp [h1, Pi.sub_apply]
      · simp only [hj, ↓reduceDIte]
        have hzero : (∑ i : J, u i * (if j = i.1 then (y_wit i - a i.1) t else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hne' : j ≠ i.1 := fun h => hj (h ▸ i.2)
          simp [hne']
        rw [hzero, add_zero]
    -- `x_u` satisfies every linear clause `L ∈ Ψ_lin` (via `e_of L`).
    have hxu_lin : ∀ L ∈ Ψ_lin, satLinClause L x_u := by
      intro L hL
      refine ⟨e_of ⟨L, hL⟩, he_mem ⟨L, hL⟩, ?_⟩
      unfold satEq
      change dotProduct (e_of ⟨L, hL⟩).a (x₀ + ∑ i : J, u i • δ i) = (e_of ⟨L, hL⟩).b
      rw [dotProduct_add, he_sat ⟨L, hL⟩, dotProduct_sum]
      have hterm : ∑ i : J, dotProduct (e_of ⟨L, hL⟩).a (u i • δ i) = T u ⟨L, hL⟩ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [dotProduct_smul, smul_eq_mul]
      rw [hterm, hu_ker]
      simp
    -- `x_u` satisfies every CNF clause `C ∈ Ψ_cnf` (via its owner block).
    have hxu_cnf : ∀ C ∈ Ψ_cnf, satClause C x_u := by
      intro C hC
      rw [satClause_iff_exists_restrictClause]
      refine ⟨owner' C, ?_⟩
      rw [hblock_xu (owner' C)]
      by_cases hj : owner' C ∈ J
      · simp only [hj, ↓reduceDIte]
        split_ifs
        · exact howner'_spec C hC (a (owner' C)) (ha (owner' C))
        · exact hy_sat ⟨owner' C, hj⟩ C (Finset.mem_filter.mpr ⟨hC, rfl⟩)
      · simp only [hj, ↓reduceDIte]
        exact howner'_spec C hC (a (owner' C)) (ha (owner' C))
    -- Therefore `x_u ∈ prodRel Rs`, contradicting `u ≠ 0`!
    have hxu_prod : x_u ∈ prodRel Rs := (hcov.2 x_u).mpr ⟨hxu_lin, hxu_cnf⟩
    have hex_nz : ∃ i : J, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu_ne (funext h)
    rcases hex_nz with ⟨i, hi_nz⟩
    have hmem_i := hxu_prod i.1
    rw [hblock_xu i.1] at hmem_i
    simp only [i.2, ↓reduceDIte, hi_nz, ↓reduceIte] at hmem_i
    exact hy_notR i hmem_i
  -- Step 4: Sum `kappa0 (Rs i) ≤ (Ψ_blk i).card` over `i ∈ Finset.univ \ J`.
  refine ⟨J, hJ_card, ?_⟩
  rw [← hcard_eq]
  calc ∑ i ∈ Finset.univ \ J, kappa0 (Rs i)
      ≤ ∑ i ∈ Finset.univ \ J, (Ψ_blk i).card := Finset.sum_le_sum hnotJ_le
    _ ≤ ∑ i : Fin s, (Ψ_blk i).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = Ψ_cnf.card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := owner') (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]

/-- Uniform-block corollary of Theorem B: if `∀ i, M ≤ kappa0 (Rs i)`, then
`(s - r) * M ≤ kappaLin (prodRel Rs) r`. -/
theorem kappaLin_product_uniform_lower_bound {s d M : ℕ}
    (Rs : Fin s → Set (Fin d → ZMod 2))
    (hne : ∀ i, (Rs i).Nonempty)
    (hM : ∀ i, M ≤ kappa0 (Rs i))
    (r : ℕ) :
    (s - r) * M ≤ kappaLin (prodRel Rs) r := by
  rcases kappaLin_product_lower_bound Rs hne r with ⟨J, hJ, hsum⟩
  calc (s - r) * M
      ≤ (Finset.univ \ J).card * M := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ J),
            Finset.card_univ, Fintype.card_fin]
        omega
    _ = ∑ _i ∈ Finset.univ \ J, M := by simp
    _ ≤ ∑ i ∈ Finset.univ \ J, kappa0 (Rs i) := Finset.sum_le_sum (fun i _ => hM i)
    _ ≤ kappaLin (prodRel Rs) r := hsum

/-! #### Instantiation 1: Parity Products `parityProd s d` -/

/-- Even-parity relation on `Fin d → ZMod 2`. -/
def parityRel (d : ℕ) : Set (Fin d → ZMod 2) :=
  {x | ∑ j : Fin d, x j = 0}

/-- The `s`-fold product of `d`-variable even-parity relations. -/
def parityProd (s d : ℕ) : Set (Fin (s * d) → ZMod 2) :=
  prodRel (fun _ : Fin s => parityRel d)

lemma parityRel_eq_orthComp (d : ℕ) :
    parityRel d = (orthComp (Submodule.span (ZMod 2) {(fun _ : Fin d => (1 : ZMod 2))}) :
      Set (Fin d → ZMod 2)) := by
  ext x
  simp only [parityRel, Set.mem_ofPred_eq, SetLike.mem_coe, mem_orthComp]
  constructor
  · intro hx w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    rw [smul_dotProduct, dotProduct]
    simp [hx]
  · intro hx
    have h := hx (fun _ => 1) (Submodule.subset_span (Set.mem_singleton _))
    simpa [dotProduct] using h

lemma finrank_span_ones {d : ℕ} (hd : 1 ≤ d) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {(fun _ : Fin d => (1 : ZMod 2))}) = 1 := by
  apply finrank_span_singleton
  intro h
  have := congrFun h ⟨0, hd⟩
  exact one_ne_zero this

lemma card_parityRel {d : ℕ} (hd : 1 ≤ d) :
    (Finset.univ.filter (fun x : Fin d → ZMod 2 => x ∈ parityRel d)).card = 2 ^ (d - 1) := by
  let U := Submodule.span (ZMod 2) {(fun _ : Fin d => (1 : ZMod 2))}
  have h1 : (Finset.univ.filter (fun x : Fin d → ZMod 2 => x ∈ parityRel d)).card =
      Fintype.card (orthComp U) := by
    rw [Fintype.card_of_subtype (Finset.univ.filter (fun x => x ∈ parityRel d))]
    intro x
    simp [parityRel_eq_orthComp, U]
  rw [h1, card_submodule_eq_pow_finrank]
  have h2 := finrank_orthComp_add_finrank U
  rw [finrank_span_ones hd] at h2
  congr 1; omega

lemma card_compl_parityRel {d : ℕ} (hd : 1 ≤ d) :
    (Finset.univ.filter (fun x : Fin d → ZMod 2 => x ∉ parityRel d)).card = 2 ^ (d - 1) := by
  have htot := card_filter_add_card_filter_not_univ (fun x : Fin d → ZMod 2 => x ∈ parityRel d)
  rw [card_parityRel hd, Fintype.card_pi] at htot
  simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at htot
  have hpow : 2 ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, Nat.pow_succ]
    omega
  omega

lemma kappa0_parityRel {d : ℕ} (hd : 1 ≤ d) :
    kappa0 (parityRel d) = 2 ^ (d - 1) := by
  apply le_antisymm
  · rcases exists_isConjCover_of_compl (parityRel d) 0 with ⟨H, Ψ, hcov, hcard⟩
    refine le_trans (kappaConj_le_card hcov) ?_
    rwa [card_compl_parityRel hd] at hcard
  · let U := Submodule.span (ZMod 2) {(fun _ : Fin d => (1 : ZMod 2))}
    have hdist : ∀ w ∈ U, w ≠ 0 → d ≤ hammingWeight w := by
      intro w hw hw0
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rcases zmod2_eq_or_eq c with rfl | rfl
      · simp at hw0
      · unfold hammingWeight
        simp
    have hr : 0 < Module.finrank (ZMod 2) U := by rw [finrank_span_ones hd]; decide
    have hcor := kappaConj_linear_code_plateau_cor U hdist hd hr
    simpa [kappa0, parityRel_eq_orthComp] using hcor

/-- Exact evaluation of `kappaLin` and `kappaConj` on parity products `parityProd s d`. -/
theorem kappaLin_parity_product_exact {s d : ℕ} (hd : 1 ≤ d) (r : ℕ) :
    kappaLin (parityProd s d) r = (s - r) * 2 ^ (d - 1) ∧
    kappaConj (parityProd s d) r = (s - r) * 2 ^ (d - 1) := by
  have hlow : (s - r) * 2 ^ (d - 1) ≤ kappaLin (parityProd s d) r := by
    apply kappaLin_product_uniform_lower_bound
    · intro _; exact ⟨0, by simp [parityRel]⟩
    · intro _; rw [kappa0_parityRel hd]
  -- Construct an explicit conjunctive cover of size `(s - r) * 2 ^ (d - 1)`.
  have hup : kappaConj (parityProd s d) r ≤ (s - r) * 2 ^ (d - 1) := by
    let eqFor : Fin s → F2Eq (s * d) := fun i =>
      ⟨combineBlocks (fun i' => if i' = i then (fun _ => 1) else 0), 0⟩
    have hsat_eqFor : ∀ i x, satEq (eqFor i) x ↔ blockOf x i ∈ parityRel d := by
      intro i x
      unfold satEq eqFor parityRel
      simp only [Set.mem_ofPred_eq, dotProduct]
      rw [← finProdFinEquiv.sum_comp]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp [combineBlocks, blockOf]
      · intro i' _ hi'
        apply Finset.sum_eq_zero
        intro j _
        simp [combineBlocks, hi']
      · intro h; exact absurd (Finset.mem_univ i) h
    let H_idx : Finset (Fin s) := Finset.univ.filter (fun i : Fin s => i.val < r)
    let C_idx : Finset (Fin s) := Finset.univ.filter (fun i : Fin s => r ≤ i.val)
    let H : Finset (F2Eq (s * d)) := H_idx.image eqFor
    let oddPts : Finset (Fin d → ZMod 2) :=
      Finset.univ.filter (fun y => y ∉ parityRel d)
    let Ψ : Finset (CNFClause (s * d)) :=
      C_idx.biUnion (fun i => oddPts.image (fun y => liftClause i (pointClause y)))
    have hH_card : H.card ≤ r := by
      calc H.card ≤ H_idx.card := Finset.card_image_le
        _ ≤ r := by
          have hinj : ∀ a ∈ H_idx, ∀ b ∈ H_idx, a.val = b.val → a = b :=
            fun _ _ _ _ h => Fin.ext h
          have hsub : H_idx.image Fin.val ⊆ Finset.range r := by
            intro n hn
            rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          rw [← Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h)]
          exact le_trans (Finset.card_le_card hsub) (by simp)
    have hC_card : C_idx.card = s - r := by
      have hdisj : Disjoint H_idx C_idx := by
        rw [Finset.disjoint_filter]
        intro i _ h1 h2; omega
      have hunion : H_idx ∪ C_idx = Finset.univ := by
        ext i
        simp only [H_idx, C_idx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => Nat.lt_or_ge i.val r⟩
      have hH_exact : H_idx.card = min s r := by
        have hbij : H_idx.image Fin.val = Finset.range (min s r) := by
          ext n
          simp only [Finset.mem_image, H_idx, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range, lt_min_iff]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨n, h1⟩, h2, rfl⟩
        rw [← Finset.card_image_of_injective H_idx Fin.val_injective, hbij, Finset.card_range]
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin, hH_exact] at hsum
      omega
    have hcov : IsConjCover (parityProd s d) r H Ψ := by
      refine ⟨hH_card, fun x => ?_⟩
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · intro e he
          rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
          exact (hsat_eqFor i x).mpr (hx i)
        · intro C hC
          rcases Finset.mem_biUnion.mp hC with ⟨i, _, hCi⟩
          rcases Finset.mem_image.mp hCi with ⟨y, hy, rfl⟩
          rw [satClause_liftClause, satClause_pointClause]
          intro heq
          exact (Finset.mem_filter.mp hy).2 (heq ▸ hx i)
      · rintro ⟨hH, hΨ⟩ i
        by_cases hi : i.val < r
        · exact (hsat_eqFor i x).mp (hH (eqFor i) (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩))
        · push Not at hi
          by_contra hnot
          have hmem : liftClause i (pointClause (blockOf x i)) ∈ Ψ :=
            Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩,
              Finset.mem_image.mpr ⟨blockOf x i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩, rfl⟩⟩
          have hsat := hΨ _ hmem
          rw [satClause_liftClause, satClause_pointClause] at hsat
          exact hsat rfl
    calc kappaConj (parityProd s d) r
        ≤ Ψ.card := kappaConj_le_card hcov
      _ ≤ ∑ i ∈ C_idx, (oddPts.image (fun y => liftClause i (pointClause y))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ C_idx, oddPts.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = (s - r) * 2 ^ (d - 1) := by
          rw [Finset.sum_const, smul_eq_mul, hC_card, card_compl_parityRel hd]
  have hle := kappaLin_le_kappaConj (parityProd s d) r
  omega

/-! #### Instantiation 2: Coupled Parity-Lifted Disjunction `orParityProd s w d` -/

/-- `OR_w ∘ ⊕_d`: at least one of the `w` blocks of length `d` has odd parity. -/
def orParityRel (w d : ℕ) : Set (Fin (w * d) → ZMod 2) :=
  {x | ∃ t : Fin w, ∑ j : Fin d, blockOf x t j = 1}

/-- The `s`-fold product of `OR_w ∘ ⊕_d`. -/
def orParityProd (s w d : ℕ) : Set (Fin (s * (w * d)) → ZMod 2) :=
  prodRel (fun _ : Fin s => orParityRel w d)

lemma not_mem_orParityRel_iff (w d : ℕ) (x : Fin (w * d) → ZMod 2) :
    x ∉ orParityRel w d ↔ x ∈ parityProd w d := by
  simp only [orParityRel, parityProd, prodRel, parityRel, Set.mem_ofPred_eq, not_exists]
  constructor
  · intro h t
    rcases zmod2_eq_or_eq (∑ j : Fin d, blockOf x t j) with h0 | h1
    · exact h0
    · exact absurd h1 (h t)
  · intro h t h1
    rw [h t] at h1
    exact zero_ne_one h1

lemma card_parityProd {w d : ℕ} (hd : 1 ≤ d) :
    (Finset.univ.filter (fun x : Fin (w * d) → ZMod 2 => x ∈ parityProd w d)).card =
      2 ^ (w * (d - 1)) := by
  let P : Finset (Fin w → (Fin d → ZMod 2)) :=
    Fintype.piFinset (fun _ : Fin w => Finset.univ.filter (fun y : Fin d → ZMod 2 => y ∈ parityRel d))
  have hbij : (Finset.univ.filter (fun x : Fin (w * d) → ZMod 2 => x ∈ parityProd w d)).card =
      P.card := by
    apply Finset.card_bij (fun x _ => blockOf x)
    · intro x hx
      rw [Fintype.mem_piFinset]
      intro t
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2 t⟩
    · intro x₁ _ x₂ _ h
      rw [← combineBlocks_blockOf x₁, ← combineBlocks_blockOf x₂, h]
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      refine ⟨combineBlocks f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩, ?_⟩
      · rw [blockOf_combineBlocks]
        exact (Finset.mem_filter.mp (hf t)).2
      · ext t j; simp
  rw [hbij, Fintype.card_piFinset]
  simp only [card_parityRel hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.pow_mul, mul_comm]

lemma orParityRel_nonempty {w d : ℕ} (hw : 1 ≤ w) (hd : 1 ≤ d) :
    (orParityRel w d).Nonempty := by
  let x : Fin (w * d) → ZMod 2 :=
    combineBlocks (fun t => if t = ⟨0, hw⟩ then Pi.single ⟨0, hd⟩ 1 else 0)
  refine ⟨x, ⟨0, hw⟩, ?_⟩
  simp [x, Pi.single_apply]

lemma kappa0_orParityRel {w d : ℕ} (hd : 1 ≤ d) :
    kappa0 (orParityRel w d) = 2 ^ (w * (d - 1)) := by
  apply le_antisymm
  · rcases exists_isConjCover_of_compl (orParityRel w d) 0 with ⟨H, Ψ, hcov, hcard⟩
    refine le_trans (kappaConj_le_card hcov) ?_
    have hfilt : (Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∉ orParityRel w d)) =
        Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∈ parityProd w d) := by
      ext y; simp [not_mem_orParityRel_iff]
    rw [hfilt, card_parityProd hd] at hcard
    exact hcard
  · rcases exists_min_conjCover (orParityRel w d) 0 with ⟨H, Ψ, hcov, hcard_eq⟩
    unfold kappa0
    rw [← hcard_eq]
    have hH : H = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcov.1)
    -- Every `C ∈ Ψ` falsifying some `y ∈ parityProd w d` must touch all `w * d` coordinates,
    -- hence falsifies at most ONE point!
    have hunique : ∀ C ∈ Ψ, ∀ y₁ y₂ : Fin (w * d) → ZMod 2,
        y₁ ∈ falsifiesClause C → y₂ ∈ falsifiesClause C → y₁ = y₂ := by
      intro C hC y₁ y₂ hy₁ hy₂
      have hfull : clauseVars C = Finset.univ := by
        by_contra hne
        have : ∃ p : Fin (w * d), p ∉ clauseVars C := by
          by_contra hall
          push Not at hall
          apply hne
          ext p; simp [hall p]
        rcases this with ⟨p, hp⟩
        -- Flip coordinate `p` of `y₁`: still falsifies `C`, yet enters `orParityRel w d`!
        let y' := Function.update y₁ p (y₁ p + 1)
        have hy'F : y' ∈ falsifiesClause C := by
          rw [mem_falsifiesClause_iff hy₁, mem_orthComp_supportedOn]
          intro q hq
          have hqp : q ≠ p := fun h => hp (h ▸ hq)
          simp [y', Function.update_of_ne hqp]
        have hy1_notR : y₁ ∉ orParityRel w d := fun hR => hy₁ (((hcov.2 y₁).mp hR).2 C hC)
        have hy1_par : y₁ ∈ parityProd w d := (not_mem_orParityRel_iff w d y₁).mp hy1_notR
        have hy'_inR : y' ∈ orParityRel w d := by
          let t := (finProdFinEquiv.symm p).1
          let j₀ := (finProdFinEquiv.symm p).2
          refine ⟨t, ?_⟩
          have hsum_eq : ∑ j : Fin d, blockOf y' t j = (∑ j : Fin d, blockOf y₁ t j) + 1 := by
            have hite : ∀ j : Fin d, blockOf y' t j =
                blockOf y₁ t j + if j = j₀ then 1 else 0 := by
              intro j
              by_cases hj : j = j₀
              · subst hj
                have hp_eq : finProdFinEquiv (t, j₀) = p := finProdFinEquiv.apply_symm_apply p
                simp [blockOf, y', hp_eq]
              · have hp_ne : finProdFinEquiv (t, j) ≠ p := by
                  intro heq
                  apply hj
                  have := congrArg (fun q => (finProdFinEquiv.symm q).2) heq
                  simpa [j₀] using this
                simp [blockOf, y', Function.update_of_ne hp_ne, hj]
            simp_rw [hite]
            rw [Finset.sum_add_distrib]
            simp
          rw [hsum_eq, hy1_par t, zero_add]
        exact hy'F (((hcov.2 y').mp hy'_inR).2 C hC)
      rw [mem_falsifiesClause_iff hy₁, hfull, mem_orthComp_supportedOn] at hy₂
      ext p
      exact (sub_eq_zero.mp (hy₂ p (Finset.mem_univ p))).symm
    -- Inject `parityProd w d` into `Ψ` by mapping each `y` to a clause `C ∈ Ψ` falsified by `y`.
    let S := Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∈ parityProd w d)
    have hmap_ex : ∀ y ∈ S, ∃ C ∈ Ψ, y ∈ falsifiesClause C := by
      intro y hy
      have hy_notR : y ∉ orParityRel w d :=
        (not_mem_orParityRel_iff w d y).mpr (Finset.mem_filter.mp hy).2
      have hnot : ¬ ∀ C ∈ Ψ, satClause C y := by
        intro hall
        exact hy_notR ((hcov.2 y).mpr ⟨by simp [hH], hall⟩)
      push Not at hnot
      exact hnot
    have hcard_le : S.card ≤ Ψ.card := by
      apply Finset.card_le_card_of_injOn (fun y => if hy : y ∈ S then Classical.choose (hmap_ex y hy) else ∅)
      · intro y hy
        rw [Finset.mem_coe] at hy ⊢
        simp only [hy, ↓reduceDIte]
        exact (Classical.choose_spec (hmap_ex y hy)).1
      · intro y₁ hy₁ y₂ hy₂ heq
        rw [Finset.mem_coe] at hy₁ hy₂
        simp only [hy₁, hy₂, ↓reduceDIte] at heq
        let C := Classical.choose (hmap_ex y₁ hy₁)
        have hC_mem : C ∈ Ψ := (Classical.choose_spec (hmap_ex y₁ hy₁)).1
        have h1 : y₁ ∈ falsifiesClause C := (Classical.choose_spec (hmap_ex y₁ hy₁)).2
        have h2 : y₂ ∈ falsifiesClause C := by
          have hC_eq : C = Classical.choose (hmap_ex y₂ hy₂) := heq
          rw [hC_eq]
          exact (Classical.choose_spec (hmap_ex y₂ hy₂)).2
        exact hunique C hC_mem y₁ y₂ h1 h2
    simpa [S, card_parityProd hd] using hcard_le

/-- **Theorem B (Smooth staircase for `orParityProd`)**:
For `1 ≤ w`, `1 ≤ d`, and any budget `r`,
`kappaLin (orParityProd s w d) r = (s - r) * 2 ^ (w * (d - 1))`. -/
theorem kappaLin_orParity_exact {s w d : ℕ} (hw : 1 ≤ w) (hd : 1 ≤ d) (r : ℕ) :
    kappaLin (orParityProd s w d) r = (s - r) * 2 ^ (w * (d - 1)) := by
  apply le_antisymm
  · -- Upper bound: put one width-`w` disjunctive linear clause for each block `i < r`,
    -- and `2 ^ (w * (d - 1))` CNF clauses for each remaining block `i ≥ r`.
    let eqBlockSub : Fin s → Fin w → F2Eq (s * (w * d)) := fun i t =>
      ⟨combineBlocks (fun i' =>
        if i' = i then combineBlocks (fun t' => if t' = t then (fun _ => 1) else 0) else 0), 1⟩
    have hsat_eq : ∀ i t x,
        satEq (eqBlockSub i t) x ↔ ∑ j : Fin d, blockOf (blockOf x i) t j = 1 := by
      intro i t x
      unfold satEq eqBlockSub
      simp only [dotProduct]
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp only [combineBlocks, Equiv.symm_apply_apply, ↓reduceIte]
        rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single t]
        · simp [blockOf]
        · intro t' _ ht'
          apply Finset.sum_eq_zero
          intro j _
          simp [ht']
        · intro h; exact absurd (Finset.mem_univ t) h
      · intro i' _ hi'
        apply Finset.sum_eq_zero
        intro p _
        simp [combineBlocks, hi']
      · intro h; exact absurd (Finset.mem_univ i) h
    let linClauseFor : Fin s → F2LinClause (s * (w * d)) := fun i =>
      Finset.univ.image (eqBlockSub i)
    have hsat_lin : ∀ i x, satLinClause (linClauseFor i) x ↔ blockOf x i ∈ orParityRel w d := by
      intro i x
      simp only [satLinClause, linClauseFor, Finset.mem_image, Finset.mem_univ, true_and,
        exists_exists_eq_and, hsat_eq, orParityRel, Set.mem_ofPred_eq]
    let H_idx : Finset (Fin s) := Finset.univ.filter (fun i : Fin s => i.val < r)
    let C_idx : Finset (Fin s) := Finset.univ.filter (fun i : Fin s => r ≤ i.val)
    let Ψ_lin : Finset (F2LinClause (s * (w * d))) := H_idx.image linClauseFor
    let badPts : Finset (Fin (w * d) → ZMod 2) :=
      Finset.univ.filter (fun y => y ∈ parityProd w d)
    let Ψ_cnf : Finset (CNFClause (s * (w * d))) :=
      C_idx.biUnion (fun i => badPts.image (fun y => liftClause i (pointClause y)))
    have hH_card : Ψ_lin.card ≤ r := by
      calc Ψ_lin.card ≤ H_idx.card := Finset.card_image_le
        _ ≤ r := by
          have hsub : H_idx.image Fin.val ⊆ Finset.range r := by
            intro n hn
            rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          rw [← Finset.card_image_of_injective H_idx Fin.val_injective]
          exact le_trans (Finset.card_le_card hsub) (by simp)
    have hC_card : C_idx.card = s - r := by
      have hdisj : Disjoint H_idx C_idx := by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; omega
      have hunion : H_idx ∪ C_idx = Finset.univ := by
        ext i
        simp only [H_idx, C_idx, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => Nat.lt_or_ge i.val r⟩
      have hH_exact : H_idx.card = min s r := by
        have hbij : H_idx.image Fin.val = Finset.range (min s r) := by
          ext n
          simp only [Finset.mem_image, H_idx, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range, lt_min_iff]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨n, h1⟩, h2, rfl⟩
        rw [← Finset.card_image_of_injective H_idx Fin.val_injective, hbij, Finset.card_range]
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin, hH_exact] at hsum
      omega
    have hcov : IsLinCover (orParityProd s w d) r Ψ_lin Ψ_cnf := by
      refine ⟨hH_card, fun x => ?_⟩
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · intro L hL
          rcases Finset.mem_image.mp hL with ⟨i, _, rfl⟩
          exact (hsat_lin i x).mpr (hx i)
        · intro C hC
          rcases Finset.mem_biUnion.mp hC with ⟨i, _, hCi⟩
          rcases Finset.mem_image.mp hCi with ⟨y, hy, rfl⟩
          rw [satClause_liftClause, satClause_pointClause]
          intro heq
          have hy_notR : y ∉ orParityRel w d :=
            (not_mem_orParityRel_iff w d y).mpr (Finset.mem_filter.mp hy).2
          exact hy_notR (heq ▸ hx i)
      · rintro ⟨hL, hC⟩ i
        by_cases hi : i.val < r
        · exact (hsat_lin i x).mp (hL _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩))
        · push Not at hi
          by_contra hnot
          have hmem : liftClause i (pointClause (blockOf x i)) ∈ Ψ_cnf :=
            Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩,
              Finset.mem_image.mpr ⟨blockOf x i,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, (not_mem_orParityRel_iff w d _).mp hnot⟩, rfl⟩⟩
          have hsat := hC _ hmem
          rw [satClause_liftClause, satClause_pointClause] at hsat
          exact hsat rfl
    calc kappaLin (orParityProd s w d) r
        ≤ Ψ_cnf.card := kappaLin_le_card hcov
      _ ≤ ∑ i ∈ C_idx, (badPts.image (fun y => liftClause i (pointClause y))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ C_idx, badPts.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = (s - r) * 2 ^ (w * (d - 1)) := by
          rw [Finset.sum_const, smul_eq_mul, hC_card, card_parityProd hd]
  · apply kappaLin_product_uniform_lower_bound
    · intro _; exact orParityRel_nonempty hw hd
    · intro _; rw [kappa0_orParityRel hd]

/-- **Theorem B (Conjunctive `F₂` Blindness)**:
For `2 ≤ w` and `1 ≤ d`, no nontrivial affine `F₂`-equation is valid on `orParityProd s w d`,
so `kappaConj (orParityProd s w d) r = s * 2 ^ (w * (d - 1))` for ALL budgets `r`. -/
theorem kappaConj_orParity_blind {s w d : ℕ} (hw : 2 ≤ w) (hd : 1 ≤ d) (r : ℕ) :
    kappaConj (orParityProd s w d) r = s * 2 ^ (w * (d - 1)) := by
  have hw1 : 1 ≤ w := by omega
  have h0 : kappaConj (orParityProd s w d) 0 = s * 2 ^ (w * (d - 1)) := by
    rw [← kappaLin_zero_eq_kappaConj_zero, kappaLin_orParity_exact hw1 hd 0]
    simp
  apply le_antisymm
  · rw [← h0]
    exact kappaConj_antitone _ (Nat.zero_le r)
  · rcases exists_min_conjCover (orParityProd s w d) r with ⟨H, Ψ, hcov, hcard_eq⟩
    rw [← hcard_eq, ← h0]
    -- Show every `e ∈ H` is trivial (`e.a = 0` and `e.b = 0`).
    have htriv : ∀ e ∈ H, ∀ x, satEq e x := by
      intro e he
      have ha_zero : e.a = 0 := by
        by_contra hne
        have hex_p : ∃ p : Fin (s * (w * d)), e.a p ≠ 0 := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        rcases hex_p with ⟨p, hp⟩
        let i₀ := (finProdFinEquiv.symm p).1
        let q₀ := (finProdFinEquiv.symm p).2
        -- Pick a valid witness `a_w ∈ orParityRel w d` for all other blocks `i ≠ i₀`.
        rcases orParityRel_nonempty hw1 hd with ⟨a_w, ha_w⟩
        let c_other : ZMod 2 :=
          ∑ i ∈ Finset.univ.erase i₀, dotProduct (blockOf e.a i) a_w
        -- Every `y ∈ orParityRel w d` must satisfy `dotProduct (blockOf e.a i₀) y = e.b + c_other`.
        have hhyper : ∀ y ∈ orParityRel w d,
            dotProduct (blockOf e.a i₀) y = e.b + c_other := by
          intro y hy
          let x : Fin (s * (w * d)) → ZMod 2 :=
            combineBlocks (fun i => if i = i₀ then y else a_w)
          have hxR : x ∈ orParityProd s w d := by
            intro i
            rw [blockOf_combineBlocks]
            split_ifs
            · exact hy
            · exact ha_w
          have hsat := ((hcov.2 x).mp hxR).1 e he
          unfold satEq at hsat
          have hsplit : dotProduct e.a x = dotProduct (blockOf e.a i₀) y + c_other := by
            unfold dotProduct
            rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
            congr 1
            · apply Finset.sum_congr rfl
              intro q _; simp [blockOf, x, combineBlocks]
            · apply Finset.sum_congr rfl
              intro i hi
              have hne_i : i ≠ i₀ := (Finset.mem_erase.mp hi).1
              apply Finset.sum_congr rfl
              intro q _; simp [blockOf, x, combineBlocks, hne_i]
          rw [hsplit] at hsat
          calc dotProduct (blockOf e.a i₀) y
              = dotProduct (blockOf e.a i₀) y + (c_other + c_other) := by rw [zmod2_add_self, add_zero]
            _ = (dotProduct (blockOf e.a i₀) y + c_other) + c_other := by ring
            _ = e.b + c_other := by rw [hsat]
        -- Yet `blockOf e.a i₀ ≠ 0`, so the hyperplane has cardinality `2 ^ (w * d - 1)`,
        -- strictly smaller than `|orParityRel w d| = 2 ^ (w * d) - 2 ^ (w * (d - 1))`!
        let v := blockOf e.a i₀
        have hv_ne : v ≠ 0 := by
          intro hv0
          have := congrFun hv0 q₀
          have hp_eq : finProdFinEquiv (i₀, q₀) = p := finProdFinEquiv.apply_symm_apply p
          simp [v, blockOf, hp_eq] at this
          exact hp this
        let S_hyp := Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => dotProduct v y = e.b + c_other)
        let S_R := Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∈ orParityRel w d)
        have hsub : S_R ⊆ S_hyp := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hhyper y (Finset.mem_filter.mp hy).2⟩
        have hcard_R : S_R.card = 2 ^ (w * d) - 2 ^ (w * (d - 1)) := by
          have htot := card_filter_add_card_filter_not_univ (fun y : Fin (w * d) → ZMod 2 => y ∈ orParityRel w d)
          have hneg : (Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∉ orParityRel w d)).card =
              2 ^ (w * (d - 1)) := by
            have heq : (Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∉ orParityRel w d)) =
                Finset.univ.filter (fun y => y ∈ parityProd w d) := by
              ext y; simp [not_mem_orParityRel_iff]
            rw [heq, card_parityProd hd]
          change S_R.card + (Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y ∉ orParityRel w d)).card =
            Fintype.card (Fin (w * d) → ZMod 2) at htot
          rw [hneg, Fintype.card_pi] at htot
          simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at htot
          omega
        have hcard_hyp : S_hyp.card = 2 ^ (w * d - 1) := by
          -- `S_hyp` is a nonempty coset of `orthComp (span {v})`, which has `finrank = w * d - 1`.
          have hne_hyp : S_hyp.Nonempty := by
            refine ⟨a_w, hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_w⟩)⟩
          rcases hne_hyp with ⟨y₀, hy₀⟩
          have hy₀_eq : dotProduct v y₀ = e.b + c_other := (Finset.mem_filter.mp hy₀).2
          let U := Submodule.span (ZMod 2) {v}
          have hS_eq : S_hyp = Finset.univ.filter (fun y : Fin (w * d) → ZMod 2 => y - y₀ ∈ orthComp U) := by
            ext y
            simp only [S_hyp, Finset.mem_filter, Finset.mem_univ, true_and, mem_orthComp]
            constructor
            · intro hy w' hw'
              rcases Submodule.mem_span_singleton.mp hw' with ⟨c, rfl⟩
              rw [smul_dotProduct, dotProduct_sub, hy, hy₀_eq, sub_self, smul_zero]
            · intro hy
              have h := hy v (Submodule.subset_span (Set.mem_singleton v))
              rw [dotProduct_sub, sub_eq_zero] at h
              rw [h, hy₀_eq]
          rw [hS_eq, card_coset_eq]
          have hrk1 : Module.finrank (ZMod 2) U = 1 := finrank_span_singleton hv_ne
          have hsum := finrank_orthComp_add_finrank U
          congr 1; omega
        have hle := Finset.card_le_card hsub
        rw [hcard_R, hcard_hyp] at hle
        -- Contradiction: `w * (d - 1) + 1 ≤ w * d - 1`, so `2^(w*(d-1)) < 2^(w*d - 1)`.
        have hwd_pos : 1 ≤ w * d := Nat.mul_pos (by omega) hd
        have hexp : w * (d - 1) < w * d - 1 := by
          have : w * d = w * (d - 1) + w := by
            conv_lhs => rw [← Nat.sub_add_cancel hd, Nat.mul_add, mul_one]
          omega
        have hlt_pow : 2 ^ (w * (d - 1)) < 2 ^ (w * d - 1) :=
          Nat.pow_lt_pow_right (by decide) hexp
        have hdouble : 2 ^ (w * d) = 2 ^ (w * d - 1) + 2 ^ (w * d - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hwd_pos, Nat.pow_succ]
          omega
        omega
      -- Since `e.a = 0` and `orParityProd s w d` is nonempty, `e.b = 0`.
      rcases orParityRel_nonempty hw1 hd with ⟨a_w, ha_w⟩
      have hx0 : combineBlocks (fun _ : Fin s => a_w) ∈ orParityProd s w d := by
        intro i; simpa using ha_w
      have hsat0 := ((hcov.2 _).mp hx0).1 e he
      rw [satEq, ha_zero, zero_dotProduct] at hsat0
      intro x
      rw [satEq, ha_zero, zero_dotProduct, hsat0]
    -- Hence `Ψ` alone is a valid pure CNF cover (`r = 0`).
    have hcov0 : IsConjCover (orParityProd s w d) 0 ∅ Ψ := by
      refine ⟨le_refl 0, fun x => ?_⟩
      rw [hcov.2 x]
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and]
      exact ⟨fun h => h.2, fun hΨ => ⟨fun e he => htriv e he x, hΨ⟩⟩
    exact kappaConj_le_card hcov0

/-! ### Section 4: Theorem C — Hybrid `ElimDynamics_r` Lower Bound -/

/-- Existential projection of `M : Set (Fin n → ZMod 2)` eliminating the variable set `E`. -/
def existsProj {n : ℕ} (E : Finset (Fin n)) (M : Set (Fin n → ZMod 2)) :
    Set (Fin n → ZMod 2) :=
  {x | ∃ y ∈ M, ∀ v, v ∉ E → y v = x v}

/-- An exact hybrid elimination state with eliminated variables `E`, at most `r` affine `F₂`
equations `H`, and CNF clause set `F`, satisfying the semantic projection invariant. -/
structure HybridElimState (n r : ℕ) (Φ : Set (Fin n → ZMod 2)) where
  E : Finset (Fin n)
  H : Finset (F2Eq n)
  F : Finset (CNFClause n)
  hH_card : H.card ≤ r
  hInv : ∀ x, x ∈ existsProj E Φ ↔ (∀ e ∈ H, satEq e x) ∧ (∀ C ∈ F, satClause C x)

/-- Extend an assignment on `Cstar` (indexed by `Fin Cstar.card` via `emb`) using `ρ` outside `Cstar`. -/
def extendWith {n : ℕ} (Cstar : Finset (Fin n))
    (emb : Fin Cstar.card ≃ {v : Fin n // v ∈ Cstar})
    (ρ : Fin n → ZMod 2) (x : Fin Cstar.card → ZMod 2) : Fin n → ZMod 2 :=
  fun v => if hv : v ∈ Cstar then x (emb.symm ⟨v, hv⟩) else ρ v

/-- The existential projection of `M` onto the component `Cstar` (indexed by `Fin Cstar.card`). -/
def projOn {n : ℕ} (Cstar : Finset (Fin n))
    (emb : Fin Cstar.card ≃ {v : Fin n // v ∈ Cstar})
    (M : Set (Fin n → ZMod 2)) : Set (Fin Cstar.card → ZMod 2) :=
  {x | ∃ y ∈ M, ∀ j : Fin Cstar.card, y (emb j).1 = x j}

/-- **Theorem C (Hybrid `ElimDynamics_r` Lower Bound)**:
If `S : HybridElimState n r Φ` and `Cstar` is a projection-cylindrical component witnessed by `ρ`
(meaning restricting `existsProj S.E Φ` by `ρ` outside `Cstar` recovers `projOn Cstar emb Φ`),
then `kappaConj (projOn Cstar emb Φ) r ≤ S.F.card`. -/
theorem hybridElim_size_ge_kappaConj {n r : ℕ} {Φ : Set (Fin n → ZMod 2)}
    (S : HybridElimState n r Φ)
    (Cstar : Finset (Fin n))
    (emb : Fin Cstar.card ≃ {v : Fin n // v ∈ Cstar})
    (ρ : Fin n → ZMod 2)
    (hCyl : ∀ x : Fin Cstar.card → ZMod 2,
      extendWith Cstar emb ρ x ∈ existsProj S.E Φ ↔ x ∈ projOn Cstar emb Φ) :
    kappaConj (projOn Cstar emb Φ) r ≤ S.F.card := by
  classical
  -- Substitute `ρ` into each linear equation `e ∈ S.H`.
  let substEq : F2Eq n → F2Eq Cstar.card := fun e =>
    ⟨fun j => e.a (emb j).1, e.b + ∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v⟩
  have hsat_substEq : ∀ e x,
      satEq (substEq e) x ↔ satEq e (extendWith Cstar emb ρ x) := by
    intro e x
    unfold satEq substEq
    have hsplit : dotProduct e.a (extendWith Cstar emb ρ x) =
        dotProduct (fun j => e.a (emb j).1) x + ∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v := by
      unfold dotProduct
      rw [← Finset.sum_sdiff (Finset.subset_univ Cstar)]
      rw [add_comm]
      congr 1
      · have h1 : ∑ v ∈ Cstar, e.a v * extendWith Cstar emb ρ x v =
            ∑ v : {v : Fin n // v ∈ Cstar}, e.a v.1 * extendWith Cstar emb ρ x v.1 :=
          (Finset.sum_coe_sort Cstar (fun v => e.a v * extendWith Cstar emb ρ x v)).symm
        rw [h1, ← emb.sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        simp [extendWith, (emb j).2]
      · apply Finset.sum_congr rfl
        intro v hv
        have hv' : v ∉ Cstar := (Finset.mem_sdiff.mp hv).2
        simp [extendWith, hv']
    rw [hsplit]
    constructor
    · intro h
      rw [h, add_assoc, zmod2_add_self, add_zero]
    · intro h
      calc dotProduct (fun j => e.a (emb j).1) x
          = dotProduct (fun j => e.a (emb j).1) x +
              ((∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v) +
               (∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v)) := by rw [zmod2_add_self, add_zero]
        _ = (dotProduct (fun j => e.a (emb j).1) x + ∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v) +
              ∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v := by ring
        _ = e.b + ∑ v ∈ Finset.univ \ Cstar, e.a v * ρ v := by rw [h]
  -- Substitute `ρ` into each CNF clause `C ∈ S.F`.
  let isSatByRho : CNFClause n → Prop := fun C => ∃ l ∈ C, l.var ∉ Cstar ∧ ρ l.var = l.val
  let substClause : CNFClause n → CNFClause Cstar.card := fun C =>
    (C.filter (fun l => l.var ∈ Cstar)).attach.image
      (fun l => ⟨emb.symm ⟨l.1.var, ((Finset.mem_filter (p := fun l : CNFLit n => l.var ∈ Cstar)).mp l.property).2⟩, l.1.val⟩)
  have hsat_substClause : ∀ C, ¬ isSatByRho C → ∀ x,
      satClause (substClause C) x ↔ satClause C (extendWith Cstar emb ρ x) := by
    intro C hnot x
    constructor
    · rintro ⟨l', hl', hxl'⟩
      rcases Finset.mem_image.mp hl' with ⟨⟨l, hl⟩, _, rfl⟩
      rcases Finset.mem_filter.mp hl with ⟨hlC, hlvar⟩
      refine ⟨l, hlC, ?_⟩
      simpa [extendWith, hlvar] using hxl'
    · rintro ⟨l, hlC, hxl⟩
      by_cases hlvar : l.var ∈ Cstar
      · refine ⟨⟨emb.symm ⟨l.var, hlvar⟩, l.val⟩, ?_, ?_⟩
        · exact Finset.mem_image.mpr
            ⟨⟨l, Finset.mem_filter.mpr ⟨hlC, hlvar⟩⟩, Finset.mem_attach _ _, rfl⟩
        · simpa [extendWith, hlvar] using hxl
      · exfalso
        apply hnot
        refine ⟨l, hlC, hlvar, ?_⟩
        simpa [extendWith, hlvar] using hxl
  let H' : Finset (F2Eq Cstar.card) := S.H.image substEq
  let F_rem : Finset (CNFClause n) := S.F.filter (fun C => ¬ isSatByRho C)
  let F' : Finset (CNFClause Cstar.card) := F_rem.image substClause
  have hcov : IsConjCover (projOn Cstar emb Φ) r H' F' := by
    refine ⟨le_trans Finset.card_image_le S.hH_card, fun x => ?_⟩
    rw [← hCyl x, S.hInv]
    constructor
    · rintro ⟨hH, hF⟩
      refine ⟨?_, ?_⟩
      · intro e' he'
        rcases Finset.mem_image.mp he' with ⟨e, he, rfl⟩
        exact (hsat_substEq e x).mpr (hH e he)
      · intro C' hC'
        rcases Finset.mem_image.mp hC' with ⟨C, hC, rfl⟩
        rcases Finset.mem_filter.mp hC with ⟨hCF, hCnot⟩
        exact (hsat_substClause C hCnot x).mpr (hF C hCF)
    · rintro ⟨hH', hF'⟩
      refine ⟨?_, ?_⟩
      · intro e he
        exact (hsat_substEq e x).mp (hH' (substEq e) (Finset.mem_image.mpr ⟨e, he, rfl⟩))
      · intro C hCF
        by_cases hsat : isSatByRho C
        · rcases hsat with ⟨l, hlC, hlvar, hρ⟩
          refine ⟨l, hlC, ?_⟩
          simp [extendWith, hlvar, hρ]
        · exact (hsat_substClause C hsat x).mp
            (hF' (substClause C)
              (Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hCF, hsat⟩, rfl⟩))
  calc kappaConj (projOn Cstar emb Φ) r
      ≤ F'.card := kappaConj_le_card hcov
    _ ≤ F_rem.card := Finset.card_image_le
    _ ≤ S.F.card := Finset.card_filter_le _ _

end Mathmatica.HybridBasisCover
