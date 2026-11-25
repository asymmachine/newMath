/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.DAGResolution

/-!
# Ben-Sasson–Wigderson Width–Size Tradeoff for General DAG Resolution

This module completes the formalization of the Ben-Sasson–Wigderson (2001) width–size tradeoff
theorem for general DAG-like propositional resolution (the proof-theoretic model of CDCL SAT
solvers).

We work with general DAG resolution with weakening (`IsWeakDAGProof`), which embeds standard DAG
resolution (`IsDAGProof.toWeak`) without increasing proof width or size. Using single-literal
restriction (`restrictDAGProof`), proof lifting (`liftDAGProof`), unit-clause combination
(`combineDAGWithUnit`), and the fat-clause averaging lemma from `Mathmatica.DAGResolution`, we
establish the full width–size tradeoff and its contrapositive exponential size lower bound.

## Main definitions

* `IsWeakDAGProof φ π`: A DAG resolution proof from `φ` allowing clause weakening.
* `IsWeakDAGRefutation φ π`: A weak DAG resolution proof from `φ` deriving `∅`.
* `restrictDAGProof l π`: The restriction of a DAG proof `π` obtained by removing clauses
  containing `l` and erasing `l.neg` from all remaining clauses.
* `proofVars π`: The finite set of Boolean variables occurring in clauses of `π`.

## Main results

* `IsDAGProof.toWeak` and `IsDAGRefutation.toWeak`: Standard DAG resolution embeds into weak DAG
  resolution.
* `restrictDAGProof_isRefutation`: Restricting a weak DAG refutation of `φ` by `l` yields a weak
  DAG refutation of `restrictCNF l φ`.
* `card_fatClauses_restrictDAGProof_le`: Fat clauses of `restrictDAGProof l π` are bounded by the
  fat clauses of `π` not containing `l`.
* `liftDAGProof`: Lifting a weak DAG refutation of `restrictCNF l φ` of width `≤ W` yields a weak
  DAG proof from `φ` deriving `{l.neg}` of width `≤ W + 1`.
* `combineDAGWithUnit`: Combining a weak DAG derivation of `{l}` from `φ` (width `≤ W₁`) with a
  weak DAG refutation of `restrictCNF l φ` (width `≤ W₂`) yields a weak DAG refutation of `φ`
  of width `≤ max W₁ W₂`.
* `bsw_dag_width_size_tradeoff`: Full Ben-Sasson–Wigderson (2001) width–size tradeoff for
  general DAG resolution.
* `bsw_dag_size_lower_bound`: Contrapositive exponential size lower bound for general DAG
  resolution.

## References

* E. Ben-Sasson and A. Wigderson, *Short proofs are narrow — resolution made simple*,
  Journal of the ACM 48 (2001), no. 2, 149–169.
-/

namespace Mathmatica.BSWDAGFull

open Mathmatica.BSWTradeoff
open Mathmatica.DAGResolution

/-! ### General DAG resolution with weakening -/

/-- A general DAG resolution proof with weakening from a CNF formula `φ`: a finite sequence `π` of
clauses in which each clause `π[i]` is either an input clause of `φ`, a weakening (superset) of an
earlier clause `π[j]` (`j < i`), or the resolvent of two earlier clauses `π[j]` and `π[k]`
(`j < i`, `k < i`). -/
def IsWeakDAGProof {n : ℕ} (φ : CNF n) (π : List (Clause n)) : Prop :=
  ∀ (i : ℕ) (hi : i < π.length),
    π[i] ∈ φ ∨
      (∃ (j : ℕ) (hj : j < i), (π[j]'(lt_trans hj hi)) ⊆ π[i]) ∨
      (∃ (j k : ℕ) (hj : j < i) (hk : k < i),
        IsResolvent (π[j]'(lt_trans hj hi)) (π[k]'(lt_trans hk hi)) π[i])

/-- A weak DAG resolution refutation of `φ` is a weak DAG resolution proof from `φ` that derives
the empty clause `∅`. -/
def IsWeakDAGRefutation {n : ℕ} (φ : CNF n) (π : List (Clause n)) : Prop :=
  IsWeakDAGProof φ π ∧ ∅ ∈ π

/-- Every standard DAG resolution proof is a weak DAG resolution proof. -/
lemma IsDAGProof.toWeak {n : ℕ} {φ : CNF n} {π : List (Clause n)}
    (h : IsDAGProof φ π) : IsWeakDAGProof φ π := by
  intro i hi
  rcases h i hi with hax | hres
  · exact Or.inl hax
  · exact Or.inr (Or.inr hres)

/-- Every standard DAG resolution refutation is a weak DAG resolution refutation. -/
lemma IsDAGRefutation.toWeak {n : ℕ} {φ : CNF n} {π : List (Clause n)}
    (h : IsDAGRefutation φ π) : IsWeakDAGRefutation φ π :=
  ⟨IsDAGProof.toWeak h.1, h.2⟩

/-- A single valid step extending a weak DAG proof `prev` by a clause `c`. -/
def IsWeakStep {n : ℕ} (φ : CNF n) (prev : List (Clause n)) (c : Clause n) : Prop :=
  c ∈ φ ∨
    (∃ d ∈ prev, d ⊆ c) ∨
    (∃ c₁ ∈ prev, ∃ c₂ ∈ prev, IsResolvent c₁ c₂ c)

/-- The empty list is a valid weak DAG proof. -/
lemma isWeakDAGProof_nil {n : ℕ} (φ : CNF n) : IsWeakDAGProof φ [] := by
  intro i hi
  simp at hi

/-- Appending a single clause `c` to `π` yields a weak DAG proof if and only if `π` is a weak DAG
proof and `c` is a valid weak step from `φ` and `π`. -/
lemma isWeakDAGProof_append_singleton {n : ℕ} {φ : CNF n} {π : List (Clause n)} {c : Clause n} :
    IsWeakDAGProof φ (π ++ [c]) ↔ IsWeakDAGProof φ π ∧ IsWeakStep φ π c := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' : i < (π ++ [c]).length := by simp; omega
      have hstep := h i hi'
      simp only [List.getElem_append_left hi] at hstep
      rcases hstep with hax | ⟨j, hj, hsub⟩ | ⟨j, k, hj, hk, hres⟩
      · exact Or.inl hax
      · refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
        simpa [List.getElem_append_left (lt_trans hj hi)] using hsub
      · refine Or.inr (Or.inr ⟨j, k, hj, hk, ?_⟩)
        simpa [List.getElem_append_left (lt_trans hj hi),
          List.getElem_append_left (lt_trans hk hi)] using hres
    · have hi' : π.length < (π ++ [c]).length := by simp
      have hstep := h π.length hi'
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
        at hstep
      rcases hstep with hax | ⟨j, hj, hsub⟩ | ⟨j, k, hj, hk, hres⟩
      · exact Or.inl hax
      · refine Or.inr (Or.inl ⟨π[j]'hj, List.getElem_mem hj, ?_⟩)
        simpa [List.getElem_append_left hj] using hsub
      · refine Or.inr (Or.inr
          ⟨π[j]'hj, List.getElem_mem hj, π[k]'hk, List.getElem_mem hk, ?_⟩)
        simpa [List.getElem_append_left hj, List.getElem_append_left hk] using hres
  · rintro ⟨hπ, hc⟩ i hi
    have hlen : (π ++ [c]).length = π.length + 1 := by simp
    by_cases hlt : i < π.length
    · simp only [List.getElem_append_left hlt]
      rcases hπ i hlt with hax | ⟨j, hj, hsub⟩ | ⟨j, k, hj, hk, hres⟩
      · exact Or.inl hax
      · refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
        simpa [List.getElem_append_left (lt_trans hj hlt)] using hsub
      · refine Or.inr (Or.inr ⟨j, k, hj, hk, ?_⟩)
        simpa [List.getElem_append_left (lt_trans hj hlt),
          List.getElem_append_left (lt_trans hk hlt)] using hres
    · have heq : i = π.length := by omega
      subst heq
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      rcases hc with hax | ⟨d, hd, hsub⟩ | ⟨c₁, hc₁, c₂, hc₂, hres⟩
      · exact Or.inl hax
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
        refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
        simpa [List.getElem_append_left hj] using hsub
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc₁
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc₂
        refine Or.inr (Or.inr ⟨j, k, hj, hk, ?_⟩)
        simpa [List.getElem_append_left hj, List.getElem_append_left hk] using hres

/-- Helper lemma: width of `π ++ [c]` is the maximum of `dagWidth π` and `c.card`. -/
lemma dagWidth_append_singleton {n : ℕ} (π : List (Clause n)) (c : Clause n) :
    dagWidth (π ++ [c]) = max (dagWidth π) c.card := by
  induction π with
  | nil => simp
  | cons d tl ih =>
    simp only [List.cons_append, dagWidth_cons, ih]
    omega

/-! ### Single-literal restriction of a DAG proof -/

/-- Restricting a DAG resolution proof `π` by setting the literal `l` to `true`:
clauses containing `l` are deleted, and `l.neg` is erased from all remaining clauses. -/
def restrictDAGProof {n : ℕ} (l : Lit n) (π : List (Clause n)) : List (Clause n) :=
  (π.filter (fun c => decide (l ∉ c))).map (fun c => c.erase l.neg)

lemma mem_restrictDAGProof {n : ℕ} {l : Lit n} {π : List (Clause n)} {c : Clause n} :
    c ∈ restrictDAGProof l π ↔ ∃ d ∈ π, l ∉ d ∧ d.erase l.neg = c := by
  simp only [restrictDAGProof, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨d, ⟨hd, hnd⟩, rfl⟩
    exact ⟨d, hd, hnd, rfl⟩
  · rintro ⟨d, hd, hnd, rfl⟩
    exact ⟨d, ⟨hd, hnd⟩, rfl⟩

lemma restrictDAGProof_nil {n : ℕ} (l : Lit n) :
    restrictDAGProof l ([] : List (Clause n)) = [] := rfl

lemma restrictDAGProof_append_singleton {n : ℕ} (l : Lit n) (π : List (Clause n))
    (c : Clause n) :
    restrictDAGProof l (π ++ [c]) =
      if l ∉ c then restrictDAGProof l π ++ [c.erase l.neg] else restrictDAGProof l π := by
  by_cases h : l ∉ c <;> simp [restrictDAGProof, h]

lemma restrictDAGProof_append_singleton_of_notMem {n : ℕ} {l : Lit n} {π : List (Clause n)}
    {c : Clause n} (hnl : l ∉ c) :
    restrictDAGProof l (π ++ [c]) = restrictDAGProof l π ++ [c.erase l.neg] := by
  simp [restrictDAGProof, hnl]

lemma restrictDAGProof_append_singleton_of_mem {n : ℕ} {l : Lit n} {π : List (Clause n)}
    {c : Clause n} (hl : l ∈ c) :
    restrictDAGProof l (π ++ [c]) = restrictDAGProof l π := by
  simp [restrictDAGProof, hl]

/-- Restricting a weak DAG proof from `φ` by a literal `l` produces a valid weak DAG proof from
`restrictCNF l φ`. -/
theorem restrictDAGProof_isProof {n : ℕ} {φ : CNF n} (l : Lit n) :
    ∀ {π : List (Clause n)}, IsWeakDAGProof φ π →
      IsWeakDAGProof (restrictCNF l φ) (restrictDAGProof l π) := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
    intro _
    rw [restrictDAGProof_nil]
    exact isWeakDAGProof_nil _
  | append_singleton π c ih =>
    intro h
    obtain ⟨hπ, hc⟩ := isWeakDAGProof_append_singleton.mp h
    have ih' := ih hπ
    by_cases hnl : l ∉ c
    · rw [restrictDAGProof_append_singleton_of_notMem hnl, isWeakDAGProof_append_singleton]
      refine ⟨ih', ?_⟩
      rcases hc with hax | ⟨d, hd, hsub⟩ | ⟨c₁, hc₁, c₂, hc₂, v, h₁, h₂, rfl⟩
      · exact Or.inl (mem_restrictCNF.mpr ⟨c, hax, hnl, rfl⟩)
      · have hnd : l ∉ d := fun hmem => hnl (hsub hmem)
        refine Or.inr (Or.inl ⟨d.erase l.neg,
          mem_restrictDAGProof.mpr ⟨d, hd, hnd, rfl⟩, Finset.erase_subset_erase _ hsub⟩)
      · by_cases hv : v = l.var
        · rcases l with ⟨vl, pol⟩
          dsimp only at hv
          subst hv
          cases pol
          · -- `l = ⟨v, false⟩`, `l.neg = ⟨v, true⟩`: keep `c₁.erase ⟨v, true⟩`
            have hnl₁ : Lit.mk v false ∉ c₁ := fun hmem =>
              hnl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
            refine Or.inr (Or.inl ⟨c₁.erase (Lit.mk v false).neg,
              mem_restrictDAGProof.mpr ⟨c₁, hc₁, hnl₁, rfl⟩, ?_⟩)
            intro x hx
            rw [Lit.mk_false_neg] at hx ⊢
            obtain ⟨hxne, hxc₁⟩ := Finset.mem_erase.mp hx
            exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨hxne, hxc₁⟩)⟩
          · -- `l = ⟨v, true⟩`, `l.neg = ⟨v, false⟩`: keep `c₂.erase ⟨v, false⟩`
            have hnl₂ : Lit.mk v true ∉ c₂ := fun hmem =>
              hnl (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
            refine Or.inr (Or.inl ⟨c₂.erase (Lit.mk v true).neg,
              mem_restrictDAGProof.mpr ⟨c₂, hc₂, hnl₂, rfl⟩, ?_⟩)
            intro x hx
            rw [Lit.mk_true_neg] at hx ⊢
            obtain ⟨hxne, hxc₂⟩ := Finset.mem_erase.mp hx
            exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_union_right _
              (Finset.mem_erase.mpr ⟨hxne, hxc₂⟩)⟩
        · -- `v ≠ l.var`: resolve `c₁.erase l.neg` and `c₂.erase l.neg` on `v`
          have hne_pos : l ≠ Lit.mk v true := fun heq => hv (congrArg Lit.var heq).symm
          have hne_neg : l ≠ Lit.mk v false := fun heq => hv (congrArg Lit.var heq).symm
          have hneg_pos : Lit.mk v true ≠ l.neg := fun heq =>
            hv (by simpa [Lit.neg] using congrArg Lit.var heq)
          have hneg_neg : Lit.mk v false ≠ l.neg := fun heq =>
            hv (by simpa [Lit.neg] using congrArg Lit.var heq)
          have hnl₁ : l ∉ c₁ := fun hmem =>
            hnl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_pos, hmem⟩))
          have hnl₂ : l ∉ c₂ := fun hmem =>
            hnl (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_neg, hmem⟩))
          refine Or.inr (Or.inr ⟨c₁.erase l.neg,
            mem_restrictDAGProof.mpr ⟨c₁, hc₁, hnl₁, rfl⟩,
            c₂.erase l.neg,
            mem_restrictDAGProof.mpr ⟨c₂, hc₂, hnl₂, rfl⟩,
            v, Finset.mem_erase.mpr ⟨hneg_pos, h₁⟩,
            Finset.mem_erase.mpr ⟨hneg_neg, h₂⟩, ?_⟩)
          ext x
          simp only [Finset.mem_erase, Finset.mem_union]
          tauto
    · rw [restrictDAGProof_append_singleton_of_mem (Classical.not_not.mp hnl)]
      exact ih'

/-- Restricting a weak DAG refutation of `φ` by a literal `l` produces a weak DAG refutation of
`restrictCNF l φ`. -/
theorem restrictDAGProof_isRefutation {n : ℕ} {φ : CNF n} (l : Lit n) {π : List (Clause n)}
    (h : IsWeakDAGRefutation φ π) :
    IsWeakDAGRefutation (restrictCNF l φ) (restrictDAGProof l π) :=
  ⟨restrictDAGProof_isProof l h.1,
    mem_restrictDAGProof.mpr ⟨∅, h.2, Finset.notMem_empty l, Finset.erase_empty _⟩⟩

/-- Every fat clause (width `> k`) in `restrictDAGProof l π` arises from a fat clause of `π` that
does not contain `l`. -/
lemma card_fatClauses_restrictDAGProof_le {n k : ℕ} (l : Lit n) (π : List (Clause n)) :
    (fatClauses (restrictDAGProof l π).toFinset k).card ≤
      ((fatClauses π.toFinset k).filter (fun c => l ∉ c)).card := by
  have hsub :
      fatClauses (restrictDAGProof l π).toFinset k ⊆
        ((fatClauses π.toFinset k).filter (fun c => l ∉ c)).image (fun c => c.erase l.neg) := by
    intro c hc
    rw [mem_fatClauses, List.mem_toFinset, mem_restrictDAGProof] at hc
    obtain ⟨⟨d, hdπ, hnd, rfl⟩, hkcard⟩ := hc
    rw [Finset.mem_image]
    refine ⟨d, ?_, rfl⟩
    rw [Finset.mem_filter, mem_fatClauses, List.mem_toFinset]
    exact ⟨⟨hdπ, lt_of_lt_of_le hkcard Finset.card_erase_le⟩, hnd⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-! ### Lifting a weak DAG proof from `restrictCNF l φ` back to `φ` -/

/-- Inserting a fixed literal `a` into both premises and the conclusion preserves the resolution
relation `IsResolvent`. -/
private lemma isResolvent_insert {n : ℕ} {c₁ c₂ c : Clause n} (a : Lit n)
    (h : IsResolvent c₁ c₂ c) :
    IsResolvent (insert a c₁) (insert a c₂) (insert a c) := by
  obtain ⟨v, h₁, h₂, rfl⟩ := h
  refine ⟨v, Finset.mem_insert_of_mem h₁, Finset.mem_insert_of_mem h₂, ?_⟩
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
  have hpq : Lit.mk v true ≠ Lit.mk v false := by simp
  constructor
  · rintro (rfl | (⟨hxp, hxc₁⟩ | ⟨hxq, hxc₂⟩))
    · by_cases hx : x = Lit.mk v true
      · exact Or.inr ⟨fun h => hpq (hx.symm.trans h), Or.inl rfl⟩
      · exact Or.inl ⟨hx, Or.inl rfl⟩
    · exact Or.inl ⟨hxp, Or.inr hxc₁⟩
    · exact Or.inr ⟨hxq, Or.inr hxc₂⟩
  · rintro (⟨hxp, rfl | hxc₁⟩ | ⟨hxq, rfl | hxc₂⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hxp, hxc₁⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hxq, hxc₂⟩)

/-- Lifting helper: any weak DAG proof `π` from `restrictCNF l φ` lifts to a weak DAG proof `π'`
from `φ` containing `insert l.neg c` for every `c ∈ π`, with
`dagWidth π' ≤ dagWidth π + 1`. -/
private lemma liftDAGProof_aux {n : ℕ} {φ : CNF n} (l : Lit n) :
    ∀ (π : List (Clause n)), IsWeakDAGProof (restrictCNF l φ) π →
      ∃ π' : List (Clause n),
        IsWeakDAGProof φ π' ∧
        (∀ c ∈ π, insert l.neg c ∈ π') ∧
        dagWidth π' ≤ dagWidth π + 1 := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], isWeakDAGProof_nil φ, by simp, by simp⟩
  | append_singleton π c ih =>
    intro h
    obtain ⟨hπ, hc⟩ := isWeakDAGProof_append_singleton.mp h
    obtain ⟨π', hπ', hmem', hw'⟩ := ih hπ
    have hw_ins : (insert l.neg c).card ≤ c.card + 1 := Finset.card_insert_le _ _
    rcases hc with hax | ⟨d, hd, hsub⟩ | ⟨c₁, hc₁, c₂, hc₂, hres⟩
    · obtain ⟨d, hdφ, _, rfl⟩ := mem_restrictCNF.mp hax
      have hd_sub : d ⊆ insert l.neg (d.erase l.neg) := by
        intro x hx
        by_cases hxl : x = l.neg
        · exact hxl ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxl, hx⟩)
      have hd_card : d.card ≤ (d.erase l.neg).card + 1 := by
        by_cases hmem : l.neg ∈ d
        · have := Finset.card_erase_add_one hmem
          omega
        · rw [Finset.erase_eq_of_notMem hmem]
          exact Nat.le_succ _
      refine ⟨(π' ++ [d]) ++ [insert l.neg (d.erase l.neg)], ?_, ?_, ?_⟩
      · rw [isWeakDAGProof_append_singleton, isWeakDAGProof_append_singleton]
        refine ⟨⟨hπ', Or.inl hdφ⟩, Or.inr (Or.inl ⟨d, by simp, hd_sub⟩)⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (Or.inl (hmem' x hx))
        · exact Or.inr rfl
      · rw [dagWidth_append_singleton, dagWidth_append_singleton, dagWidth_append_singleton]
        omega
    · refine ⟨π' ++ [insert l.neg c], ?_, ?_, ?_⟩
      · rw [isWeakDAGProof_append_singleton]
        exact ⟨hπ', Or.inr (Or.inl ⟨insert l.neg d, hmem' d hd,
          Finset.insert_subset_insert l.neg hsub⟩)⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (hmem' x hx)
        · exact Or.inr rfl
      · rw [dagWidth_append_singleton, dagWidth_append_singleton]
        omega
    · refine ⟨π' ++ [insert l.neg c], ?_, ?_, ?_⟩
      · rw [isWeakDAGProof_append_singleton]
        exact ⟨hπ', Or.inr (Or.inr ⟨insert l.neg c₁, hmem' c₁ hc₁,
          insert l.neg c₂, hmem' c₂ hc₂, isResolvent_insert l.neg hres⟩)⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (hmem' x hx)
        · exact Or.inr rfl
      · rw [dagWidth_append_singleton, dagWidth_append_singleton]
        omega

/-- **DAG Proof Lifting Lemma**: Any weak DAG refutation `π` of `restrictCNF l φ` of width at most
`W` lifts to a weak DAG proof `π'` from `φ` deriving the unit clause `{l.neg}` of width at most
`W + 1`. -/
theorem liftDAGProof {n W : ℕ} {φ : CNF n} (l : Lit n) {π : List (Clause n)}
    (hπ : IsWeakDAGRefutation (restrictCNF l φ) π) (hw : dagWidth π ≤ W) :
    ∃ π' : List (Clause n),
      IsWeakDAGProof φ π' ∧ {l.neg} ∈ π' ∧ dagWidth π' ≤ W + 1 := by
  obtain ⟨π', hπ', hmem', hw'⟩ := liftDAGProof_aux l π hπ.1
  have hunit : ({l.neg} : Clause n) ∈ π' := by
    simpa using hmem' ∅ hπ.2
  exact ⟨π', hπ', hunit, by omega⟩

/-! ### Combining a unit-clause derivation with a restricted refutation -/

/-- Resolving a clause `d` containing `l.neg` with the unit clause `{l}` gives `d.erase l.neg`. -/
private lemma isResolvent_unit_erase {n : ℕ} {l : Lit n} {d : Clause n} (hmem : l.neg ∈ d) :
    IsResolvent {l} d (d.erase l.neg) ∨ IsResolvent d {l} (d.erase l.neg) := by
  rcases l with ⟨v, pol⟩
  cases pol
  · refine Or.inr ⟨v, hmem, Finset.mem_singleton_self _, ?_⟩
    simp [Lit.neg]
  · refine Or.inl ⟨v, Finset.mem_singleton_self _, hmem, ?_⟩
    simp [Lit.neg]

/-- Auxiliary substitution lemma for combining a weak DAG proof containing `{l}` with a weak DAG
proof from `restrictCNF l φ`. -/
private lemma combineDAGWithUnit_aux {n W : ℕ} {φ : CNF n} {l : Lit n}
    (hφ : ∀ c ∈ φ, c.card ≤ W)
    {π₁ : List (Clause n)} (hπ₁ : IsWeakDAGProof φ π₁) (hunit : {l} ∈ π₁)
    (hw₁ : dagWidth π₁ ≤ W) :
    ∀ (π₂ : List (Clause n)),
      IsWeakDAGProof (restrictCNF l φ) π₂ → dagWidth π₂ ≤ W →
      ∃ π : List (Clause n),
        IsWeakDAGProof φ π ∧
        {l} ∈ π ∧
        (∀ c ∈ π₂, c ∈ π) ∧
        dagWidth π ≤ W := by
  intro π₂
  induction π₂ using List.reverseRecOn with
  | nil =>
    intro _ _
    exact ⟨π₁, hπ₁, hunit, by simp, hw₁⟩
  | append_singleton π₂ c ih =>
    intro h hw₂
    obtain ⟨hπ₂, hc⟩ := isWeakDAGProof_append_singleton.mp h
    rw [dagWidth_append_singleton] at hw₂
    have hw₂' : dagWidth π₂ ≤ W := le_trans (le_max_left _ _) hw₂
    have hcw : c.card ≤ W := le_trans (le_max_right _ _) hw₂
    obtain ⟨π, hπ, hunit', hmem', hw⟩ := ih hπ₂ hw₂'
    rcases hc with hax | ⟨d, hd, hsub⟩ | ⟨c₁, hc₁, c₂, hc₂, hres⟩
    · obtain ⟨d, hdφ, _, rfl⟩ := mem_restrictCNF.mp hax
      by_cases hmem : l.neg ∈ d
      · refine ⟨(π ++ [d]) ++ [d.erase l.neg], ?_, ?_, ?_, ?_⟩
        · rw [isWeakDAGProof_append_singleton, isWeakDAGProof_append_singleton]
          refine ⟨⟨hπ, Or.inl hdφ⟩, ?_⟩
          rcases isResolvent_unit_erase hmem with hres | hres
          · exact Or.inr (Or.inr ⟨{l}, List.mem_append_left _ hunit', d, by simp, hres⟩)
          · exact Or.inr (Or.inr ⟨d, by simp, {l}, List.mem_append_left _ hunit', hres⟩)
        · exact List.mem_append_left _ (List.mem_append_left _ hunit')
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx ⊢
          rcases hx with hx | rfl
          · exact Or.inl (Or.inl (hmem' x hx))
          · exact Or.inr rfl
        · rw [dagWidth_append_singleton, dagWidth_append_singleton]
          have hdw : d.card ≤ W := hφ d hdφ
          omega
      · rw [Finset.erase_eq_of_notMem hmem]
        refine ⟨π ++ [d], ?_, ?_, ?_, ?_⟩
        · rw [isWeakDAGProof_append_singleton]
          exact ⟨hπ, Or.inl hdφ⟩
        · exact List.mem_append_left _ hunit'
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx ⊢
          rcases hx with hx | rfl
          · exact Or.inl (hmem' x hx)
          · exact Or.inr rfl
        · rw [dagWidth_append_singleton]
          have hdw : d.card ≤ W := hφ d hdφ
          omega
    · refine ⟨π ++ [c], ?_, ?_, ?_, ?_⟩
      · rw [isWeakDAGProof_append_singleton]
        exact ⟨hπ, Or.inr (Or.inl ⟨d, hmem' d hd, hsub⟩)⟩
      · exact List.mem_append_left _ hunit'
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (hmem' x hx)
        · exact Or.inr rfl
      · rw [dagWidth_append_singleton]
        omega
    · refine ⟨π ++ [c], ?_, ?_, ?_, ?_⟩
      · rw [isWeakDAGProof_append_singleton]
        exact ⟨hπ, Or.inr (Or.inr ⟨c₁, hmem' c₁ hc₁, c₂, hmem' c₂ hc₂, hres⟩)⟩
      · exact List.mem_append_left _ hunit'
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (hmem' x hx)
        · exact Or.inr rfl
      · rw [dagWidth_append_singleton]
        omega

/-- **Unit-Clause Combination Lemma**: Combining a weak DAG proof from `φ` deriving `{l}` of width
at most `W₁` with a weak DAG refutation of `restrictCNF l φ` of width at most `W₂` yields a
weak DAG refutation of `φ` of width at most `max W₁ W₂`, provided every clause of `φ` has
width at most `max W₁ W₂`. -/
theorem combineDAGWithUnit {n W₁ W₂ : ℕ} {φ : CNF n} {l : Lit n}
    (hφ : ∀ c ∈ φ, c.card ≤ max W₁ W₂)
    {π₁ π₂ : List (Clause n)}
    (hπ₁ : IsWeakDAGProof φ π₁) (hunit : {l} ∈ π₁) (hw₁ : dagWidth π₁ ≤ W₁)
    (hπ₂ : IsWeakDAGRefutation (restrictCNF l φ) π₂) (hw₂ : dagWidth π₂ ≤ W₂) :
    ∃ π : List (Clause n), IsWeakDAGRefutation φ π ∧ dagWidth π ≤ max W₁ W₂ := by
  obtain ⟨π, hπ, _, hmem, hw⟩ :=
    combineDAGWithUnit_aux hφ hπ₁ hunit (le_trans hw₁ (le_max_left _ _))
      π₂ hπ₂.1 (le_trans hw₂ (le_max_right _ _))
  exact ⟨π, ⟨hπ, hmem ∅ hπ₂.2⟩, hw⟩

/-! ### Active variables of a DAG proof -/

/-- The finite set of Boolean variables occurring in any clause of a DAG proof `π`. -/
def proofVars {n : ℕ} (π : List (Clause n)) : Finset (Fin n) :=
  π.toFinset.biUnion (fun c => c.image Lit.var)

lemma mem_proofVars {n : ℕ} {π : List (Clause n)} {v : Fin n} :
    v ∈ proofVars π ↔ ∃ c ∈ π, ∃ x ∈ c, x.var = v := by
  simp only [proofVars, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image]

/-- Restricting `π` by `l` cannot introduce new variables. -/
lemma proofVars_restrictDAGProof_subset {n : ℕ} (l : Lit n) (π : List (Clause n)) :
    proofVars (restrictDAGProof l π) ⊆ proofVars π := by
  intro v hv
  obtain ⟨c', hc', x, hx, rfl⟩ := mem_proofVars.mp hv
  obtain ⟨c, hc, _, rfl⟩ := mem_restrictDAGProof.mp hc'
  exact mem_proofVars.mpr ⟨c, hc, x, Finset.mem_of_mem_erase hx, rfl⟩

/-- The variable `l.var` does not appear in `restrictDAGProof l π`. -/
lemma var_not_mem_proofVars_restrictDAGProof {n : ℕ} (l : Lit n) (π : List (Clause n)) :
    l.var ∉ proofVars (restrictDAGProof l π) := by
  intro hv
  obtain ⟨c', hc', x, hx, hxv⟩ := mem_proofVars.mp hv
  obtain ⟨c, _, hnl, rfl⟩ := mem_restrictDAGProof.mp hc'
  obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
  cases hpol : x.pol == l.pol
  · have hxe : x = l.neg := by
      apply Lit.ext
      · exact hxv
      · cases hxpol : x.pol <;> cases hlpol : l.pol <;>
          simp [Lit.neg, hxpol, hlpol] at hpol ⊢
    exact hxne hxe
  · have hxe : x = l := by
      apply Lit.ext
      · exact hxv
      · exact eq_of_beq hpol
    exact hnl (hxe ▸ hxc)

/-- If a literal `l` occurs in some clause of `π`, then restricting `π` by `l.neg` strictly
reduces the number of variables occurring in the proof. -/
lemma card_proofVars_restrictDAGProof_lt {n : ℕ} {l : Lit n} {π : List (Clause n)}
    (hocc : ∃ c ∈ π, l ∈ c) :
    (proofVars (restrictDAGProof l.neg π)).card < (proofVars π).card := by
  have hsub := proofVars_restrictDAGProof_subset l.neg π
  have hmem : l.var ∈ proofVars π := by
    obtain ⟨c, hc, hl⟩ := hocc
    exact mem_proofVars.mpr ⟨c, hc, l, hl, rfl⟩
  have hnotmem : l.var ∉ proofVars (restrictDAGProof l.neg π) := by
    simpa [Lit.neg] using var_not_mem_proofVars_restrictDAGProof l.neg π
  exact Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨l.var, hmem, hnotmem⟩)

/-! ### Ben-Sasson–Wigderson (2001) General DAG Resolution Width–Size Tradeoff -/

/-- Core inductive version of the Ben-Sasson–Wigderson (2001) width–size tradeoff for general
DAG resolution with weakening. -/
theorem bsw_weak_dag_width_size_tradeoff {n k w₀ : ℕ}
    (hn : 0 < n) (hk_pos : 0 < k) (hk : k ≤ 2 * n) :
    ∀ (r : ℕ) (φ : CNF n), (∀ c ∈ φ, c.card ≤ w₀) →
      ∀ (π : List (Clause n)), IsWeakDAGRefutation φ π →
        (2 * n - k) ^ r * (fatClauses π.toFinset k).card < (2 * n) ^ r →
        ∃ π' : List (Clause n),
          IsWeakDAGRefutation φ π' ∧ dagWidth π' ≤ max w₀ k + r := by
  intro r
  induction r with
  | zero =>
    intro φ _ π hπ hbound
    simp only [Nat.pow_zero, Nat.one_mul] at hbound
    have hzero : (fatClauses π.toFinset k).card = 0 := by omega
    have hempty : fatClauses π.toFinset k = ∅ := Finset.card_eq_zero.mp hzero
    have hw : dagWidth π ≤ k := fatClauses_toFinset_eq_empty_iff.mp hempty
    exact ⟨π, hπ, le_trans hw (le_max_right w₀ k)⟩
  | succ r ih_r =>
    suffices h : ∀ (m : ℕ) (φ : CNF n), (∀ c ∈ φ, c.card ≤ w₀) →
        ∀ (π : List (Clause n)), IsWeakDAGRefutation φ π →
          (proofVars π).card = m →
          (2 * n - k) ^ (r + 1) * (fatClauses π.toFinset k).card < (2 * n) ^ (r + 1) →
          ∃ π' : List (Clause n),
            IsWeakDAGRefutation φ π' ∧ dagWidth π' ≤ max w₀ k + (r + 1) from
      fun φ hφ π hπ hbound => h (proofVars π).card φ hφ π hπ rfl hbound
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih_m =>
      intro φ hφ π hπ hvars hbound
      set B := fatClauses π.toFinset k with hB_def
      by_cases hb0 : B.card = 0
      · have hempty : B = ∅ := Finset.card_eq_zero.mp hb0
        have hw : dagWidth π ≤ k := fatClauses_toFinset_eq_empty_iff.mp hempty
        exact ⟨π, hπ, by omega⟩
      · have hb_pos : 0 < B.card := Nat.pos_of_ne_zero hb0
        have hB_width : ∀ c ∈ B, k ≤ c.card := fun c hc =>
          le_of_lt (mem_fatClauses.mp hc).2
        obtain ⟨l, hl_avg⟩ := exists_popular_lit_in_fatClauses hn B hB_width
        -- Branch 1: restrict by `l`, reducing the fat-clause bound to level `r`.
        have hshrink : 2 * n * (B.filter (fun c => l ∉ c)).card ≤ (2 * n - k) * B.card :=
          restrict_shrinks_fatClauses hk B l hl_avg
        have hπ₁_ref : IsWeakDAGRefutation (restrictCNF l φ) (restrictDAGProof l π) :=
          restrictDAGProof_isRefutation l hπ
        have hb₁_le :
            (fatClauses (restrictDAGProof l π).toFinset k).card ≤
              (B.filter (fun c => l ∉ c)).card :=
          card_fatClauses_restrictDAGProof_le l π
        have hmul₁ :
            2 * n * ((2 * n - k) ^ r * (fatClauses (restrictDAGProof l π).toFinset k).card) <
              2 * n * (2 * n) ^ r := by
          calc
            2 * n * ((2 * n - k) ^ r * (fatClauses (restrictDAGProof l π).toFinset k).card)
                = (2 * n - k) ^ r *
                    (2 * n * (fatClauses (restrictDAGProof l π).toFinset k).card) := by
                  rw [← Nat.mul_assoc, Nat.mul_comm (2 * n), Nat.mul_assoc]
            _ ≤ (2 * n - k) ^ r * (2 * n * (B.filter (fun c => l ∉ c)).card) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb₁_le)
            _ ≤ (2 * n - k) ^ r * ((2 * n - k) * B.card) :=
                  Nat.mul_le_mul_left _ hshrink
            _ = (2 * n - k) ^ (r + 1) * B.card := by
                  rw [← Nat.mul_assoc, ← Nat.pow_succ]
            _ < (2 * n) ^ (r + 1) := hbound
            _ = 2 * n * (2 * n) ^ r := by
                  rw [Nat.pow_succ, Nat.mul_comm]
        have hbound₁ :
            (2 * n - k) ^ r * (fatClauses (restrictDAGProof l π).toFinset k).card <
              (2 * n) ^ r :=
          Nat.lt_of_mul_lt_mul_left hmul₁
        obtain ⟨σ₁, hσ₁_ref, hσ₁_w⟩ :=
          ih_r (restrictCNF l φ) (restrictCNF_width_le hφ)
            (restrictDAGProof l π) hπ₁_ref hbound₁
        obtain ⟨σ₁', hσ₁'_proof, hσ₁'_unit, hσ₁'_w⟩ :=
          liftDAGProof l hσ₁_ref hσ₁_w
        -- Branch 2: restrict by `l.neg`, strictly reducing the number of proof variables.
        have hocc_pos : 0 < (B.filter (fun c => l ∈ c)).card := by
          have hpos : 0 < k * B.card := Nat.mul_pos hk_pos hb_pos
          have hmul_pos : 0 < 2 * n * (B.filter (fun c => l ∈ c)).card :=
            lt_of_lt_of_le hpos hl_avg
          exact Nat.pos_of_mul_pos_left hmul_pos
        obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hocc_pos
        have hc₀_mem : c₀ ∈ π ∧ l ∈ c₀ := by
          rw [Finset.mem_filter, hB_def, mem_fatClauses, List.mem_toFinset] at hc₀
          exact ⟨hc₀.1.1, hc₀.2⟩
        have hvars_lt : (proofVars (restrictDAGProof l.neg π)).card < m :=
          hvars ▸ card_proofVars_restrictDAGProof_lt ⟨c₀, hc₀_mem.1, hc₀_mem.2⟩
        have hπ₂_ref : IsWeakDAGRefutation (restrictCNF l.neg φ) (restrictDAGProof l.neg π) :=
          restrictDAGProof_isRefutation l.neg hπ
        have hb₂_le : (fatClauses (restrictDAGProof l.neg π).toFinset k).card ≤ B.card :=
          le_trans (card_fatClauses_restrictDAGProof_le l.neg π) (Finset.card_filter_le _ _)
        have hbound₂ :
            (2 * n - k) ^ (r + 1) * (fatClauses (restrictDAGProof l.neg π).toFinset k).card <
              (2 * n) ^ (r + 1) :=
          lt_of_le_of_lt (Nat.mul_le_mul_left _ hb₂_le) hbound
        obtain ⟨σ₂, hσ₂_ref, hσ₂_w⟩ :=
          ih_m (proofVars (restrictDAGProof l.neg π)).card hvars_lt
            (restrictCNF l.neg φ) (restrictCNF_width_le hφ)
            (restrictDAGProof l.neg π) hπ₂_ref rfl hbound₂
        -- Combine the unit derivation `{l.neg}` with the refutation of `restrictCNF l.neg φ`.
        have hφ_w :
            ∀ c ∈ φ, c.card ≤ max (max w₀ k + (r + 1)) (max w₀ k + (r + 1)) := by
          intro c hc
          have := hφ c hc
          omega
        obtain ⟨σ, hσ_ref, hσ_w⟩ :=
          combineDAGWithUnit hφ_w hσ₁'_proof hσ₁'_unit hσ₁'_w hσ₂_ref hσ₂_w
        exact ⟨σ, hσ_ref, by simpa using hσ_w⟩

/-- **Ben-Sasson–Wigderson (2001) General DAG Resolution Width–Size Tradeoff**:
Let `0 < n` and `0 < k ≤ 2 * n`. Suppose every clause in `φ` has width at most `w₀` and `φ`
has a general DAG resolution refutation `π` whose number of fat clauses
`b := (fatClauses π.toFinset k).card` satisfies `(2 * n - k) ^ r * b < (2 * n) ^ r`. Then `φ`
has a general DAG resolution refutation (with weakening) of width at most `max w₀ k + r`. -/
theorem bsw_dag_width_size_tradeoff {n k w₀ r : ℕ}
    (hn : 0 < n) (hk_pos : 0 < k) (hk : k ≤ 2 * n)
    (φ : CNF n) (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (π : List (Clause n)) (hπ : IsDAGRefutation φ π)
    (hbound : (2 * n - k) ^ r * (fatClauses π.toFinset k).card < (2 * n) ^ r) :
    ∃ π' : List (Clause n),
      IsWeakDAGRefutation φ π' ∧ dagWidth π' ≤ max w₀ k + r :=
  bsw_weak_dag_width_size_tradeoff hn hk_pos hk r φ hφ π (IsDAGRefutation.toWeak hπ) hbound

/-- **Exponential Size Lower Bound for General DAG Resolution** (Corollary of Ben-Sasson–Wigderson
2001): If every clause in `φ` has width at most `w₀` and every general DAG resolution refutation
(with weakening) of `φ` has width strictly greater than `max w₀ k + r`, then every general DAG
resolution refutation `π` of `φ` satisfies the exponential size lower bound
`(2 * n) ^ r ≤ (2 * n - k) ^ r * dagSize π`. -/
theorem bsw_dag_size_lower_bound {n k w₀ r : ℕ}
    (hn : 0 < n) (hk_pos : 0 < k) (hk : k ≤ 2 * n)
    (φ : CNF n) (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (hwidth : ∀ π' : List (Clause n),
      IsWeakDAGRefutation φ π' → max w₀ k + r < dagWidth π')
    (π : List (Clause n)) (hπ : IsDAGRefutation φ π) :
    (2 * n) ^ r ≤ (2 * n - k) ^ r * dagSize π := by
  by_contra hlt
  have hlt' : (2 * n - k) ^ r * dagSize π < (2 * n) ^ r := Nat.lt_of_not_ge hlt
  have hfat_le : (fatClauses π.toFinset k).card ≤ dagSize π :=
    le_trans (Finset.card_filter_le _ _) (List.toFinset_card_le π)
  have hbound : (2 * n - k) ^ r * (fatClauses π.toFinset k).card < (2 * n) ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hfat_le) hlt'
  obtain ⟨π', hπ'_ref, hπ'_w⟩ :=
    bsw_dag_width_size_tradeoff hn hk_pos hk φ hφ π hπ hbound
  exact Nat.not_lt.mpr hπ'_w (hwidth π' hπ'_ref)

end Mathmatica.BSWDAGFull
