import Mathlib.Data.Finset.Card

/-!
# Ben-Sasson–Wigderson Tree-like Resolution Width–Size Tradeoff

This module formalizes the tree-like resolution width–size tradeoff theorem of Ben-Sasson and
Wigderson (2001), using duplicate-free clauses represented as `Finset (Lit n)`.

## Main definitions

* `Lit n`: A propositional literal over `n` Boolean variables (`var : Fin n`, `pol : Bool`),
  together with negation `Lit.neg`.
* `Clause n`: A propositional clause as a `Finset (Lit n)`.
* `CNF n`: A CNF formula as a `Finset (Clause n)`.
* `ResTree φ c`: A tree-like resolution derivation of `c` from `φ`.
* `ResTree.size`: The leaf-count size of a tree-like resolution proof.
* `ResTree.width`: The maximum clause cardinality appearing in a tree-like resolution proof.
* `restrictCNF l φ`: The restriction of `φ` obtained by setting the literal `l` to `true`.

## Main results

* `liftTree`: Lifting a resolution derivation from `restrictCNF l φ` back to `φ` increases width
  by at most `1`.
* `bsw_tree_width_size`: If every clause in `φ` has width at most `w₀` and `φ` has a tree-like
  resolution refutation of size at most `2 ^ d`, then `φ` has a tree-like resolution refutation
  of width at most `w₀ + d`.
* `bsw_tree_size_lower_bound`: If every tree-like resolution refutation of `φ` has width strictly
  greater than `w₀ + d`, then every tree-like resolution refutation of `φ` has size strictly
  greater than `2 ^ d`.

## References

* E. Ben-Sasson and A. Wigderson, *Short proofs are narrow — resolution made simple*,
  Journal of the ACM 48 (2001), no. 2, 149–169.
-/

namespace Mathmatica.BSWTradeoff

/-! ### Literals, clauses, and CNF formulas -/

/-- A propositional literal over `n` Boolean variables: a variable index together with a
polarity (`true` for positive, `false` for negative). -/
@[ext]
structure Lit (n : ℕ) where
  /-- The underlying variable index. -/
  var : Fin n
  /-- The polarity of the literal (`true` = positive, `false` = negative). -/
  pol : Bool
  deriving DecidableEq

namespace Lit

/-- Negation of a literal, flipping its polarity. -/
def neg {n : ℕ} (l : Lit n) : Lit n :=
  ⟨l.var, !l.pol⟩

@[simp]
lemma neg_neg {n : ℕ} (l : Lit n) : l.neg.neg = l := by
  cases l with
  | mk v p => simp [neg]

@[simp]
lemma neg_ne_self {n : ℕ} (l : Lit n) : l.neg ≠ l := by
  cases l with
  | mk v p =>
    intro h
    have hp : (!p) = p := congrArg Lit.pol h
    cases p <;> simp at hp

@[simp]
lemma self_ne_neg {n : ℕ} (l : Lit n) : l ≠ l.neg :=
  (neg_ne_self l).symm

lemma neg_eq_iff {n : ℕ} {l₁ l₂ : Lit n} : l₁.neg = l₂ ↔ l₁ = l₂.neg := by
  constructor
  · intro h; subst h; exact (neg_neg l₁).symm
  · intro h; subst h; exact neg_neg l₂

lemma mk_true_neg {n : ℕ} (v : Fin n) : (Lit.mk v true).neg = Lit.mk v false := rfl

lemma mk_false_neg {n : ℕ} (v : Fin n) : (Lit.mk v false).neg = Lit.mk v true := rfl

end Lit

/-- A propositional clause represented as a finite set of literals. -/
abbrev Clause (n : ℕ) := Finset (Lit n)

/-- A CNF formula represented as a finite set of clauses. -/
abbrev CNF (n : ℕ) := Finset (Clause n)

/-! ### Tree-like resolution proofs -/

/-- A tree-like resolution proof deriving a clause `c` from a CNF formula `φ`. -/
inductive ResTree {n : ℕ} (φ : CNF n) : Clause n → Type
  | axiom_clause {c : Clause n} (hc : c ∈ φ) : ResTree φ c
  | resolve {c₁ c₂ : Clause n} (v : Fin n)
      (h₁ : Lit.mk v true ∈ c₁) (h₂ : Lit.mk v false ∈ c₂)
      (t₁ : ResTree φ c₁) (t₂ : ResTree φ c₂) :
      ResTree φ ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)))

namespace ResTree

/-- The size of a tree-like resolution proof, measured as the number of leaves. -/
def size {n : ℕ} {φ : CNF n} : ∀ {c : Clause n}, ResTree φ c → ℕ
  | _, axiom_clause _ => 1
  | _, resolve _ _ _ t₁ t₂ => t₁.size + t₂.size

/-- The width of a tree-like resolution proof, defined as the maximum cardinality of any clause
occurring in the proof tree. -/
def width {n : ℕ} {φ : CNF n} : ∀ {c : Clause n}, ResTree φ c → ℕ
  | c, axiom_clause _ => c.card
  | _, @resolve _ _ c₁ c₂ v _ _ t₁ t₂ =>
    max ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))).card
      (max t₁.width t₂.width)

/-- Every tree-like resolution proof has positive size. -/
lemma size_pos {n : ℕ} {φ : CNF n} : ∀ {c : Clause n} (t : ResTree φ c), 0 < t.size
  | _, axiom_clause _ => Nat.zero_lt_one
  | _, resolve _ _ _ t₁ t₂ => Nat.add_pos_left (size_pos t₁) t₂.size

/-- The cardinality of the derived clause is at most the width of the proof. -/
lemma card_le_width {n : ℕ} {φ : CNF n} :
    ∀ {c : Clause n} (t : ResTree φ c), c.card ≤ t.width
  | _, axiom_clause _ => le_rfl
  | _, resolve _ _ _ _ _ => le_max_left _ _

/-- Transporting a resolution tree along an equality of clauses preserves its width. -/
lemma width_cast {n : ℕ} {φ : CNF n} {c₁ c₂ : Clause n}
    (h : c₁ = c₂) (t : ResTree φ c₁) :
    (h ▸ t).width = t.width := by
  subst h
  rfl

end ResTree

/-! ### Single-literal restriction -/

/-- The restriction of a CNF formula `φ` by setting the literal `l` to `true`:
clauses containing `l` are satisfied and deleted, while `l.neg` is removed from all remaining
clauses. -/
def restrictCNF {n : ℕ} (l : Lit n) (φ : CNF n) : CNF n :=
  (φ.filter (fun c => l ∉ c)).image (fun c => c.erase l.neg)

lemma mem_restrictCNF {n : ℕ} {l : Lit n} {φ : CNF n} {c : Clause n} :
    c ∈ restrictCNF l φ ↔ ∃ d ∈ φ, l ∉ d ∧ d.erase l.neg = c := by
  simp only [restrictCNF, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨d, ⟨hd, hnd⟩, rfl⟩
    exact ⟨d, hd, hnd, rfl⟩
  · rintro ⟨d, hd, hnd, rfl⟩
    exact ⟨d, ⟨hd, hnd⟩, rfl⟩

/-- Restricting a CNF formula does not increase its maximum clause width. -/
lemma restrictCNF_width_le {n : ℕ} {l : Lit n} {φ : CNF n} {w₀ : ℕ}
    (hφ : ∀ c ∈ φ, c.card ≤ w₀) :
    ∀ c ∈ restrictCNF l φ, c.card ≤ w₀ := by
  intro c hc
  obtain ⟨d, hd, _, rfl⟩ := mem_restrictCNF.mp hc
  exact le_trans (Finset.card_erase_le) (hφ d hd)

/-- No clause derived from `restrictCNF l φ` contains `l.neg`. -/
lemma not_mem_neg_of_restrictCNF {n : ℕ} {l : Lit n} {φ : CNF n} :
    ∀ {c : Clause n}, ResTree (restrictCNF l φ) c → l.neg ∉ c
  | _, ResTree.axiom_clause hc => by
    obtain ⟨d, _, _, rfl⟩ := mem_restrictCNF.mp hc
    exact Finset.notMem_erase l.neg d
  | _, ResTree.resolve _ _ _ t₁ t₂ => by
    have h₁ := not_mem_neg_of_restrictCNF t₁
    have h₂ := not_mem_neg_of_restrictCNF t₂
    simp only [Finset.mem_union, not_or]
    exact ⟨fun h => h₁ (Finset.mem_of_mem_erase h), fun h => h₂ (Finset.mem_of_mem_erase h)⟩

/-! ### Restricting, lifting, and substituting resolution trees -/

/-- Restricting a tree-like resolution proof of `c` (with `l ∉ c`) by setting `l` to `true`
yields a proof from `restrictCNF l φ` of a subclause of `c.erase l.neg`, without increasing
proof size. -/
theorem restrictTree {n : ℕ} {φ : CNF n} (l : Lit n) :
    ∀ {c : Clause n} (t : ResTree φ c), l ∉ c →
      ∃ c' : Clause n, c' ⊆ c.erase l.neg ∧
        ∃ t' : ResTree (restrictCNF l φ) c', t'.size ≤ t.size
  | c, ResTree.axiom_clause hc, hnl =>
    ⟨c.erase l.neg, Finset.Subset.refl _,
      ResTree.axiom_clause (mem_restrictCNF.mpr ⟨c, hc, hnl, rfl⟩), le_rfl⟩
  | _, @ResTree.resolve _ _ c₁ c₂ v h₁ h₂ t₁ t₂, hnl => by
    by_cases hv : v = l.var
    · -- Resolution variable equals `l.var`: one premise contains `l`, the other `l.neg`.
      rcases l with ⟨vl, pol⟩
      dsimp only at hv
      subst hv
      cases pol
      · -- `l = ⟨v, false⟩`, `l.neg = ⟨v, true⟩`: keep the `t₁` branch.
        have hnl₁ : Lit.mk v false ∉ c₁ := by
          intro hmem
          apply hnl
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
        obtain ⟨c₁', hc₁'sub, t₁', ht₁'size⟩ :=
          restrictTree (Lit.mk v false) t₁ hnl₁
        refine ⟨c₁', ?_, t₁', ?_⟩
        · intro x hx
          have hx' := hc₁'sub hx
          rw [Lit.mk_false_neg] at hx'
          obtain ⟨hxne, hxc₁⟩ := Finset.mem_erase.mp hx'
          rw [Lit.mk_false_neg]
          exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hxne, hxc₁⟩)⟩
        · exact le_trans ht₁'size (Nat.le_add_right _ _)
      · -- `l = ⟨v, true⟩`, `l.neg = ⟨v, false⟩`: keep the `t₂` branch.
        have hnl₂ : Lit.mk v true ∉ c₂ := by
          intro hmem
          apply hnl
          exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
        obtain ⟨c₂', hc₂'sub, t₂', ht₂'size⟩ := restrictTree (Lit.mk v true) t₂ hnl₂
        refine ⟨c₂', ?_, t₂', ?_⟩
        · intro x hx
          have hx' := hc₂'sub hx
          rw [Lit.mk_true_neg] at hx'
          obtain ⟨hxne, hxc₂⟩ := Finset.mem_erase.mp hx'
          rw [Lit.mk_true_neg]
          exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨hxne, hxc₂⟩)⟩
        · exact le_trans ht₂'size (Nat.le_add_left _ _)
    · -- Resolution variable differs from `l.var`: restrict both premises.
      have hne_pos : l ≠ Lit.mk v true := fun h => hv (congrArg Lit.var h).symm
      have hne_neg : l ≠ Lit.mk v false := fun h => hv (congrArg Lit.var h).symm
      have hnl₁ : l ∉ c₁ := fun hmem =>
        hnl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_pos, hmem⟩))
      have hnl₂ : l ∉ c₂ := fun hmem =>
        hnl (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_neg, hmem⟩))
      obtain ⟨c₁', hc₁'sub, t₁', ht₁'size⟩ := restrictTree l t₁ hnl₁
      obtain ⟨c₂', hc₂'sub, t₂', ht₂'size⟩ := restrictTree l t₂ hnl₂
      by_cases hp : Lit.mk v true ∈ c₁'
      · by_cases hq : Lit.mk v false ∈ c₂'
        · refine ⟨(c₁'.erase (Lit.mk v true)) ∪ (c₂'.erase (Lit.mk v false)), ?_,
            ResTree.resolve v hp hq t₁' t₂', Nat.add_le_add ht₁'size ht₂'size⟩
          intro x hx
          rcases Finset.mem_union.mp hx with hx₁ | hx₂
          · obtain ⟨hxne, hxc₁'⟩ := Finset.mem_erase.mp hx₁
            obtain ⟨hxnl, hxc₁⟩ := Finset.mem_erase.mp (hc₁'sub hxc₁')
            exact Finset.mem_erase.mpr ⟨hxnl, Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨hxne, hxc₁⟩)⟩
          · obtain ⟨hxne, hxc₂'⟩ := Finset.mem_erase.mp hx₂
            obtain ⟨hxnl, hxc₂⟩ := Finset.mem_erase.mp (hc₂'sub hxc₂')
            exact Finset.mem_erase.mpr ⟨hxnl, Finset.mem_union_right _
              (Finset.mem_erase.mpr ⟨hxne, hxc₂⟩)⟩
        · refine ⟨c₂', ?_, t₂', le_trans ht₂'size (Nat.le_add_left _ _)⟩
          intro x hx
          have hxne : x ≠ Lit.mk v false := fun h => hq (h ▸ hx)
          obtain ⟨hxnl, hxc₂⟩ := Finset.mem_erase.mp (hc₂'sub hx)
          exact Finset.mem_erase.mpr ⟨hxnl, Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨hxne, hxc₂⟩)⟩
      · refine ⟨c₁', ?_, t₁', le_trans ht₁'size (Nat.le_add_right _ _)⟩
        intro x hx
        have hxne : x ≠ Lit.mk v true := fun h => hp (h ▸ hx)
        obtain ⟨hxnl, hxc₁⟩ := Finset.mem_erase.mp (hc₁'sub hx)
        exact Finset.mem_erase.mpr ⟨hxnl, Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hxne, hxc₁⟩)⟩

/-- Helper lemma: erasing an element `b ≠ a` commutes with inserting `a` into a `Finset`. -/
private lemma erase_insert_of_ne {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b)
    (s : Finset α) :
    (insert a s).erase b = insert a (s.erase b) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hxb, rfl | hxs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hxb, hxs⟩
  · rintro (rfl | ⟨hxb, hxs⟩)
    · exact ⟨h, Or.inl rfl⟩
    · exact ⟨hxb, Or.inr hxs⟩

/-- Lifting a tree-like resolution proof from `restrictCNF l φ` back to `φ`: any proof of `c`
of width `W` lifts to a proof of either `c` or `insert l.neg c` of width at most `W + 1`. -/
theorem liftTree {n : ℕ} {φ : CNF n} (l : Lit n) :
    ∀ {c : Clause n} (t : ResTree (restrictCNF l φ) c),
      ∃ c' : Clause n, (c' = c ∨ c' = insert l.neg c) ∧
        ∃ t' : ResTree φ c', t'.width ≤ t.width + 1
  | c, ResTree.axiom_clause hc => by
    obtain ⟨d, hd, _, rfl⟩ := mem_restrictCNF.mp hc
    by_cases hmem : l.neg ∈ d
    · refine ⟨d, Or.inr (Finset.insert_erase hmem).symm, ResTree.axiom_clause hd, ?_⟩
      change d.card ≤ (d.erase l.neg).card + 1
      have hcard := Finset.card_erase_add_one hmem
      omega
    · refine ⟨d, Or.inl (Finset.erase_eq_of_notMem hmem).symm, ResTree.axiom_clause hd, ?_⟩
      change d.card ≤ (d.erase l.neg).card + 1
      rw [Finset.erase_eq_of_notMem hmem]
      exact Nat.le_succ _
  | _, @ResTree.resolve _ _ c₁ c₂ v h₁ h₂ t₁ t₂ => by
    have hnl₁ : l.neg ∉ c₁ := not_mem_neg_of_restrictCNF t₁
    have hnl₂ : l.neg ∉ c₂ := not_mem_neg_of_restrictCNF t₂
    have hne₁ : l.neg ≠ Lit.mk v true := fun h => hnl₁ (h ▸ h₁)
    have hne₂ : l.neg ≠ Lit.mk v false := fun h => hnl₂ (h ▸ h₂)
    obtain ⟨c₁', hc₁', t₁', hw₁⟩ := liftTree l t₁
    obtain ⟨c₂', hc₂', t₂', hw₂⟩ := liftTree l t₂
    have h₁' : Lit.mk v true ∈ c₁' := by
      rcases hc₁' with rfl | rfl
      · exact h₁
      · exact Finset.mem_insert_of_mem h₁
    have h₂' : Lit.mk v false ∈ c₂' := by
      rcases hc₂' with rfl | rfl
      · exact h₂
      · exact Finset.mem_insert_of_mem h₂
    let c := (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))
    let c' := (c₁'.erase (Lit.mk v true)) ∪ (c₂'.erase (Lit.mk v false))
    have hc' : c' = c ∨ c' = insert l.neg c := by
      rcases hc₁' with rfl | rfl <;> rcases hc₂' with rfl | rfl
      · exact Or.inl rfl
      · refine Or.inr ?_
        simp only [c', c, erase_insert_of_ne hne₂, Finset.union_insert]
      · refine Or.inr ?_
        simp only [c', c, erase_insert_of_ne hne₁, Finset.insert_union]
      · refine Or.inr ?_
        simp only [c', c, erase_insert_of_ne hne₁, erase_insert_of_ne hne₂,
          Finset.insert_union, Finset.union_insert, Finset.insert_idem]
    refine ⟨c', hc', ResTree.resolve v h₁' h₂' t₁' t₂', ?_⟩
    have hcard : c'.card ≤ c.card + 1 := by
      rcases hc' with h | h
      · rw [h]; exact Nat.le_succ _
      · rw [h]; exact Finset.card_insert_le _ _
    change max c'.card (max t₁'.width t₂'.width) ≤
      max c.card (max t₁.width t₂.width) + 1
    omega

/-- Substituting a unit-clause derivation `u : ResTree φ {l}` into a proof from
`restrictCNF l φ` eliminates the restriction while preserving the derived clause and the
width bound `W`. -/
theorem substUnit {n : ℕ} {φ : CNF n} {l : Lit n} {W : ℕ}
    (hφ : ∀ c ∈ φ, c.card ≤ W)
    (u : ResTree φ {l}) (hu : u.width ≤ W) :
    ∀ {c : Clause n} (t : ResTree (restrictCNF l φ) c), t.width ≤ W →
      ∃ t' : ResTree φ c, t'.width ≤ W
  | c, ResTree.axiom_clause hc, _ => by
    obtain ⟨d, hd, _, rfl⟩ := mem_restrictCNF.mp hc
    by_cases hmem : l.neg ∈ d
    · rcases l with ⟨v, pol⟩
      cases pol
      · -- `l = ⟨v, false⟩`, `l.neg = ⟨v, true⟩`
        rw [Lit.mk_false_neg] at hmem ⊢
        have heq : (d.erase (Lit.mk v true)) ∪ ({Lit.mk v false} : Clause n).erase
            (Lit.mk v false) = d.erase (Lit.mk v true) := by
          simp
        refine ⟨heq ▸ ResTree.resolve v hmem (Finset.mem_singleton_self _)
          (ResTree.axiom_clause hd) u, ?_⟩
        rw [ResTree.width_cast]
        change max _ (max d.card u.width) ≤ W
        rw [heq]
        have hde : (d.erase (Lit.mk v true)).card ≤ d.card := Finset.card_erase_le
        have hdW : d.card ≤ W := hφ d hd
        omega
      · -- `l = ⟨v, true⟩`, `l.neg = ⟨v, false⟩`
        rw [Lit.mk_true_neg] at hmem ⊢
        have heq : ({Lit.mk v true} : Clause n).erase (Lit.mk v true) ∪
            (d.erase (Lit.mk v false)) = d.erase (Lit.mk v false) := by
          simp
        refine ⟨heq ▸ ResTree.resolve v (Finset.mem_singleton_self _) hmem
          u (ResTree.axiom_clause hd), ?_⟩
        rw [ResTree.width_cast]
        change max _ (max u.width d.card) ≤ W
        rw [heq]
        have hde : (d.erase (Lit.mk v false)).card ≤ d.card := Finset.card_erase_le
        have hdW : d.card ≤ W := hφ d hd
        omega
    · rw [Finset.erase_eq_of_notMem hmem]
      exact ⟨ResTree.axiom_clause hd, hφ d hd⟩
  | _, @ResTree.resolve _ _ c₁ c₂ v h₁ h₂ t₁ t₂, hW => by
    have hW₁ : t₁.width ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
    have hW₂ : t₂.width ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
    have hWc : ((c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false))).card ≤ W :=
      le_trans (le_max_left _ _) hW
    obtain ⟨t₁', ht₁'⟩ := substUnit hφ u hu t₁ hW₁
    obtain ⟨t₂', ht₂'⟩ := substUnit hφ u hu t₂ hW₂
    refine ⟨ResTree.resolve v h₁ h₂ t₁' t₂', ?_⟩
    change max _ (max t₁'.width t₂'.width) ≤ W
    omega

/-! ### Ben-Sasson–Wigderson Tree-like Width–Size Tradeoff -/

/-- Helper lemma: if `a ∈ c` and `c.erase a = ∅`, then `c = {a}`. -/
private lemma eq_singleton_of_erase_eq_empty {α : Type*} [DecidableEq α] {a : α} {c : Finset α}
    (ha : a ∈ c) (he : c.erase a = ∅) : c = {a} := by
  have := Finset.insert_erase ha
  rw [he] at this
  exact this.symm

/-- One branch of the inductive step in the Ben-Sasson–Wigderson proof. -/
private lemma bsw_step_branch {n : ℕ} {d w₀ m : ℕ} {φ : CNF n} {l : Lit n}
    (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (ih_d : ∀ (ψ : CNF n), (∀ c ∈ ψ, c.card ≤ w₀) →
      ∀ S : ResTree ψ ∅, S.size ≤ 2 ^ d → ∃ S' : ResTree ψ ∅, S'.width ≤ w₀ + d)
    (ih_m : ∀ k < m, ∀ (ψ : CNF n), (∀ c ∈ ψ, c.card ≤ w₀) →
      ∀ S : ResTree ψ ∅, S.size = k → S.size ≤ 2 ^ (d + 1) →
        ∃ S' : ResTree ψ ∅, S'.width ≤ w₀ + (d + 1))
    (tSmall : ResTree φ {l}) (hSmall : tSmall.size ≤ 2 ^ d)
    (tOther : ResTree φ {l.neg}) (hOther_lt : tOther.size < m)
    (hOther_le : tOther.size ≤ 2 ^ (d + 1)) :
    ∃ T' : ResTree φ ∅, T'.width ≤ w₀ + (d + 1) := by
  -- Step 1: Restrict `tSmall` by setting `l.neg` to `true`, yielding a refutation of size ≤ 2^d.
  have hnl : l.neg ∉ ({l} : Clause n) := by simp
  obtain ⟨c₁', hc₁'sub, tSmall_r, htSmall_r⟩ := restrictTree l.neg tSmall hnl
  have hc₁'empty : c₁' = ∅ := by
    rw [Lit.neg_neg, Finset.erase_singleton] at hc₁'sub
    exact Finset.subset_empty.mp hc₁'sub
  subst hc₁'empty
  -- Step 2: Apply the outer induction hypothesis (for `d`) to `tSmall_r`.
  obtain ⟨π₁, hπ₁⟩ := ih_d (restrictCNF l.neg φ) (restrictCNF_width_le hφ) tSmall_r
    (le_trans htSmall_r hSmall)
  -- Step 3: Lift `π₁` back to `φ` with width ≤ w₀ + d + 1.
  obtain ⟨c₁'', hc₁'', π₁', hπ₁'⟩ := liftTree l.neg π₁
  rw [Lit.neg_neg] at hc₁''
  change c₁'' = ∅ ∨ c₁'' = {l} at hc₁''
  rcases hc₁'' with rfl | rfl
  · -- `π₁'` already refutes `φ`.
    exact ⟨π₁', by omega⟩
  · -- `π₁'` derives `{l}` with width ≤ w₀ + (d + 1).
    -- Step 4: Restrict `tOther` by setting `l` to `true`, strictly decreasing size.
    have hnl' : l ∉ ({l.neg} : Clause n) := by simp
    obtain ⟨c₂', hc₂'sub, tOther_r, htOther_r⟩ := restrictTree l tOther hnl'
    have hc₂'empty : c₂' = ∅ := by
      rw [Finset.erase_singleton] at hc₂'sub
      exact Finset.subset_empty.mp hc₂'sub
    subst hc₂'empty
    -- Step 5: Apply the inner strong induction hypothesis to `tOther_r`.
    obtain ⟨π₂, hπ₂⟩ := ih_m tOther_r.size (lt_of_le_of_lt htOther_r hOther_lt)
      (restrictCNF l φ) (restrictCNF_width_le hφ) tOther_r rfl (le_trans htOther_r hOther_le)
    -- Step 6: Substitute `π₁' : ResTree φ {l}` into `π₂` without increasing width.
    exact substUnit (fun c hc => le_trans (hφ c hc) (Nat.le_add_right _ _))
      π₁' (by omega) π₂ hπ₂

/-- **Ben-Sasson–Wigderson (2001) Tree-like Resolution Width–Size Tradeoff**:
If every clause in `φ` has width at most `w₀` and `φ` admits a tree-like resolution refutation
of size at most `2 ^ d`, then `φ` admits a tree-like resolution refutation of width at most
`w₀ + d`. -/
theorem bsw_tree_width_size {n : ℕ} (d w₀ : ℕ) (φ : CNF n)
    (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (T : ResTree φ ∅) (hsize : T.size ≤ 2 ^ d) :
    ∃ T' : ResTree φ ∅, T'.width ≤ w₀ + d := by
  induction d generalizing φ with
  | zero =>
    generalize hc : (∅ : Clause n) = c at T
    cases T with
    | axiom_clause hc' =>
      subst hc
      exact ⟨ResTree.axiom_clause hc', by simp [ResTree.width]⟩
    | resolve v h₁ h₂ t₁ t₂ =>
      have h1 := ResTree.size_pos t₁
      have h2 := ResTree.size_pos t₂
      simp only [ResTree.size, Nat.pow_zero] at hsize
      omega
  | succ d ih_d =>
    suffices h : ∀ m (ψ : CNF n), (∀ c ∈ ψ, c.card ≤ w₀) →
        ∀ S : ResTree ψ ∅, S.size = m → S.size ≤ 2 ^ (d + 1) →
          ∃ S' : ResTree ψ ∅, S'.width ≤ w₀ + (d + 1) from
      h T.size φ hφ T rfl hsize
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih_m =>
      intro ψ hψ S hSm hSle
      generalize hc : (∅ : Clause n) = c at S
      cases S with
      | axiom_clause hc' =>
        subst hc
        exact ⟨ResTree.axiom_clause hc', by simp [ResTree.width]⟩
      | @resolve c₁ c₂ v h₁ h₂ t₁ t₂ =>
        have hunion :
            (c₁.erase (Lit.mk v true)) ∪ (c₂.erase (Lit.mk v false)) = ∅ := hc.symm
        rw [Finset.union_eq_empty] at hunion
        have hc₁ : c₁ = {Lit.mk v true} := eq_singleton_of_erase_eq_empty h₁ hunion.1
        have hc₂ : c₂ = {Lit.mk v false} := eq_singleton_of_erase_eq_empty h₂ hunion.2
        subst hc₁ hc₂
        have hpos₁ : 0 < t₁.size := ResTree.size_pos t₁
        have hpos₂ : 0 < t₂.size := ResTree.size_pos t₂
        have hsum : t₁.size + t₂.size = m := hSm
        have hpow : t₁.size + t₂.size ≤ 2 ^ d + 2 ^ d := by
          have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
          rw [← this]
          exact hSle
        have hlt₁ : t₁.size < m := by omega
        have hlt₂ : t₂.size < m := by omega
        have hle₁_all : t₁.size ≤ 2 ^ (d + 1) := by
          have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
          omega
        have hle₂_all : t₂.size ≤ 2 ^ (d + 1) := by
          have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
          omega
        rw [← hc]
        by_cases hle₁ : t₁.size ≤ 2 ^ d
        · exact bsw_step_branch (l := Lit.mk v true) hψ ih_d ih_m
            t₁ hle₁ t₂ hlt₂ hle₂_all
        · have hle₂ : t₂.size ≤ 2 ^ d := by omega
          exact bsw_step_branch (l := Lit.mk v false) hψ ih_d ih_m
            t₂ hle₂ t₁ hlt₁ hle₁_all

/-- **Exponential Tree-like Resolution Size Lower Bound** (Corollary of Ben-Sasson–Wigderson):
If every clause in `φ` has width at most `w₀` and every tree-like resolution refutation of `φ`
has width strictly greater than `w₀ + d`, then every tree-like resolution refutation of `φ`
has size strictly greater than `2 ^ d`. -/
theorem bsw_tree_size_lower_bound {n : ℕ} (d w₀ : ℕ) (φ : CNF n)
    (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (hwidth : ∀ T : ResTree φ ∅, w₀ + d < T.width)
    (T : ResTree φ ∅) :
    2 ^ d < T.size := by
  by_contra h
  obtain ⟨T', hT'⟩ := bsw_tree_width_size d w₀ φ hφ T (Nat.le_of_not_lt h)
  exact Nat.not_lt.mpr hT' (hwidth T')

end Mathmatica.BSWTradeoff
