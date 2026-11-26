/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Find

/-!
# Recursive Black Pebbling Game on Complete Binary Trees (Paterson-Hewitt 1970)

This module formalizes the black pebbling game (with leaf placement, internal placement,
left/right sliding moves, pebble removal for recomputation, and idle steps) on the complete
binary tree of height `h`, and proves the exact renormalization-group (RG) space complexity
`S(h) = h + 1` for all `h : ℕ` (Paterson & Hewitt 1970).

Using prefix-bit tree addressing (`TreeNode h := { p : List Bool // p.length ≤ h }`), the
left and right subtree RG embeddings `embedLeft` and `embedRight` commute definitionally
(`rfl`) with `leftChild`, `rightChild`, and `rootNode`. The dual projections `leftProj` and
`rightProj` have disjoint preimages, yielding `(leftProj C).card + (rightProj C).card ≤ C.card`
and a clean inductive proof of both the lower bound and the matching clean-pebbling upper bound.

## Epistemic Discipline (Four-Tier Classification)

* **Machine-Verified**: All definitions and theorems in this file — including the exact
  Paterson-Hewitt lower bound `h + 1 ≤ P.peakSpace`, the constructive clean-pebbling upper
  bound `∃ P, P.peakSpace ≤ h + 1`, and the exact RG space recursion `minPebbleSpace h = h + 1`
  — are formally verified in Lean 4 with zero `sorry`s and no extra axioms.
* **Model-Restricted**: The lower bound applies strictly to the black pebbling game on the
  complete binary tree DAG (`PebbleStep` / `ValidPebbling`), where pebbles model straight-line
  register reuse with recomputation allowed. Complete binary trees exhibit **no** time-space
  tradeoff: linear time `O(2^h)` already achieves the optimal space `h + 1`.
* **Conditional**: Obtaining super-linear time-space tradeoffs requires DAGs with higher
  pebbling / superconcentrator structure (e.g., Paul-Tarjan-Celoni or Lengauer-Tarjan graphs),
  and transferring pebbling lower bounds to general RAM or branching-program models requires
  obliviousness or white-box straight-line execution assumptions.
* **Conjectural**: General algorithm time-space lower bounds, Turing machine / circuit
  separations, and `P ≠ NP` are **NOT** claimed or implied by this module.

## Main definitions

* `TreeNode`, `rootNode`, `isLeaf`, `leftChild`, `rightChild`: Complete binary tree of height `h`.
* `embedLeft`, `embedRight`, `leftProj`, `rightProj`: RG subtree embeddings and projections.
* `PebbleConfig`, `PebbleStep`, `ValidPebbling`, `ValidPebbling.peakSpace`: Black pebbling game
  with sliding, removal (recomputation), and idle moves.
* `minPebbleSpace`: Minimum achievable peak pebble count on the height-`h` complete binary tree.

## Main results

* `card_leftProj_add_rightProj_le`: Disjointness of left/right RG projections.
* `binTree_pebbling_lower_bound`: For every `P : ValidPebbling h`, `h + 1 ≤ P.peakSpace`.
* `exists_clean_pebbling`: Constructive RG pebbling of height `h` with peak space `≤ h + 1`
  and final configuration `{rootNode h}`.
* `binTree_pebbling_upper_bound`: `∃ P : ValidPebbling h, P.peakSpace ≤ h + 1`.
* `binTree_min_pebbleSpace_eq`, `minPebbleSpace_eq`, `minPebbleSpace_succ`: Exact RG space
  equality `S(h) = h + 1` and recursion `S(h + 1) = S(h) + 1`.
-/

namespace Mathmatica.PebblingRG

/-! ### Complete Binary Tree and Prefix-Bit RG Embeddings -/

/-- Nodes of the complete binary tree of height `h`, addressed by root-to-node bit paths
of length at most `h`. -/
abbrev TreeNode (h : ℕ) := { p : List Bool // p.length ≤ h }

/-- The root node of the complete binary tree of height `h`. -/
def rootNode (h : ℕ) : TreeNode h := ⟨[], Nat.zero_le h⟩

/-- Predicate identifying leaves (nodes at maximum depth `h`). -/
def isLeaf {h : ℕ} (v : TreeNode h) : Prop := v.val.length = h

/-- Left child of an internal node `v` (appending `false`). -/
def leftChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) : TreeNode h :=
  ⟨v.val ++ [false], by simp; omega⟩

/-- Right child of an internal node `v` (appending `true`). -/
def rightChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) : TreeNode h :=
  ⟨v.val ++ [true], by simp; omega⟩

/-- RG embedding of the height-`h` tree into the left subtree of the height-`(h + 1)` tree
(prepending `false`). -/
def embedLeft {h : ℕ} (v : TreeNode h) : TreeNode (h + 1) :=
  ⟨false :: v.val, by simp [v.property]⟩

/-- RG embedding of the height-`h` tree into the right subtree of the height-`(h + 1)` tree
(prepending `true`). -/
def embedRight {h : ℕ} (v : TreeNode h) : TreeNode (h + 1) :=
  ⟨true :: v.val, by simp [v.property]⟩

lemma embedLeft_injective {h : ℕ} : Function.Injective (@embedLeft h) := by
  intro u v huv
  apply Subtype.ext
  have hval : false :: u.val = false :: v.val := congrArg Subtype.val huv
  exact List.cons.inj hval |>.2

lemma embedRight_injective {h : ℕ} : Function.Injective (@embedRight h) := by
  intro u v huv
  apply Subtype.ext
  have hval : true :: u.val = true :: v.val := congrArg Subtype.val huv
  exact List.cons.inj hval |>.2

lemma embedLeft_ne_embedRight {h : ℕ} (u v : TreeNode h) : embedLeft u ≠ embedRight v := by
  intro huv
  have hval : false :: u.val = true :: v.val := congrArg Subtype.val huv
  cases hval

lemma embedLeft_ne_root {h : ℕ} (v : TreeNode h) : embedLeft v ≠ rootNode (h + 1) := by
  intro hv
  have hval : false :: v.val = [] := congrArg Subtype.val hv
  cases hval

lemma embedRight_ne_root {h : ℕ} (v : TreeNode h) : embedRight v ≠ rootNode (h + 1) := by
  intro hv
  have hval : true :: v.val = [] := congrArg Subtype.val hv
  cases hval

lemma embedLeft_root (h : ℕ) :
    embedLeft (rootNode h) = leftChild (rootNode (h + 1)) (Nat.zero_lt_succ h) := rfl

lemma embedRight_root (h : ℕ) :
    embedRight (rootNode h) = rightChild (rootNode (h + 1)) (Nat.zero_lt_succ h) := rfl

lemma embedLeft_leftChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) :
    embedLeft (leftChild v hv) =
      leftChild (embedLeft v) (by simpa [embedLeft] using Nat.succ_lt_succ hv) := rfl

lemma embedLeft_rightChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) :
    embedLeft (rightChild v hv) =
      rightChild (embedLeft v) (by simpa [embedLeft] using Nat.succ_lt_succ hv) := rfl

lemma embedRight_leftChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) :
    embedRight (leftChild v hv) =
      leftChild (embedRight v) (by simpa [embedRight] using Nat.succ_lt_succ hv) := rfl

lemma embedRight_rightChild {h : ℕ} (v : TreeNode h) (hv : v.val.length < h) :
    embedRight (rightChild v hv) =
      rightChild (embedRight v) (by simpa [embedRight] using Nat.succ_lt_succ hv) := rfl

lemma embedLeft_isLeaf_iff {h : ℕ} (v : TreeNode h) :
    isLeaf (embedLeft v) ↔ isLeaf v := by
  simp [isLeaf, embedLeft]

lemma embedRight_isLeaf_iff {h : ℕ} (v : TreeNode h) :
    isLeaf (embedRight v) ↔ isLeaf v := by
  simp [isLeaf, embedRight]

/-- Exhaustive trichotomy for nodes of the height-`(h + 1)` tree: root, left subtree, or
right subtree. -/
lemma treeNode_cases {h : ℕ} (v : TreeNode (h + 1)) :
    v = rootNode (h + 1) ∨ (∃ u : TreeNode h, v = embedLeft u) ∨
      (∃ u : TreeNode h, v = embedRight u) := by
  rcases v with ⟨p, hp⟩
  cases p with
  | nil => exact Or.inl rfl
  | cons b rest =>
    have hrest : rest.length ≤ h := by simpa using hp
    cases b with
    | false => exact Or.inr (Or.inl ⟨⟨rest, hrest⟩, rfl⟩)
    | true => exact Or.inr (Or.inr ⟨⟨rest, hrest⟩, rfl⟩)

/-! ### Pebble Configurations and RG Projections -/

/-- A black pebble configuration on the complete binary tree of height `h`. -/
abbrev PebbleConfig (h : ℕ) := Finset (TreeNode h)

/-- Partial inverse of `embedLeft`. -/
def unembedLeft {h : ℕ} (v : TreeNode (h + 1)) : Option (TreeNode h) :=
  match v with
  | ⟨false :: rest, hlen⟩ => some ⟨rest, Nat.le_of_succ_le_succ hlen⟩
  | _ => none

/-- Partial inverse of `embedRight`. -/
def unembedRight {h : ℕ} (v : TreeNode (h + 1)) : Option (TreeNode h) :=
  match v with
  | ⟨true :: rest, hlen⟩ => some ⟨rest, Nat.le_of_succ_le_succ hlen⟩
  | _ => none

/-- RG projection onto the left height-`h` subtree. -/
def leftProj {h : ℕ} (C : PebbleConfig (h + 1)) : PebbleConfig h :=
  C.biUnion fun v => (unembedLeft v).toFinset

/-- RG projection onto the right height-`h` subtree. -/
def rightProj {h : ℕ} (C : PebbleConfig (h + 1)) : PebbleConfig h :=
  C.biUnion fun v => (unembedRight v).toFinset

lemma mem_leftProj {h : ℕ} {C : PebbleConfig (h + 1)} {u : TreeNode h} :
    u ∈ leftProj C ↔ embedLeft u ∈ C := by
  constructor
  · intro hu
    rcases Finset.mem_biUnion.mp hu with ⟨v, hvC, hvu⟩
    rcases v with ⟨p, hp⟩
    cases p with
    | nil => simp [unembedLeft] at hvu
    | cons b rest =>
      cases b with
      | true => simp [unembedLeft] at hvu
      | false =>
        simp only [unembedLeft, Option.mem_toFinset, Option.mem_def, Option.some.injEq] at hvu
        subst hvu
        exact hvC
  · intro hu
    exact Finset.mem_biUnion.mpr ⟨embedLeft u, hu, by simp [unembedLeft, embedLeft]⟩

lemma mem_rightProj {h : ℕ} {C : PebbleConfig (h + 1)} {u : TreeNode h} :
    u ∈ rightProj C ↔ embedRight u ∈ C := by
  constructor
  · intro hu
    rcases Finset.mem_biUnion.mp hu with ⟨v, hvC, hvu⟩
    rcases v with ⟨p, hp⟩
    cases p with
    | nil => simp [unembedRight] at hvu
    | cons b rest =>
      cases b with
      | false => simp [unembedRight] at hvu
      | true =>
        simp only [unembedRight, Option.mem_toFinset, Option.mem_def, Option.some.injEq] at hvu
        subst hvu
        exact hvC
  · intro hu
    exact Finset.mem_biUnion.mpr ⟨embedRight u, hu, by simp [unembedRight, embedRight]⟩

@[simp]
lemma leftProj_empty {h : ℕ} : leftProj (∅ : PebbleConfig (h + 1)) = ∅ := by
  ext u
  simp [mem_leftProj]

@[simp]
lemma rightProj_empty {h : ℕ} : rightProj (∅ : PebbleConfig (h + 1)) = ∅ := by
  ext u
  simp [mem_rightProj]

lemma leftProj_insert_embedLeft {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    leftProj (insert (embedLeft u) C) = insert u (leftProj C) := by
  ext x
  simp [mem_leftProj, embedLeft_injective.eq_iff]

lemma leftProj_insert_embedRight {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    leftProj (insert (embedRight u) C) = leftProj C := by
  ext x
  simp [mem_leftProj, embedLeft_ne_embedRight]

lemma leftProj_insert_root {h : ℕ} (C : PebbleConfig (h + 1)) :
    leftProj (insert (rootNode (h + 1)) C) = leftProj C := by
  ext x
  simp [mem_leftProj, embedLeft_ne_root]

lemma leftProj_erase_embedLeft {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    leftProj (C.erase (embedLeft u)) = (leftProj C).erase u := by
  ext x
  simp [mem_leftProj, embedLeft_injective.eq_iff]

lemma leftProj_erase_embedRight {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    leftProj (C.erase (embedRight u)) = leftProj C := by
  ext x
  simp [mem_leftProj, embedLeft_ne_embedRight]

lemma leftProj_erase_root {h : ℕ} (C : PebbleConfig (h + 1)) :
    leftProj (C.erase (rootNode (h + 1))) = leftProj C := by
  ext x
  simp [mem_leftProj, embedLeft_ne_root]

lemma rightProj_insert_embedRight {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    rightProj (insert (embedRight u) C) = insert u (rightProj C) := by
  ext x
  simp [mem_rightProj, embedRight_injective.eq_iff]

lemma rightProj_insert_embedLeft {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    rightProj (insert (embedLeft u) C) = rightProj C := by
  ext x
  simp [mem_rightProj, (embedLeft_ne_embedRight _ _).symm]

lemma rightProj_insert_root {h : ℕ} (C : PebbleConfig (h + 1)) :
    rightProj (insert (rootNode (h + 1)) C) = rightProj C := by
  ext x
  simp [mem_rightProj, embedRight_ne_root]

lemma rightProj_erase_embedRight {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    rightProj (C.erase (embedRight u)) = (rightProj C).erase u := by
  ext x
  simp [mem_rightProj, embedRight_injective.eq_iff]

lemma rightProj_erase_embedLeft {h : ℕ} (u : TreeNode h) (C : PebbleConfig (h + 1)) :
    rightProj (C.erase (embedLeft u)) = rightProj C := by
  ext x
  simp [mem_rightProj, (embedLeft_ne_embedRight _ _).symm]

lemma rightProj_erase_root {h : ℕ} (C : PebbleConfig (h + 1)) :
    rightProj (C.erase (rootNode (h + 1))) = rightProj C := by
  ext x
  simp [mem_rightProj, embedRight_ne_root]

/-- Left and right subtree projections occupy disjoint subsets of `C`, so their cardinalities
sum to at most `C.card`. -/
theorem card_leftProj_add_rightProj_le {h : ℕ} (C : PebbleConfig (h + 1)) :
    (leftProj C).card + (rightProj C).card ≤ C.card := by
  have hL : (leftProj C).card = ((leftProj C).image embedLeft).card :=
    (Finset.card_image_of_injective _ embedLeft_injective).symm
  have hR : (rightProj C).card = ((rightProj C).image embedRight).card :=
    (Finset.card_image_of_injective _ embedRight_injective).symm
  have hdisj : Disjoint ((leftProj C).image embedLeft) ((rightProj C).image embedRight) := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    rcases Finset.mem_image.mp hxL with ⟨u, _, rfl⟩
    rcases Finset.mem_image.mp hxR with ⟨v, _, hv⟩
    exact embedLeft_ne_embedRight u v hv.symm
  have hsub : ((leftProj C).image embedLeft) ∪ ((rightProj C).image embedRight) ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxL | hxR
    · rcases Finset.mem_image.mp hxL with ⟨u, hu, rfl⟩
      exact mem_leftProj.mp hu
    · rcases Finset.mem_image.mp hxR with ⟨u, hu, rfl⟩
      exact mem_rightProj.mp hu
  rw [hL, hR, ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

/-! ### Black Pebbling Transition Rules and Valid Strategies -/

/-- Single-step transitions of the black pebbling game (with sliding, recomputation via removal,
and idle moves). -/
inductive PebbleStep {h : ℕ} : PebbleConfig h → PebbleConfig h → Prop where
  | placeLeaf (C : PebbleConfig h) (v : TreeNode h) (hv : isLeaf v) :
      PebbleStep C (insert v C)
  | placeInternal (C : PebbleConfig h) (v : TreeNode h) (hv : v.val.length < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PebbleStep C (insert v C)
  | slideLeft (C : PebbleConfig h) (v : TreeNode h) (hv : v.val.length < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PebbleStep C (insert v (C.erase (leftChild v hv)))
  | slideRight (C : PebbleConfig h) (v : TreeNode h) (hv : v.val.length < h)
      (hL : leftChild v hv ∈ C) (hR : rightChild v hv ∈ C) :
      PebbleStep C (insert v (C.erase (rightChild v hv)))
  | remove (C : PebbleConfig h) (v : TreeNode h) :
      PebbleStep C (C.erase v)
  | idle (C : PebbleConfig h) :
      PebbleStep C C

/-- A valid black pebbling strategy on the height-`h` complete binary tree starts empty,
takes valid `PebbleStep`s, and places a pebble on `rootNode h` at the final step. -/
structure ValidPebbling (h : ℕ) where
  steps : ℕ
  trace : Fin (steps + 1) → PebbleConfig h
  init_empty : trace 0 = ∅
  valid_step : ∀ i : Fin steps,
    PebbleStep (trace ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (trace ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
  reaches_root : rootNode h ∈ trace ⟨steps, Nat.lt_succ_self steps⟩

/-- Peak pebble space used by a valid pebbling strategy `P`. -/
def ValidPebbling.peakSpace {h : ℕ} (P : ValidPebbling h) : ℕ :=
  Finset.univ.sup fun t : Fin (P.steps + 1) => (P.trace t).card

lemma card_le_peakSpace {h : ℕ} (P : ValidPebbling h) (t : Fin (P.steps + 1)) :
    (P.trace t).card ≤ P.peakSpace :=
  Finset.le_sup (f := fun t => (P.trace t).card) (Finset.mem_univ t)

lemma peakSpace_le_iff {h : ℕ} (P : ValidPebbling h) (k : ℕ) :
    P.peakSpace ≤ k ↔ ∀ t : Fin (P.steps + 1), (P.trace t).card ≤ k := by
  simp [ValidPebbling.peakSpace]

lemma exists_peakSpace_attained {h : ℕ} (P : ValidPebbling h) :
    ∃ t : Fin (P.steps + 1), P.peakSpace = (P.trace t).card := by
  have hne : (Finset.univ : Finset (Fin (P.steps + 1))).Nonempty :=
    ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _⟩
  rcases Finset.exists_mem_eq_sup Finset.univ hne (fun t => (P.trace t).card) with ⟨t, _, ht⟩
  exact ⟨t, ht⟩

/-! ### Projection Lemmas for the Paterson-Hewitt Lower Bound -/

/-- Placing a pebble on the root of the height-`(h + 1)` tree requires both children
(`embedLeft (rootNode h)` and `embedRight (rootNode h)`) to be pebbled immediately before. -/
lemma pebbleStep_root_children {h : ℕ} {C C' : PebbleConfig (h + 1)}
    (hs : PebbleStep C C')
    (hnot : rootNode (h + 1) ∉ C)
    (hmem : rootNode (h + 1) ∈ C') :
    embedLeft (rootNode h) ∈ C ∧ embedRight (rootNode h) ∈ C := by
  cases hs with
  | placeLeaf v hv =>
    have hne : v ≠ rootNode (h + 1) := by
      intro hveq
      subst hveq
      simp [isLeaf, rootNode] at hv
    simp [hnot] at hmem
    exact (hne hmem.symm).elim
  | placeInternal v hv hL hR =>
    have hveq : v = rootNode (h + 1) := by
      rcases Finset.mem_insert.mp hmem with h1 | h2
      · exact h1.symm
      · exact (hnot h2).elim
    subst hveq
    exact ⟨hL, hR⟩
  | slideLeft v hv hL hR =>
    have hveq : v = rootNode (h + 1) := by
      rcases Finset.mem_insert.mp hmem with h1 | h2
      · exact h1.symm
      · exact (hnot (Finset.mem_of_mem_erase h2)).elim
    subst hveq
    exact ⟨hL, hR⟩
  | slideRight v hv hL hR =>
    have hveq : v = rootNode (h + 1) := by
      rcases Finset.mem_insert.mp hmem with h1 | h2
      · exact h1.symm
      · exact (hnot (Finset.mem_of_mem_erase h2)).elim
    subst hveq
    exact ⟨hL, hR⟩
  | remove v =>
    exact (hnot (Finset.mem_of_mem_erase hmem)).elim
  | idle =>
    exact (hnot hmem).elim

/-- Any step whose resulting configuration does not pebble the root projects to a valid
`PebbleStep` on the left subtree. -/
lemma pebbleStep_leftProj {h : ℕ} {C C' : PebbleConfig (h + 1)}
    (hs : PebbleStep C C') (hnot : rootNode (h + 1) ∉ C') :
    PebbleStep (leftProj C) (leftProj C') := by
  cases hs with
  | placeLeaf v hv =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · rw [leftProj_insert_embedLeft]
      exact PebbleStep.placeLeaf _ u ((embedLeft_isLeaf_iff u).mp hv)
    · rw [leftProj_insert_embedRight]
      exact PebbleStep.idle _
  | placeInternal v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · have hu : u.val.length < h := by simpa [embedLeft] using hv
      rw [leftProj_insert_embedLeft]
      exact PebbleStep.placeInternal _ u hu (mem_leftProj.mpr hL) (mem_leftProj.mpr hR)
    · rw [leftProj_insert_embedRight]
      exact PebbleStep.idle _
  | slideLeft v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · have hu : u.val.length < h := by simpa [embedLeft] using hv
      rw [leftProj_insert_embedLeft, ← embedLeft_leftChild u hu, leftProj_erase_embedLeft]
      exact PebbleStep.slideLeft _ u hu (mem_leftProj.mpr hL) (mem_leftProj.mpr hR)
    · have hu : u.val.length < h := by simpa [embedRight] using hv
      rw [leftProj_insert_embedRight, ← embedRight_leftChild u hu, leftProj_erase_embedRight]
      exact PebbleStep.idle _
  | slideRight v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · have hu : u.val.length < h := by simpa [embedLeft] using hv
      rw [leftProj_insert_embedLeft, ← embedLeft_rightChild u hu, leftProj_erase_embedLeft]
      exact PebbleStep.slideRight _ u hu (mem_leftProj.mpr hL) (mem_leftProj.mpr hR)
    · have hu : u.val.length < h := by simpa [embedRight] using hv
      rw [leftProj_insert_embedRight, ← embedRight_rightChild u hu, leftProj_erase_embedRight]
      exact PebbleStep.idle _
  | remove v =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [leftProj_erase_root]
      exact PebbleStep.idle _
    · rw [leftProj_erase_embedLeft]
      exact PebbleStep.remove _ u
    · rw [leftProj_erase_embedRight]
      exact PebbleStep.idle _
  | idle =>
    exact PebbleStep.idle _

/-- Any step whose resulting configuration does not pebble the root projects to a valid
`PebbleStep` on the right subtree. -/
lemma pebbleStep_rightProj {h : ℕ} {C C' : PebbleConfig (h + 1)}
    (hs : PebbleStep C C') (hnot : rootNode (h + 1) ∉ C') :
    PebbleStep (rightProj C) (rightProj C') := by
  cases hs with
  | placeLeaf v hv =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · rw [rightProj_insert_embedLeft]
      exact PebbleStep.idle _
    · rw [rightProj_insert_embedRight]
      exact PebbleStep.placeLeaf _ u ((embedRight_isLeaf_iff u).mp hv)
  | placeInternal v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · rw [rightProj_insert_embedLeft]
      exact PebbleStep.idle _
    · have hu : u.val.length < h := by simpa [embedRight] using hv
      rw [rightProj_insert_embedRight]
      exact PebbleStep.placeInternal _ u hu (mem_rightProj.mpr hL) (mem_rightProj.mpr hR)
  | slideLeft v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · have hu : u.val.length < h := by simpa [embedLeft] using hv
      rw [rightProj_insert_embedLeft, ← embedLeft_leftChild u hu, rightProj_erase_embedLeft]
      exact PebbleStep.idle _
    · have hu : u.val.length < h := by simpa [embedRight] using hv
      rw [rightProj_insert_embedRight, ← embedRight_leftChild u hu, rightProj_erase_embedRight]
      exact PebbleStep.slideLeft _ u hu (mem_rightProj.mpr hL) (mem_rightProj.mpr hR)
  | slideRight v hv hL hR =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hnot (Finset.mem_insert_self _ _)).elim
    · have hu : u.val.length < h := by simpa [embedLeft] using hv
      rw [rightProj_insert_embedLeft, ← embedLeft_rightChild u hu, rightProj_erase_embedLeft]
      exact PebbleStep.idle _
    · have hu : u.val.length < h := by simpa [embedRight] using hv
      rw [rightProj_insert_embedRight, ← embedRight_rightChild u hu, rightProj_erase_embedRight]
      exact PebbleStep.slideRight _ u hu (mem_rightProj.mpr hL) (mem_rightProj.mpr hR)
  | remove v =>
    rcases treeNode_cases v with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [rightProj_erase_root]
      exact PebbleStep.idle _
    · rw [rightProj_erase_embedLeft]
      exact PebbleStep.idle _
    · rw [rightProj_erase_embedRight]
      exact PebbleStep.remove _ u
  | idle =>
    exact PebbleStep.idle _

/-! ### Main Theorem 1: Paterson-Hewitt Exact Lower Bound -/

/-- **Paterson-Hewitt Lower Bound (1970)**: Every valid black pebbling strategy on the
complete binary tree of height `h` uses at least `h + 1` pebbles at its peak. -/
theorem binTree_pebbling_lower_bound (h : ℕ) (P : ValidPebbling h) :
    h + 1 ≤ P.peakSpace := by
  induction h with
  | zero =>
    have hpos : 1 ≤ (P.trace ⟨P.steps, Nat.lt_succ_self P.steps⟩).card :=
      Finset.one_le_card.mpr ⟨rootNode 0, P.reaches_root⟩
    exact hpos.trans (card_le_peakSpace P ⟨P.steps, Nat.lt_succ_self P.steps⟩)
  | succ h ih =>
    -- Step 1: Find the first time `tRoot` at which `rootNode (h + 1)` is pebbled.
    let Sroot : Finset (Fin (P.steps + 1)) :=
      Finset.univ.filter fun t => rootNode (h + 1) ∈ P.trace t
    have hSroot_ne : Sroot.Nonempty :=
      ⟨⟨P.steps, Nat.lt_succ_self _⟩, by simp [Sroot, P.reaches_root]⟩
    let tRoot : Fin (P.steps + 1) := Sroot.min' hSroot_ne
    have htRoot_mem : rootNode (h + 1) ∈ P.trace tRoot :=
      (Finset.mem_filter.mp (Finset.min'_mem Sroot hSroot_ne)).2
    have htRoot_min : ∀ t : Fin (P.steps + 1), t < tRoot → rootNode (h + 1) ∉ P.trace t := by
      intro t hlt hmem
      have hle : tRoot ≤ t := Finset.min'_le Sroot t (by simp [Sroot, hmem])
      exact not_lt_of_ge hle hlt
    have htRoot_pos : 1 ≤ tRoot.val := by
      by_contra h0
      have hzero : tRoot = 0 := by
        ext
        show tRoot.val = 0
        omega
      rw [hzero, P.init_empty] at htRoot_mem
      simp at htRoot_mem
    -- At `tPrev = tRoot - 1`, both `embedLeft (rootNode h)` and `embedRight (rootNode h)` hold.
    let tPrev : ℕ := tRoot.val - 1
    have htPrev_lt : tPrev < P.steps := by omega
    have htPrev_succ : tPrev + 1 = tRoot.val := by omega
    have hnotPrev : rootNode (h + 1) ∉ P.trace ⟨tPrev, Nat.lt_succ_of_lt htPrev_lt⟩ :=
      htRoot_min ⟨tPrev, Nat.lt_succ_of_lt htPrev_lt⟩ (by show tPrev < tRoot.val; omega)
    have hstepPrev :
        PebbleStep (P.trace ⟨tPrev, Nat.lt_succ_of_lt htPrev_lt⟩) (P.trace tRoot) := by
      have h := P.valid_step ⟨tPrev, htPrev_lt⟩
      have hfin : (⟨tPrev + 1, Nat.succ_lt_succ htPrev_lt⟩ : Fin (P.steps + 1)) = tRoot := by
        ext
        exact htPrev_succ
      rwa [hfin] at h
    have ⟨hLeftPrev, hRightPrev⟩ := pebbleStep_root_children hstepPrev hnotPrev htRoot_mem
    -- Step 2: Find the last times `tL, tR ≤ tPrev` when `leftProj` / `rightProj` are empty.
    let SL : Finset (Fin (P.steps + 1)) :=
      Finset.univ.filter fun t => t.val ≤ tPrev ∧ leftProj (P.trace t) = ∅
    let SR : Finset (Fin (P.steps + 1)) :=
      Finset.univ.filter fun t => t.val ≤ tPrev ∧ rightProj (P.trace t) = ∅
    have hSL_ne : SL.Nonempty :=
      ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [SL, P.init_empty]⟩
    have hSR_ne : SR.Nonempty :=
      ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [SR, P.init_empty]⟩
    let tL : Fin (P.steps + 1) := SL.max' hSL_ne
    let tR : Fin (P.steps + 1) := SR.max' hSR_ne
    have htL_spec := (Finset.mem_filter.mp (Finset.max'_mem SL hSL_ne)).2
    have htR_spec := (Finset.mem_filter.mp (Finset.max'_mem SR hSR_ne)).2
    have htL_max : ∀ t : Fin (P.steps + 1),
        tL.val < t.val → t.val ≤ tPrev → leftProj (P.trace t) ≠ ∅ := by
      intro t hgt hle hemp
      have hle' : t ≤ tL := Finset.le_max' SL t (by simp [SL, hle, hemp])
      exact not_lt_of_ge hle' hgt
    have htR_max : ∀ t : Fin (P.steps + 1),
        tR.val < t.val → t.val ≤ tPrev → rightProj (P.trace t) ≠ ∅ := by
      intro t hgt hle hemp
      have hle' : t ≤ tR := Finset.le_max' SR t (by simp [SR, hle, hemp])
      exact not_lt_of_ge hle' hgt
    -- Step 3: Case split on `tL.val ≤ tR.val` vs `tR.val ≤ tL.val`.
    rcases le_total tL.val tR.val with hLR | hRL
    · -- Project `[tR, tPrev]` onto the right subtree.
      let PR : ValidPebbling h :=
        { steps := tPrev - tR.val
          trace := fun i => rightProj (P.trace ⟨tR.val + i.val, by omega⟩)
          init_empty := by
            have hfin : (⟨tR.val + 0, by omega⟩ : Fin (P.steps + 1)) = tR := by ext; simp
            simpa [hfin] using htR_spec.2
          valid_step := fun i => by
            have hnot : rootNode (h + 1) ∉ P.trace ⟨tR.val + i.val + 1, by omega⟩ :=
              htRoot_min ⟨tR.val + i.val + 1, by omega⟩
                (by show tR.val + i.val + 1 < tRoot.val; omega)
            exact pebbleStep_rightProj (P.valid_step ⟨tR.val + i.val, by omega⟩) hnot
          reaches_root := by
            have hfin : (⟨tR.val + (tPrev - tR.val), by omega⟩ : Fin (P.steps + 1)) =
                ⟨tPrev, Nat.lt_succ_of_lt htPrev_lt⟩ := by
              ext; dsimp; omega
            rw [hfin]
            exact mem_rightProj.mpr hRightPrev }
      have hPR_lb : h + 1 ≤ PR.peakSpace := ih PR
      rcases exists_peakSpace_attained PR with ⟨iStar, hiStar⟩
      have hiStar_le : iStar.val ≤ tPrev - tR.val := Nat.lt_succ_iff.mp iStar.isLt
      let tStar : Fin (P.steps + 1) := ⟨tR.val + iStar.val, by omega⟩
      have hR_card : h + 1 ≤ (rightProj (P.trace tStar)).card := by
        simpa [PR, tStar, hiStar] using hPR_lb
      have hiStar_pos : 0 < iStar.val := by
        by_contra h0
        have hi0 : iStar.val = 0 := by omega
        have htStar_eq : tStar = tR := by ext; simp [tStar, hi0]
        rw [htStar_eq, htR_spec.2] at hR_card
        simp at hR_card
      have hL_ne : leftProj (P.trace tStar) ≠ ∅ :=
        htL_max tStar (by dsimp [tStar]; omega) (by dsimp [tStar]; omega)
      have hL_card : 1 ≤ (leftProj (P.trace tStar)).card :=
        Finset.one_le_card.mpr (Finset.ne_empty_iff_nonempty.mp hL_ne)
      have hsum : h + 2 ≤ (P.trace tStar).card := by
        have hdisj := card_leftProj_add_rightProj_le (P.trace tStar)
        omega
      exact hsum.trans (card_le_peakSpace P tStar)
    · -- Symmetric case: project `[tL, tPrev]` onto the left subtree.
      let PL : ValidPebbling h :=
        { steps := tPrev - tL.val
          trace := fun i => leftProj (P.trace ⟨tL.val + i.val, by omega⟩)
          init_empty := by
            have hfin : (⟨tL.val + 0, by omega⟩ : Fin (P.steps + 1)) = tL := by ext; simp
            simpa [hfin] using htL_spec.2
          valid_step := fun i => by
            have hnot : rootNode (h + 1) ∉ P.trace ⟨tL.val + i.val + 1, by omega⟩ :=
              htRoot_min ⟨tL.val + i.val + 1, by omega⟩
                (by show tL.val + i.val + 1 < tRoot.val; omega)
            exact pebbleStep_leftProj (P.valid_step ⟨tL.val + i.val, by omega⟩) hnot
          reaches_root := by
            have hfin : (⟨tL.val + (tPrev - tL.val), by omega⟩ : Fin (P.steps + 1)) =
                ⟨tPrev, Nat.lt_succ_of_lt htPrev_lt⟩ := by
              ext; dsimp; omega
            rw [hfin]
            exact mem_leftProj.mpr hLeftPrev }
      have hPL_lb : h + 1 ≤ PL.peakSpace := ih PL
      rcases exists_peakSpace_attained PL with ⟨iStar, hiStar⟩
      have hiStar_le : iStar.val ≤ tPrev - tL.val := Nat.lt_succ_iff.mp iStar.isLt
      let tStar : Fin (P.steps + 1) := ⟨tL.val + iStar.val, by omega⟩
      have hL_card : h + 1 ≤ (leftProj (P.trace tStar)).card := by
        simpa [PL, tStar, hiStar] using hPL_lb
      have hiStar_pos : 0 < iStar.val := by
        by_contra h0
        have hi0 : iStar.val = 0 := by omega
        have htStar_eq : tStar = tL := by ext; simp [tStar, hi0]
        rw [htStar_eq, htL_spec.2] at hL_card
        simp at hL_card
      have hR_ne : rightProj (P.trace tStar) ≠ ∅ :=
        htR_max tStar (by dsimp [tStar]; omega) (by dsimp [tStar]; omega)
      have hR_card : 1 ≤ (rightProj (P.trace tStar)).card :=
        Finset.one_le_card.mpr (Finset.ne_empty_iff_nonempty.mp hR_ne)
      have hsum : h + 2 ≤ (P.trace tStar).card := by
        have hdisj := card_leftProj_add_rightProj_le (P.trace tStar)
        omega
      exact hsum.trans (card_le_peakSpace P tStar)

/-! ### Embedding Lemmas for the Constructive RG Upper Bound -/

/-- Embedding a `PebbleStep` into the left subtree preserves validity. -/
lemma pebbleStep_embedLeft {h : ℕ} {C C' : PebbleConfig h} (hs : PebbleStep C C') :
    PebbleStep (C.image embedLeft) (C'.image embedLeft) := by
  cases hs with
  | placeLeaf v hv =>
    rw [Finset.image_insert]
    exact PebbleStep.placeLeaf _ (embedLeft v) ((embedLeft_isLeaf_iff v).mpr hv)
  | placeInternal v hv hL hR =>
    rw [Finset.image_insert]
    exact PebbleStep.placeInternal _ (embedLeft v)
      (by simpa [embedLeft] using Nat.succ_lt_succ hv)
      (by rw [← embedLeft_leftChild v hv]; exact Finset.mem_image_of_mem _ hL)
      (by rw [← embedLeft_rightChild v hv]; exact Finset.mem_image_of_mem _ hR)
  | slideLeft v hv hL hR =>
    rw [Finset.image_insert, Finset.image_erase embedLeft_injective]
    exact PebbleStep.slideLeft _ (embedLeft v)
      (by simpa [embedLeft] using Nat.succ_lt_succ hv)
      (by rw [← embedLeft_leftChild v hv]; exact Finset.mem_image_of_mem _ hL)
      (by rw [← embedLeft_rightChild v hv]; exact Finset.mem_image_of_mem _ hR)
  | slideRight v hv hL hR =>
    rw [Finset.image_insert, Finset.image_erase embedLeft_injective]
    exact PebbleStep.slideRight _ (embedLeft v)
      (by simpa [embedLeft] using Nat.succ_lt_succ hv)
      (by rw [← embedLeft_leftChild v hv]; exact Finset.mem_image_of_mem _ hL)
      (by rw [← embedLeft_rightChild v hv]; exact Finset.mem_image_of_mem _ hR)
  | remove v =>
    rw [Finset.image_erase embedLeft_injective]
    exact PebbleStep.remove _ (embedLeft v)
  | idle =>
    exact PebbleStep.idle _

/-- Embedding a `PebbleStep` into the right subtree while holding a disjoint spectator set `A`
fixed preserves validity. -/
lemma pebbleStep_embedRight_union {h : ℕ} {C C' : PebbleConfig h} {A : PebbleConfig (h + 1)}
    (hdisj : ∀ v : TreeNode h, embedRight v ∉ A) (hs : PebbleStep C C') :
    PebbleStep (A ∪ C.image embedRight) (A ∪ C'.image embedRight) := by
  have herase : ∀ (D : PebbleConfig h) (v : TreeNode h),
      (A ∪ D.image embedRight).erase (embedRight v) = A ∪ (D.erase v).image embedRight := by
    intro D v
    ext x
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hne, hxA | ⟨u, hu, rfl⟩⟩
      · exact Or.inl hxA
      · exact Or.inr ⟨u, ⟨fun h => hne (congrArg embedRight h), hu⟩, rfl⟩
    · rintro (hxA | ⟨u, ⟨hne, hu⟩, rfl⟩)
      · exact ⟨fun h => hdisj v (h ▸ hxA), Or.inl hxA⟩
      · exact ⟨fun h => hne (embedRight_injective h), Or.inr ⟨u, hu, rfl⟩⟩
  cases hs with
  | placeLeaf v hv =>
    rw [Finset.image_insert, Finset.union_insert]
    exact PebbleStep.placeLeaf _ (embedRight v) ((embedRight_isLeaf_iff v).mpr hv)
  | placeInternal v hv hL hR =>
    rw [Finset.image_insert, Finset.union_insert]
    exact PebbleStep.placeInternal _ (embedRight v)
      (by simpa [embedRight] using Nat.succ_lt_succ hv)
      (Finset.mem_union_right _
        (by rw [← embedRight_leftChild v hv]; exact Finset.mem_image_of_mem _ hL))
      (Finset.mem_union_right _
        (by rw [← embedRight_rightChild v hv]; exact Finset.mem_image_of_mem _ hR))
  | slideLeft v hv hL hR =>
    rw [Finset.image_insert, Finset.union_insert, ← herase]
    exact PebbleStep.slideLeft _ (embedRight v)
      (by simpa [embedRight] using Nat.succ_lt_succ hv)
      (Finset.mem_union_right _
        (by rw [← embedRight_leftChild v hv]; exact Finset.mem_image_of_mem _ hL))
      (Finset.mem_union_right _
        (by rw [← embedRight_rightChild v hv]; exact Finset.mem_image_of_mem _ hR))
  | slideRight v hv hL hR =>
    rw [Finset.image_insert, Finset.union_insert, ← herase]
    exact PebbleStep.slideRight _ (embedRight v)
      (by simpa [embedRight] using Nat.succ_lt_succ hv)
      (Finset.mem_union_right _
        (by rw [← embedRight_leftChild v hv]; exact Finset.mem_image_of_mem _ hL))
      (Finset.mem_union_right _
        (by rw [← embedRight_rightChild v hv]; exact Finset.mem_image_of_mem _ hR))
  | remove v =>
    rw [← herase]
    exact PebbleStep.remove _ (embedRight v)
  | idle =>
    exact PebbleStep.idle _

/-! ### Main Theorem 2: Constructive Recursive RG Upper Bound -/

/-- Strengthened inductive construction: for every `h : ℕ`, there exists a valid black pebbling
of the height-`h` complete binary tree with peak space `≤ h + 1` whose final configuration is
the singleton `{rootNode h}`. -/
theorem exists_clean_pebbling (h : ℕ) :
    ∃ P : ValidPebbling h,
      P.peakSpace ≤ h + 1 ∧ P.trace ⟨P.steps, Nat.lt_succ_self P.steps⟩ = {rootNode h} := by
  induction h with
  | zero =>
    refine ⟨{
      steps := 1
      trace := fun i => if i.val = 0 then ∅ else {rootNode 0}
      init_empty := rfl
      valid_step := fun i => by
        have hi : i.val = 0 := by omega
        simpa [hi] using PebbleStep.placeLeaf (∅ : PebbleConfig 0) (rootNode 0) rfl
      reaches_root := by simp
    }, ?_, by simp⟩
    rw [peakSpace_le_iff]
    intro t
    by_cases ht : t.val = 0 <;> simp [ht]
  | succ h ih =>
    rcases ih with ⟨P, hP_peak, hP_final⟩
    have hP_card : ∀ t : Fin (P.steps + 1), (P.trace t).card ≤ h + 1 :=
      (peakSpace_le_iff P (h + 1)).mp hP_peak
    let L0 : TreeNode (h + 1) := embedLeft (rootNode h)
    let R0 : TreeNode (h + 1) := embedRight (rootNode h)
    let N : ℕ := P.steps + P.steps + 2
    let tr : Fin (N + 1) → PebbleConfig (h + 1) := fun i =>
      if h1 : i.val ≤ P.steps then
        (P.trace ⟨i.val, Nat.lt_succ_of_le h1⟩).image embedLeft
      else if h2 : i.val ≤ P.steps + P.steps then
        {L0} ∪ (P.trace ⟨i.val - P.steps, by omega⟩).image embedRight
      else if i.val = P.steps + P.steps + 1 then
        {rootNode (h + 1), R0}
      else
        {rootNode (h + 1)}
    have hP_pos : 0 < P.steps := by
      by_contra h0
      have hfin : (⟨P.steps, Nat.lt_succ_self P.steps⟩ : Fin (P.steps + 1)) = 0 := by
        ext; show P.steps = 0; omega
      have hmem := P.reaches_root
      rw [hfin, P.init_empty] at hmem
      simp at hmem
    have htr_P : tr ⟨P.steps, by omega⟩ = {L0} := by
      simp [tr, hP_final, L0]
    have htr_2P : tr ⟨P.steps + P.steps, by omega⟩ = {L0, R0} := by
      have hnot1 : ¬ (P.steps + P.steps ≤ P.steps) := by omega
      have hsub : P.steps + P.steps - P.steps = P.steps := by omega
      simp only [tr, hnot1, ↓reduceDIte, le_refl, hsub]
      rw [hP_final]
      ext x
      simp [L0, R0]
    have htr_2P1 : tr ⟨P.steps + P.steps + 1, by omega⟩ = {rootNode (h + 1), R0} := by
      have h1 : ¬ (P.steps + P.steps + 1 ≤ P.steps) := by omega
      have h2 : ¬ (P.steps + P.steps + 1 ≤ P.steps + P.steps) := by omega
      simp [tr, h1, h2]
    have htr_N : tr ⟨N, Nat.lt_succ_self N⟩ = {rootNode (h + 1)} := by
      have h1 : ¬ (N ≤ P.steps) := by omega
      have h2 : ¬ (N ≤ P.steps + P.steps) := by omega
      have h3 : ¬ (N = P.steps + P.steps + 1) := by omega
      simp [tr, h1, h2, h3]
    have hdisjA : ∀ v : TreeNode h, embedRight v ∉ ({L0} : PebbleConfig (h + 1)) := by
      intro v hv
      rw [Finset.mem_singleton] at hv
      exact embedLeft_ne_embedRight (rootNode h) v hv.symm
    let Q : ValidPebbling (h + 1) :=
      { steps := N
        trace := tr
        init_empty := by simp [tr, P.init_empty]
        valid_step := fun i => by
          by_cases hlt1 : i.val < P.steps
          · have ha : i.val ≤ P.steps := le_of_lt hlt1
            have hb : i.val + 1 ≤ P.steps := hlt1
            simp only [tr, ha, hb, ↓reduceDIte]
            exact pebbleStep_embedLeft (P.valid_step ⟨i.val, hlt1⟩)
          · by_cases heq1 : i.val = P.steps
            · have hb1 : ¬ (i.val + 1 ≤ P.steps) := by omega
              have hb2 : i.val + 1 ≤ P.steps + P.steps := by omega
              have htr_i : tr ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
                  {L0} ∪ (P.trace 0).image embedRight := by
                have hfin : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) =
                    ⟨P.steps, by omega⟩ := by ext; exact heq1
                rw [hfin, htr_P, P.init_empty]
                simp
              have htr_i1 : tr ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
                  {L0} ∪ (P.trace ⟨1, by omega⟩).image embedRight := by
                simp only [tr, hb1, hb2, ↓reduceDIte]
                have hsub : i.val + 1 - P.steps = 1 := by omega
                simp [hsub]
              rw [htr_i, htr_i1]
              exact pebbleStep_embedRight_union hdisjA (P.valid_step ⟨0, hP_pos⟩)
            · by_cases hlt2 : i.val < P.steps + P.steps
              · have ha1 : ¬ (i.val ≤ P.steps) := by omega
                have ha2 : i.val ≤ P.steps + P.steps := le_of_lt hlt2
                have hb1 : ¬ (i.val + 1 ≤ P.steps) := by omega
                have hb2 : i.val + 1 ≤ P.steps + P.steps := hlt2
                simp only [tr, ha1, ha2, hb1, hb2, ↓reduceDIte]
                have hsub : i.val + 1 - P.steps = (i.val - P.steps) + 1 := by omega
                have hfin : (⟨i.val + 1 - P.steps, by omega⟩ : Fin (P.steps + 1)) =
                    ⟨(i.val - P.steps) + 1, by omega⟩ := by ext; exact hsub
                rw [hfin]
                exact pebbleStep_embedRight_union hdisjA
                  (P.valid_step ⟨i.val - P.steps, by omega⟩)
              · by_cases heq2 : i.val = P.steps + P.steps
                · have hfin1 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) =
                      ⟨P.steps + P.steps, by omega⟩ := by ext; exact heq2
                  have hfin2 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) =
                      ⟨P.steps + P.steps + 1, by omega⟩ := by ext; dsimp; omega
                  rw [hfin1, hfin2, htr_2P, htr_2P1]
                  have hslide := PebbleStep.slideLeft ({L0, R0} : PebbleConfig (h + 1))
                    (rootNode (h + 1)) (Nat.zero_lt_succ h)
                    (by rw [← embedLeft_root]; simp [L0])
                    (by rw [← embedRight_root]; simp [R0])
                  have heqSet :
                      insert (rootNode (h + 1))
                        (({L0, R0} : PebbleConfig (h + 1)).erase
                          (leftChild (rootNode (h + 1)) (Nat.zero_lt_succ h))) =
                      {rootNode (h + 1), R0} := by
                    rw [← embedLeft_root]
                    ext x
                    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
                    constructor
                    · rintro (rfl | ⟨hne, rfl | rfl⟩)
                      · exact Or.inl rfl
                      · exact (hne rfl).elim
                      · exact Or.inr rfl
                    · rintro (rfl | rfl)
                      · exact Or.inl rfl
                      · exact Or.inr ⟨(embedLeft_ne_embedRight (rootNode h) (rootNode h)).symm,
                          Or.inr rfl⟩
                  rwa [heqSet] at hslide
                · have heq3 : i.val = P.steps + P.steps + 1 := by omega
                  have hfin1 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) =
                      ⟨P.steps + P.steps + 1, by omega⟩ := by ext; exact heq3
                  have hfin2 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) =
                      ⟨N, Nat.lt_succ_self N⟩ := by ext; dsimp [N]; omega
                  rw [hfin1, hfin2, htr_2P1, htr_N]
                  have hrem := PebbleStep.remove ({rootNode (h + 1), R0} : PebbleConfig (h + 1)) R0
                  have heqSet :
                      ({rootNode (h + 1), R0} : PebbleConfig (h + 1)).erase R0 =
                        {rootNode (h + 1)} := by
                    ext x
                    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
                    constructor
                    · rintro ⟨hne, rfl | rfl⟩
                      · rfl
                      · exact (hne rfl).elim
                    · rintro rfl
                      exact ⟨(embedRight_ne_root (rootNode h)).symm, Or.inl rfl⟩
                  rwa [heqSet] at hrem
        reaches_root := by
          rw [htr_N]
          exact Finset.mem_singleton_self _ }
    refine ⟨Q, ?_, htr_N⟩
    rw [peakSpace_le_iff]
    intro t
    change (tr t).card ≤ h + 2
    by_cases h1 : t.val ≤ P.steps
    · simp only [tr, h1, ↓reduceDIte]
      rw [Finset.card_image_of_injective _ embedLeft_injective]
      exact (hP_card _).trans (Nat.le_succ _)
    · by_cases h2 : t.val ≤ P.steps + P.steps
      · simp only [tr, h1, h2, ↓reduceDIte]
        have hle := Finset.card_union_le ({L0} : PebbleConfig (h + 1))
          ((P.trace ⟨t.val - P.steps, by omega⟩).image embedRight)
        rw [Finset.card_singleton, Finset.card_image_of_injective _ embedRight_injective] at hle
        have hc := hP_card ⟨t.val - P.steps, by omega⟩
        omega
      · by_cases h3 : t.val = P.steps + P.steps + 1
        · simp only [tr, h1, h2, ↓reduceDIte]
          simp only [h3, ↓reduceIte]
          have hle := Finset.card_insert_le (rootNode (h + 1)) ({R0} : PebbleConfig (h + 1))
          simp only [Finset.card_singleton] at hle
          omega
        · simp only [tr, h1, h2, ↓reduceDIte]
          simp only [h3, ↓reduceIte, Finset.card_singleton]
          omega

/-- **Constructive RG Upper Bound**: For every `h : ℕ`, there exists a valid black pebbling
of the height-`h` complete binary tree using at most `h + 1` pebbles. -/
theorem binTree_pebbling_upper_bound (h : ℕ) :
    ∃ P : ValidPebbling h, P.peakSpace ≤ h + 1 :=
  let ⟨P, hP, _⟩ := exists_clean_pebbling h
  ⟨P, hP⟩

/-- **Exact Paterson-Hewitt RG Characterization**: Every valid pebbling of the height-`h`
complete binary tree uses at least `h + 1` pebbles, and this bound is attained with equality. -/
theorem binTree_min_pebbleSpace_eq (h : ℕ) :
    (∀ P : ValidPebbling h, h + 1 ≤ P.peakSpace) ∧
      (∃ P : ValidPebbling h, P.peakSpace = h + 1) := by
  refine ⟨binTree_pebbling_lower_bound h, ?_⟩
  rcases binTree_pebbling_upper_bound h with ⟨P, hle⟩
  exact ⟨P, le_antisymm hle (binTree_pebbling_lower_bound h P)⟩

/-- Minimum black pebbling space of the complete binary tree of height `h`. -/
noncomputable def minPebbleSpace (h : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ s : ℕ, ∃ P : ValidPebbling h, P.peakSpace ≤ s from
    ⟨h + 1, binTree_pebbling_upper_bound h⟩)

/-- Exact closed form: `minPebbleSpace h = h + 1`. -/
theorem minPebbleSpace_eq (h : ℕ) : minPebbleSpace h = h + 1 := by
  classical
  have hle : minPebbleSpace h ≤ h + 1 :=
    Nat.find_min' _ (binTree_pebbling_upper_bound h)
  rcases Nat.find_spec (show ∃ s : ℕ, ∃ P : ValidPebbling h, P.peakSpace ≤ s from
    ⟨h + 1, binTree_pebbling_upper_bound h⟩) with ⟨P, hP⟩
  have hge : h + 1 ≤ minPebbleSpace h :=
    (binTree_pebbling_lower_bound h P).trans hP
  exact le_antisymm hle hge

/-- Exact RG recursion: doubling the tree (increasing height by 1) adds exactly 1 pebble. -/
theorem minPebbleSpace_succ (h : ℕ) : minPebbleSpace (h + 1) = minPebbleSpace h + 1 := by
  rw [minPebbleSpace_eq, minPebbleSpace_eq]

end Mathmatica.PebblingRG
