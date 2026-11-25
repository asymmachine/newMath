/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Data.Finset.Powerset
import Mathmatica.ExpanderWidth
import Mathmatica.XORSATBasis

/-!
# Tseitin Formulas on Edge-Expanding Graphs: Dual-Basis Separation

This module establishes the end-to-end separation between the `GF(2)`-linear basis and the Boolean
CNF / general DAG resolution (CDCL) basis on Tseitin formulas over edge-expanding graphs.

For any finite loopless graph `G` with `V` vertices and `E` edges and any vertex charge assignment
`χ : Fin V → Bool`, we encode the exact same Tseitin parity constraints in two algebraic bases:

1. **`GF(2)`-linear basis (`tseitinLinSys G χ`)**: `V` linear equations over `GF(2)`, one per
   vertex. By `Mathmatica.XORSATBasis.gaussElimList_length_le`, Gaussian elimination along any
   variable order suffers zero blowup and maintains at most `V` equations
   (`tseitin_f2_zero_blowup`).
2. **CNF Boolean basis (`tseitinCNF G χ`)**: For each vertex `v`, the set of all full-polarity
   clauses on `incidentEdges G v` forbidding assignments of the wrong parity. When the maximum
   degree is bounded by `Δ`, every clause has width at most `Δ` (`tseitinCNF_width_le`), and an
   assignment satisfies `tseitinCNF G χ` if and only if it satisfies `tseitinLinSys G χ`
   (`satVertexCNF_iff_satLinEq`, `satCNF_iff_satLinSys`).

We then construct the Ben-Sasson–Wigderson (2001, Section 4) subadditive semantic complexity
measure `tseitinMeasure G χ : SubadditiveMeasure (tseitinCNF G χ)` and prove the single-edge flip
boundary-covering lemma (`edgeBoundary_subset_clauseVars_of_minimal`): for any minimal vertex set
`U` semantically entailing a clause `c`, every edge in `edgeBoundary G U` must appear in
`clauseVars c`. Combining this with edge expansion (`IsEdgeExpander`) and
`Mathmatica.ExpanderWidth.boundary_expansion_dag_size_lower_bound` yields an end-to-end
exponential size lower bound for all general DAG resolution (CDCL) refutations of Tseitin formulas
on bounded-degree edge expanders (`tseitin_expander_cdcl_lower_bound`).

## Main definitions

* `IndexedGraph V E`: A finite loopless multigraph with `V` vertices and `E` edges.
* `incidentEdges G v`: The set of edges incident to vertex `v`.
* `edgeBoundary G U`: The set of edges with exactly one endpoint in `U`.
* `IsEdgeExpander G c q`: Edge expansion with rational expansion ratio `c / q`.
* `tseitinLinEq G χ v` and `tseitinLinSys G χ`: `GF(2)`-linear encoding of Tseitin constraints.
* `tseitinVertexCNF G χ v` and `tseitinCNF G χ`: Boolean CNF encoding of Tseitin constraints.
* `Entails G χ U c`: Semantic entailment of clause `c` by vertex constraints in `U`.
* `tseitinMeasure G χ`: Subadditive complexity measure on `tseitinCNF G χ`.

## Main results

* `edgeBoundary_compl`: `edgeBoundary G Uᶜ = edgeBoundary G U`.
* `tseitin_f2_zero_blowup`: `(gaussElimList vs (tseitinLinSys G χ)).length ≤ V`.
* `tseitinCNF_width_le`: Bounded vertex degree `≤ Δ` implies CNF clause width `≤ Δ`.
* `satVertexCNF_iff_satLinEq`: Dual-basis semantic equivalence at each vertex.
* `edgeBoundary_subset_clauseVars_of_minimal`: Minimal entailing sets have their edge boundary
  contained in `clauseVars c`.
* `tseitinMeasure_empty_ge`: Any edge expander with positive expansion satisfies
  `V ≤ (tseitinMeasure G χ).μ ∅`.
* `tseitin_hasBoundaryExpansion`: Edge expansion implies `HasBoundaryExpansion`.
* `tseitin_expander_cdcl_lower_bound`: End-to-end exponential size lower bound for general DAG
  resolution / CDCL refutations of Tseitin formulas on bounded-degree edge expanders.

## References

* E. Ben-Sasson and A. Wigderson, *Short proofs are narrow — resolution made simple*,
  Journal of the ACM 48 (2001), no. 2, 149–169.
-/

namespace Mathmatica.TseitinExpander

open Mathmatica.BSWTradeoff
open Mathmatica.DAGResolution
open Mathmatica.BSWDAGFull
open Mathmatica.ExpanderWidth
open Mathmatica.XORSATBasis

/-! ### Finite loopless graphs and edge boundaries -/

/-- A finite loopless graph with `V` vertices (`Fin V`) and `E` edges (`Fin E`). -/
structure IndexedGraph (V E : ℕ) where
  /-- The pair of endpoint vertices of each edge. -/
  endpoints : Fin E → Fin V × Fin V
  /-- Every edge connects two distinct vertices. -/
  loopless : ∀ e : Fin E, (endpoints e).1 ≠ (endpoints e).2

/-- The finite set of edges incident to vertex `v` in `G`. -/
def incidentEdges {V E : ℕ} (G : IndexedGraph V E) (v : Fin V) : Finset (Fin E) :=
  Finset.univ.filter (fun e => (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v)

@[simp]
lemma mem_incidentEdges {V E : ℕ} (G : IndexedGraph V E) {v : Fin V} {e : Fin E} :
    e ∈ incidentEdges G v ↔ (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v := by
  simp [incidentEdges]

/-- The edge boundary of a vertex subset `U`: the set of edges having exactly one endpoint
in `U`. -/
def edgeBoundary {V E : ℕ} (G : IndexedGraph V E) (U : Finset (Fin V)) : Finset (Fin E) :=
  Finset.univ.filter (fun e =>
    ((G.endpoints e).1 ∈ U ∧ (G.endpoints e).2 ∉ U) ∨
    ((G.endpoints e).1 ∉ U ∧ (G.endpoints e).2 ∈ U))

@[simp]
lemma mem_edgeBoundary {V E : ℕ} (G : IndexedGraph V E) {U : Finset (Fin V)} {e : Fin E} :
    e ∈ edgeBoundary G U ↔
      ((G.endpoints e).1 ∈ U ∧ (G.endpoints e).2 ∉ U) ∨
      ((G.endpoints e).1 ∉ U ∧ (G.endpoints e).2 ∈ U) := by
  simp [edgeBoundary]

/-- The edge boundary of a vertex subset equals the edge boundary of its complement. -/
theorem edgeBoundary_compl {V E : ℕ} (G : IndexedGraph V E) (U : Finset (Fin V)) :
    edgeBoundary G Uᶜ = edgeBoundary G U := by
  ext e
  simp only [mem_edgeBoundary, Finset.mem_compl]
  tauto

/-- A graph `G` is a `(c / q)`-edge expander if `0 < q` and every vertex subset `U` of size at
most `V / 2` satisfies `c * U.card ≤ q * (edgeBoundary G U).card`. -/
def IsEdgeExpander {V E : ℕ} (G : IndexedGraph V E) (c q : ℕ) : Prop :=
  0 < q ∧ ∀ U : Finset (Fin V), 2 * U.card ≤ V → c * U.card ≤ q * (edgeBoundary G U).card

/-- Every edge in `edgeBoundary G U` has a unique endpoint `u ∈ U`, is incident to `u`, and is
not incident to any other vertex in `U.erase u`. -/
private lemma exists_unique_endpoint_of_mem_edgeBoundary {V E : ℕ} (G : IndexedGraph V E)
    {U : Finset (Fin V)} {e : Fin E} (he : e ∈ edgeBoundary G U) :
    ∃ u ∈ U, e ∈ incidentEdges G u ∧ ∀ v ∈ U.erase u, e ∉ incidentEdges G v := by
  rw [mem_edgeBoundary] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(G.endpoints e).1, h1, (mem_incidentEdges G).mpr (Or.inl rfl), ?_⟩
    intro v hv hinc
    obtain ⟨hne, hvU⟩ := Finset.mem_erase.mp hv
    rcases (mem_incidentEdges G).mp hinc with h | h
    · exact hne h.symm
    · exact h2 (h.symm ▸ hvU)
  · refine ⟨(G.endpoints e).2, h2, (mem_incidentEdges G).mpr (Or.inr rfl), ?_⟩
    intro v hv hinc
    obtain ⟨hne, hvU⟩ := Finset.mem_erase.mp hv
    rcases (mem_incidentEdges G).mp hinc with h | h
    · exact h1 (h.symm ▸ hvU)
    · exact hne h.symm

/-! ### Dual-basis encoding of Tseitin formulas -/

/-- The `GF(2)`-linear equation associated with vertex `v` in the Tseitin instance `(G, χ)`. -/
def tseitinLinEq {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) (v : Fin V) : LinEq E :=
  ⟨incidentEdges G v, χ v⟩

/-- The `GF(2)`-linear system encoding all vertex parity constraints of the Tseitin instance
`(G, χ)`. -/
def tseitinLinSys {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) : LinSys E :=
  (List.finRange V).map (tseitinLinEq G χ)

/-- **Zero-Bloat Renormalization in the `GF(2)`-Linear Basis**: Pivot Gaussian elimination along
any sequence of edges never exceeds `V` equations. -/
theorem tseitin_f2_zero_blowup {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (vs : List (Fin E)) :
    (gaussElimList vs (tseitinLinSys G χ)).length ≤ V := by
  calc
    (gaussElimList vs (tseitinLinSys G χ)).length
        ≤ (tseitinLinSys G χ).length := gaussElimList_length_le vs (tseitinLinSys G χ)
    _ = V := by simp [tseitinLinSys]

/-- Gaussian elimination on `tseitinLinSys G χ` preserves exact satisfiability. -/
theorem tseitin_f2_equisatisfiable {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (vs : List (Fin E)) :
    Satisfiable (gaussElimList vs (tseitinLinSys G χ)) ↔ Satisfiable (tseitinLinSys G χ) :=
  gaussElimList_equisatisfiable vs (tseitinLinSys G χ)

/-- The full-polarity clause over variable set `I` that forbids the assignment `e ↦ decide (e ∈ S)`
on `I`. -/
def forbidClause {E : ℕ} (I S : Finset (Fin E)) : Clause E :=
  I.image (fun e => Lit.mk e (decide (e ∉ S)))

/-- The CNF encoding of the vertex parity constraint at `v`: all full-polarity clauses on
`incidentEdges G v` forbidding assignments whose XOR parity differs from `χ v`. -/
def tseitinVertexCNF {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) (v : Fin V) : CNF E :=
  ((incidentEdges G v).powerset.filter
    (fun S => evalXor (fun e => decide (e ∈ S)) (incidentEdges G v) != χ v)).image
    (forbidClause (incidentEdges G v))

/-- The CNF encoding of the Tseitin instance `(G, χ)` as the union of all vertex CNFs. -/
def tseitinCNF {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) : CNF E :=
  Finset.univ.biUnion (tseitinVertexCNF G χ)

/-- Satisfaction of a propositional clause `c` under a Boolean assignment `σ`. -/
def SatClause {E : ℕ} (σ : Assign E) (c : Clause E) : Prop :=
  ∃ l ∈ c, σ l.var = l.pol

/-- Satisfaction of a CNF formula `φ` under a Boolean assignment `σ`. -/
def SatCNF {E : ℕ} (σ : Assign E) (φ : CNF E) : Prop :=
  ∀ c ∈ φ, SatClause σ c

/-- If every vertex in `G` has degree at most `Δ`, then every clause in `tseitinCNF G χ` has
cardinality at most `Δ`. -/
theorem tseitinCNF_width_le {V E Δ : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (hdeg : ∀ v : Fin V, (incidentEdges G v).card ≤ Δ) :
    ∀ c ∈ tseitinCNF G χ, c.card ≤ Δ := by
  intro c hc
  rw [tseitinCNF, Finset.mem_biUnion] at hc
  obtain ⟨v, _, hcv⟩ := hc
  rw [tseitinVertexCNF, Finset.mem_image] at hcv
  obtain ⟨S, _, rfl⟩ := hcv
  exact le_trans Finset.card_image_le (hdeg v)

/-- **Dual-Basis Semantic Equivalence (Vertex Level)**: An assignment `σ` satisfies the CNF
encoding `tseitinVertexCNF G χ v` if and only if it satisfies the `GF(2)`-linear equation
`tseitinLinEq G χ v`. -/
theorem satVertexCNF_iff_satLinEq {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (σ : Assign E) (v : Fin V) :
    SatCNF σ (tseitinVertexCNF G χ v) ↔ SatEq σ (tseitinLinEq G χ v) := by
  set I := incidentEdges G v
  constructor
  · intro hsat
    by_contra hne
    unfold SatEq tseitinLinEq at hne
    set S : Finset (Fin E) := I.filter (fun e => σ e = true)
    have hS_sub : S ⊆ I := Finset.filter_subset _ I
    have hcongr : ∀ e ∈ I, (decide (e ∈ S)) = σ e := by
      intro e he
      simp [S, he]
    have hxor : evalXor (fun e => decide (e ∈ S)) I = evalXor σ I :=
      evalXor_congr hcongr
    have hmem : forbidClause I S ∈ tseitinVertexCNF G χ v := by
      rw [tseitinVertexCNF, Finset.mem_image]
      refine ⟨S, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hS_sub, ?_⟩
      rw [hxor]
      simpa [bne_iff_ne] using hne
    obtain ⟨l, hl, hσl⟩ := hsat (forbidClause I S) hmem
    rw [forbidClause, Finset.mem_image] at hl
    obtain ⟨e, heI, rfl⟩ := hl
    dsimp only at hσl
    have hde := hcongr e heI
    have hnot : decide (e ∉ S) = !(decide (e ∈ S)) := by simp
    rw [hnot, hde] at hσl
    cases h : σ e <;> simp [h] at hσl
  · intro hsat c hc
    unfold SatEq tseitinLinEq at hsat
    rw [tseitinVertexCNF, Finset.mem_image] at hc
    obtain ⟨S, hS, rfl⟩ := hc
    rw [Finset.mem_filter] at hS
    have hne : evalXor (fun e => decide (e ∈ S)) I ≠ χ v := by
      simpa [bne_iff_ne] using hS.2
    have hdiff : ∃ e ∈ I, σ e ≠ decide (e ∈ S) := by
      by_contra hall
      push Not at hall
      have hEq : evalXor σ I = evalXor (fun e => decide (e ∈ S)) I :=
        evalXor_congr hall
      exact hne (hEq.symm.trans hsat)
    obtain ⟨e, heI, hne_e⟩ := hdiff
    refine ⟨Lit.mk e (decide (e ∉ S)), ?_, ?_⟩
    · rw [forbidClause, Finset.mem_image]
      exact ⟨e, heI, rfl⟩
    · dsimp only
      have hnot : decide (e ∉ S) = !(decide (e ∈ S)) := by simp
      rw [hnot]
      cases h1 : σ e <;> cases h2 : decide (e ∈ S) <;> simp [h1, h2] at hne_e ⊢

/-- **Dual-Basis Semantic Equivalence (Global Level)**: An assignment `σ` satisfies `tseitinCNF G χ`
if and only if it satisfies `tseitinLinSys G χ`. -/
theorem satCNF_iff_satLinSys {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) (σ : Assign E) :
    SatCNF σ (tseitinCNF G χ) ↔ SatSys σ (tseitinLinSys G χ) := by
  constructor
  · intro hsat eq heq
    rw [tseitinLinSys, List.mem_map] at heq
    obtain ⟨v, _, rfl⟩ := heq
    refine (satVertexCNF_iff_satLinEq G χ σ v).mp ?_
    intro c hc
    exact hsat c (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hc⟩)
  · intro hsat c hc
    rw [tseitinCNF, Finset.mem_biUnion] at hc
    obtain ⟨v, _, hcv⟩ := hc
    have hveq : SatEq σ (tseitinLinEq G χ v) :=
      hsat (tseitinLinEq G χ v) (List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩)
    exact (satVertexCNF_iff_satLinEq G χ σ v).mpr hveq c hcv

/-! ### Ben-Sasson–Wigderson subadditive semantic complexity measure -/

/-- A vertex subset `U` semantically entails a clause `c` under `(G, χ)` if every assignment
satisfying all vertex parity constraints in `U` also satisfies `c`. -/
def Entails {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (U : Finset (Fin V)) (c : Clause E) : Prop :=
  ∀ σ : Assign E, (∀ v ∈ U, SatEq σ (tseitinLinEq G χ v)) → SatClause σ c

/-- Semantic resolution soundness: if `U₁` entails `c₁` and `U₂` entails `c₂`, then `U₁ ∪ U₂`
entails any resolvent `c` of `c₁` and `c₂`. -/
lemma entails_of_isResolvent {V E : ℕ} {G : IndexedGraph V E} {χ : Fin V → Bool}
    {U₁ U₂ : Finset (Fin V)} {c₁ c₂ c : Clause E}
    (h₁ : Entails G χ U₁ c₁) (h₂ : Entails G χ U₂ c₂) (hres : IsResolvent c₁ c₂ c) :
    Entails G χ (U₁ ∪ U₂) c := by
  obtain ⟨e, _, _, rfl⟩ := hres
  intro σ hσ
  have hσ₁ : SatClause σ c₁ := h₁ σ (fun v hv => hσ v (Finset.mem_union_left U₂ hv))
  have hσ₂ : SatClause σ c₂ := h₂ σ (fun v hv => hσ v (Finset.mem_union_right U₁ hv))
  cases he : σ e
  · obtain ⟨l, hl, hσl⟩ := hσ₁
    have hne : l ≠ Lit.mk e true := by
      intro h
      subst h
      simp [he] at hσl
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hl⟩), hσl⟩
  · obtain ⟨l, hl, hσl⟩ := hσ₂
    have hne : l ≠ Lit.mk e false := by
      intro h
      subst h
      simp [he] at hσl
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hl⟩), hσl⟩

/-- The finite set of all vertex subsets `U ⊆ Fin V` semantically entailing clause `c`. -/
private noncomputable def entailingSets {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (c : Clause E) : Finset (Finset (Fin V)) :=
  letI := Classical.decPred (fun U : Finset (Fin V) => Entails G χ U c)
  (Finset.univ : Finset (Fin V)).powerset.filter (fun U => Entails G χ U c)

private lemma mem_entailingSets {V E : ℕ} {G : IndexedGraph V E} {χ : Fin V → Bool}
    {c : Clause E} {U : Finset (Fin V)} :
    U ∈ entailingSets G χ c ↔ Entails G χ U c := by
  classical
  unfold entailingSets
  simp

/-- The minimum cardinality of a vertex subset `U ⊆ Fin V` semantically entailing clause `c`, or
`V + 1` if no such subset exists. -/
noncomputable def tseitinMeasureVal {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (c : Clause E) : ℕ :=
  if h : (entailingSets G χ c).Nonempty then
    ((entailingSets G χ c).image Finset.card).min' (h.image Finset.card)
  else
    V + 1

/-- If `U` semantically entails `c`, then `tseitinMeasureVal G χ c ≤ U.card`. -/
lemma tseitinMeasureVal_le_card {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    {U : Finset (Fin V)} {c : Clause E} (hent : Entails G χ U c) :
    tseitinMeasureVal G χ c ≤ U.card := by
  have hU : U ∈ entailingSets G χ c := mem_entailingSets.mpr hent
  have hne : (entailingSets G χ c).Nonempty := ⟨U, hU⟩
  unfold tseitinMeasureVal
  simp only [hne, ↓reduceDIte]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)

/-- `tseitinMeasureVal G χ c` is always at most `V + 1`. -/
lemma tseitinMeasureVal_le_succ {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    (c : Clause E) :
    tseitinMeasureVal G χ c ≤ V + 1 := by
  unfold tseitinMeasureVal
  by_cases hne : (entailingSets G χ c).Nonempty
  · simp only [hne, ↓reduceDIte]
    have hmem :=
      Finset.min'_mem ((entailingSets G χ c).image Finset.card) (hne.image Finset.card)
    obtain ⟨U, _, hcard⟩ := Finset.mem_image.mp hmem
    have hle : U.card ≤ V := by
      simpa using Finset.card_le_univ U
    omega
  · simp only [hne, ↓reduceDIte]
    exact le_rfl

/-- Whenever `tseitinMeasureVal G χ c ≤ V`, there exists a minimal vertex subset `U` entailing `c`
whose cardinality equals `tseitinMeasureVal G χ c`. -/
theorem exists_minimal_entailing_of_le {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool)
    {c : Clause E} (hle : tseitinMeasureVal G χ c ≤ V) :
    ∃ U : Finset (Fin V),
      Entails G χ U c ∧
      U.card = tseitinMeasureVal G χ c ∧
      ∀ u ∈ U, ¬ Entails G χ (U.erase u) c := by
  have hne : (entailingSets G χ c).Nonempty := by
    by_contra hemp
    have hval : tseitinMeasureVal G χ c = V + 1 := by
      unfold tseitinMeasureVal
      simp only [hemp, ↓reduceDIte]
    omega
  have hval : tseitinMeasureVal G χ c =
      ((entailingSets G χ c).image Finset.card).min' (hne.image Finset.card) := by
    unfold tseitinMeasureVal
    simp only [hne, ↓reduceDIte]
  have hmem :=
    Finset.min'_mem ((entailingSets G χ c).image Finset.card) (hne.image Finset.card)
  obtain ⟨U, hUmem, hUcard⟩ := Finset.mem_image.mp hmem
  have hUent : Entails G χ U c := mem_entailingSets.mp hUmem
  refine ⟨U, hUent, hUcard.trans hval.symm, ?_⟩
  intro u hu hErase
  have hle' : tseitinMeasureVal G χ c ≤ (U.erase u).card :=
    tseitinMeasureVal_le_card G χ hErase
  have hlt : (U.erase u).card < U.card := Finset.card_erase_lt_of_mem hu
  omega

/-- **BSW Subadditive Semantic Measure for Tseitin Formulas**: `tseitinMeasureVal` satisfies
`axiom_le_one`, `weaken_le`, and `resolve_le` for `tseitinCNF G χ`. -/
noncomputable def tseitinMeasure {V E : ℕ} (G : IndexedGraph V E) (χ : Fin V → Bool) :
    SubadditiveMeasure (tseitinCNF G χ) where
  μ := tseitinMeasureVal G χ
  axiom_le_one := by
    intro c hc
    rw [tseitinCNF, Finset.mem_biUnion] at hc
    obtain ⟨v, _, hcv⟩ := hc
    have hent : Entails G χ {v} c := by
      intro σ hσ
      have hveq : SatEq σ (tseitinLinEq G χ v) := hσ v (Finset.mem_singleton_self v)
      exact (satVertexCNF_iff_satLinEq G χ σ v).mpr hveq c hcv
    simpa using tseitinMeasureVal_le_card G χ hent
  weaken_le := by
    intro c₁ c₂ hsub
    by_cases hle : tseitinMeasureVal G χ c₁ ≤ V
    · obtain ⟨U, hUent, hUcard, _⟩ := exists_minimal_entailing_of_le G χ hle
      have hUent₂ : Entails G χ U c₂ := by
        intro σ hσ
        obtain ⟨l, hl, hσl⟩ := hUent σ hσ
        exact ⟨l, hsub hl, hσl⟩
      exact hUcard ▸ tseitinMeasureVal_le_card G χ hUent₂
    · have hge : V + 1 ≤ tseitinMeasureVal G χ c₁ := by omega
      exact le_trans (tseitinMeasureVal_le_succ G χ c₂) hge
  resolve_le := by
    intro c₁ c₂ c hres
    by_cases h₁ : tseitinMeasureVal G χ c₁ ≤ V
    · by_cases h₂ : tseitinMeasureVal G χ c₂ ≤ V
      · obtain ⟨U₁, hU₁ent, hU₁card, _⟩ := exists_minimal_entailing_of_le G χ h₁
        obtain ⟨U₂, hU₂ent, hU₂card, _⟩ := exists_minimal_entailing_of_le G χ h₂
        have hent : Entails G χ (U₁ ∪ U₂) c := entails_of_isResolvent hU₁ent hU₂ent hres
        calc
          tseitinMeasureVal G χ c ≤ (U₁ ∪ U₂).card := tseitinMeasureVal_le_card G χ hent
          _ ≤ U₁.card + U₂.card := Finset.card_union_le U₁ U₂
          _ = tseitinMeasureVal G χ c₁ + tseitinMeasureVal G χ c₂ := by rw [hU₁card, hU₂card]
      · have hle := tseitinMeasureVal_le_succ G χ c
        omega
    · have hle := tseitinMeasureVal_le_succ G χ c
      omega

/-! ### Edge-boundary covering lemma and end-to-end CDCL lower bound -/

/-- The finite set of edge variables occurring in a clause `c`. -/
def clauseVars {E : ℕ} (c : Clause E) : Finset (Fin E) :=
  c.image Lit.var

/-- Flipping an assignment on an edge `e ∈ incidentEdges G u` negates the XOR parity at `u`. -/
private lemma evalXor_flip_incident {V E : ℕ} (G : IndexedGraph V E) (σ : Assign E)
    {u : Fin V} {e : Fin E} (he : e ∈ incidentEdges G u) :
    evalXor (updateAssign σ e (!σ e)) (incidentEdges G u) =
      !(evalXor σ (incidentEdges G u)) := by
  rw [evalXor_update_mem σ (!σ e) he, evalXor_erase σ he]
  cases σ e <;> cases evalXor σ ((incidentEdges G u).erase e) <;> rfl

/-- **Edge-Boundary Covering Lemma (Single-Edge Flip Argument)**:
If `U` is a minimal vertex subset semantically entailing a clause `c`, then every edge in
`edgeBoundary G U` must appear among the variables `clauseVars c`. -/
theorem edgeBoundary_subset_clauseVars_of_minimal {V E : ℕ}
    (G : IndexedGraph V E) (χ : Fin V → Bool) {U : Finset (Fin V)} {c : Clause E}
    (hent : Entails G χ U c)
    (hmin : ∀ u ∈ U, ¬ Entails G χ (U.erase u) c) :
    edgeBoundary G U ⊆ clauseVars c := by
  intro e he
  by_contra hnotvar
  obtain ⟨u, huU, heu, he_other⟩ := exists_unique_endpoint_of_mem_edgeBoundary G he
  have hnotent : ¬ Entails G χ (U.erase u) c := hmin u huU
  unfold Entails at hnotent
  push Not at hnotent
  obtain ⟨σ, hσ_erase, hσ_not_c⟩ := hnotent
  have hσ_not_u : ¬ SatEq σ (tseitinLinEq G χ u) := by
    intro hσu
    apply hσ_not_c
    apply hent σ
    intro v hv
    by_cases hvu : v = u
    · exact hvu ▸ hσu
    · exact hσ_erase v (Finset.mem_erase.mpr ⟨hvu, hv⟩)
  let σ' : Assign E := updateAssign σ e (!σ e)
  have hσ'_U : ∀ v ∈ U, SatEq σ' (tseitinLinEq G χ v) := by
    intro v hv
    by_cases hvu : v = u
    · subst hvu
      unfold SatEq tseitinLinEq at hσ_not_u ⊢
      rw [evalXor_flip_incident G σ heu]
      cases hx : evalXor σ (incidentEdges G v) <;> cases hχ : χ v <;> simp [hx, hχ] at hσ_not_u ⊢
    · have hv_er : v ∈ U.erase u := Finset.mem_erase.mpr ⟨hvu, hv⟩
      have hnotinc : e ∉ incidentEdges G v := he_other v hv_er
      have hsatv := hσ_erase v hv_er
      unfold SatEq tseitinLinEq at hsatv ⊢
      simpa only [σ', evalXor_update_not_mem σ (!σ e) hnotinc] using hsatv
  obtain ⟨l, hl, hσ'l⟩ := hent σ' hσ'_U
  have hne : l.var ≠ e := fun h => hnotvar (Finset.mem_image.mpr ⟨l, hl, h⟩)
  have hσl : σ l.var = l.pol := by
    simpa [σ', updateAssign, hne] using hσ'l
  exact hσ_not_c ⟨l, hl, hσl⟩

/-- In an edge expander with positive expansion `0 < c_exp`, every nonempty proper vertex subset
has a nonempty edge boundary. -/
private lemma edgeBoundary_nonempty_of_isEdgeExpander {V E c_exp q : ℕ}
    {G : IndexedGraph V E} (hexp : IsEdgeExpander G c_exp q) (hc_pos : 0 < c_exp)
    {U : Finset (Fin V)} (hne : U.Nonempty) (hlt : U.card < V) :
    (edgeBoundary G U).Nonempty := by
  by_cases hhalf : 2 * U.card ≤ V
  · have hbound : c_exp * U.card ≤ q * (edgeBoundary G U).card := hexp.2 U hhalf
    have hpos : 0 < c_exp * U.card := Nat.mul_pos hc_pos (Finset.card_pos.mpr hne)
    exact Finset.card_pos.mp (Nat.pos_of_mul_pos_left (lt_of_lt_of_le hpos hbound))
  · have hcompl_card : Uᶜ.card = V - U.card := by
      simpa using Finset.card_compl U
    have hhalf' : 2 * Uᶜ.card ≤ V := by omega
    have hpos_compl : 0 < Uᶜ.card := by omega
    have hbound : c_exp * Uᶜ.card ≤ q * (edgeBoundary G Uᶜ).card := hexp.2 Uᶜ hhalf'
    rw [edgeBoundary_compl] at hbound
    have hpos : 0 < c_exp * Uᶜ.card := Nat.mul_pos hc_pos hpos_compl
    exact Finset.card_pos.mp (Nat.pos_of_mul_pos_left (lt_of_lt_of_le hpos hbound))

/-- In an edge expander with positive expansion, every proper subset `U` of vertices is
simultaneously satisfiable. -/
private lemma exists_sat_proper_subset_of_isEdgeExpander {V E c_exp q : ℕ}
    {G : IndexedGraph V E} (χ : Fin V → Bool)
    (hexp : IsEdgeExpander G c_exp q) (hc_pos : 0 < c_exp) :
    ∀ (m : ℕ) (U : Finset (Fin V)), U.card = m → U.card < V →
      ∃ σ : Assign E, ∀ v ∈ U, SatEq σ (tseitinLinEq G χ v) := by
  intro m
  induction m with
  | zero =>
    intro U hcard _
    have hemp : U = ∅ := Finset.card_eq_zero.mp hcard
    subst hemp
    exact ⟨fun _ => false, by simp⟩
  | succ m ih =>
    intro U hcard hlt
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := edgeBoundary_nonempty_of_isEdgeExpander hexp hc_pos hne hlt
    obtain ⟨u, huU, heu, he_other⟩ := exists_unique_endpoint_of_mem_edgeBoundary G he
    have herase_card : (U.erase u).card = m := by
      have := Finset.card_erase_of_mem huU
      omega
    obtain ⟨σ, hσ⟩ := ih (U.erase u) herase_card (by omega)
    by_cases hsat_u : SatEq σ (tseitinLinEq G χ u)
    · refine ⟨σ, fun v hv => ?_⟩
      by_cases hvu : v = u
      · exact hvu ▸ hsat_u
      · exact hσ v (Finset.mem_erase.mpr ⟨hvu, hv⟩)
    · refine ⟨updateAssign σ e (!σ e), fun v hv => ?_⟩
      by_cases hvu : v = u
      · subst hvu
        unfold SatEq tseitinLinEq at hsat_u ⊢
        rw [evalXor_flip_incident G σ heu]
        cases hx : evalXor σ (incidentEdges G v) <;> cases hχ : χ v <;>
          simp [hx, hχ] at hsat_u ⊢
      · have hv_er : v ∈ U.erase u := Finset.mem_erase.mpr ⟨hvu, hv⟩
        have hnotinc : e ∉ incidentEdges G v := he_other v hv_er
        have hsatv := hσ v hv_er
        unfold SatEq tseitinLinEq at hsatv ⊢
        simpa only [evalXor_update_not_mem σ (!σ e) hnotinc] using hsatv

/-- In an edge expander with positive expansion, no proper vertex subset entails the empty clause,
so `(tseitinMeasure G χ).μ ∅ ≥ V`. -/
theorem tseitinMeasure_empty_ge {V E c_exp q : ℕ}
    {G : IndexedGraph V E} (χ : Fin V → Bool)
    (hexp : IsEdgeExpander G c_exp q) (hc_pos : 0 < c_exp) :
    V ≤ (tseitinMeasure G χ).μ ∅ := by
  by_contra hlt
  have hle : tseitinMeasureVal G χ ∅ ≤ V := by
    change (tseitinMeasure G χ).μ ∅ ≤ V
    omega
  obtain ⟨U, hUent, hUcard, _⟩ := exists_minimal_entailing_of_le G χ hle
  have hUlt : U.card < V := by
    change U.card = (tseitinMeasure G χ).μ ∅ at hUcard
    omega
  obtain ⟨σ, hσ⟩ :=
    exists_sat_proper_subset_of_isEdgeExpander χ hexp hc_pos U.card U rfl hUlt
  obtain ⟨l, hl, _⟩ := hUent σ hσ
  exact Finset.notMem_empty l hl

/-- **Boundary Expansion for Tseitin Formulas on Edge Expanders**:
If `G` is a `(c_exp / q)`-edge expander, `3 * T ≤ V`, and `q * W ≤ c_exp * T`, then
`tseitinMeasure G χ` satisfies `HasBoundaryExpansion (tseitinMeasure G χ) T W`. -/
theorem tseitin_hasBoundaryExpansion {V E c_exp q T W : ℕ}
    {G : IndexedGraph V E} (χ : Fin V → Bool)
    (hexp : IsEdgeExpander G c_exp q) (hTV : 3 * T ≤ V) (hW : q * W ≤ c_exp * T) :
    HasBoundaryExpansion (tseitinMeasure G χ) T W := by
  intro c hgt hle
  have hleV : tseitinMeasureVal G χ c ≤ V := by
    change (tseitinMeasure G χ).μ c ≤ 2 * T at hle
    exact le_trans hle (by omega)
  obtain ⟨U, hUent, hUcard, hUmin⟩ := exists_minimal_entailing_of_le G χ hleV
  change U.card = (tseitinMeasure G χ).μ c at hUcard
  have hbd_le : (edgeBoundary G U).card ≤ c.card :=
    le_trans (Finset.card_le_card (edgeBoundary_subset_clauseVars_of_minimal G χ hUent hUmin))
      Finset.card_image_le
  have hqW : q * W ≤ q * c.card := by
    by_cases hhalf : 2 * U.card ≤ V
    · have hTU : T ≤ U.card := by
        change T < (tseitinMeasure G χ).μ c at hgt
        omega
      calc
        q * W ≤ c_exp * T := hW
        _ ≤ c_exp * U.card := Nat.mul_le_mul_left c_exp hTU
        _ ≤ q * (edgeBoundary G U).card := hexp.2 U hhalf
        _ ≤ q * c.card := Nat.mul_le_mul_left q hbd_le
    · have hcompl_card : Uᶜ.card = V - U.card := by
        simpa using Finset.card_compl U
      have hhalf' : 2 * Uᶜ.card ≤ V := by omega
      have hTUc : T ≤ Uᶜ.card := by
        change (tseitinMeasure G χ).μ c ≤ 2 * T at hle
        omega
      calc
        q * W ≤ c_exp * T := hW
        _ ≤ c_exp * Uᶜ.card := Nat.mul_le_mul_left c_exp hTUc
        _ ≤ q * (edgeBoundary G Uᶜ).card := hexp.2 Uᶜ hhalf'
        _ = q * (edgeBoundary G U).card := by rw [edgeBoundary_compl]
        _ ≤ q * c.card := Nat.mul_le_mul_left q hbd_le
  exact Nat.le_of_mul_le_mul_left hqW hexp.1

/-- **End-to-End Exponential CDCL / General DAG Resolution Lower Bound for Tseitin Formulas on
Edge Expanders**:
For any bounded-degree `(c_exp / q)`-edge expander `G` (`0 < c_exp`, degree `≤ Δ`) and any charge
assignment `χ`, every general DAG resolution refutation `π` (and hence every CDCL proof) of
`tseitinCNF G χ` satisfies the exponential size lower bound
`(2 * E) ^ r ≤ (2 * E - k) ^ r * dagSize π`, in stark contrast to `tseitin_f2_zero_blowup`
in the `GF(2)`-linear basis. -/
theorem tseitin_expander_cdcl_lower_bound {V E Δ c_exp q k r T : ℕ}
    (hE : 0 < E) (hk_pos : 0 < k) (hk : k ≤ 2 * E)
    (G : IndexedGraph V E) (χ : Fin V → Bool)
    (hdeg : ∀ v : Fin V, (incidentEdges G v).card ≤ Δ)
    (hexp : IsEdgeExpander G c_exp q) (hc_pos : 0 < c_exp)
    (hT : 1 ≤ T) (hTV : 3 * T ≤ V)
    (hW : q * (max Δ k + r + 1) ≤ c_exp * T)
    (π : List (Clause E)) (hπ : IsDAGRefutation (tseitinCNF G χ) π) :
    (2 * E) ^ r ≤ (2 * E - k) ^ r * dagSize π := by
  have hEmpty : T < (tseitinMeasure G χ).μ ∅ :=
    lt_of_lt_of_le (by omega) (tseitinMeasure_empty_ge χ hexp hc_pos)
  exact boundary_expansion_dag_size_lower_bound hE hk_pos hk
    (tseitinCNF G χ) (tseitinCNF_width_le G χ hdeg)
    (tseitinMeasure G χ) hT hEmpty
    (tseitin_hasBoundaryExpansion χ hexp hTV hW)
    π hπ

end Mathmatica.TseitinExpander
