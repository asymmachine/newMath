/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.BSWDAGFull

/-!
# Subadditive Complexity Measures and Boundary-Expansion Lower Bounds

This module formalizes the Ben-Sasson–Wigderson (2001, Section 4) framework linking subadditive
complexity measures, boundary expansion, resolution width lower bounds, and exponential size lower
bounds for general DAG resolution (the proof-theoretic model of CDCL SAT solvers).

Given any subadditive complexity measure `M` on clauses of a CNF formula `φ` (where axioms have
complexity at most `1`, weakening does not increase complexity, and resolution is subadditive), any
general weak DAG refutation `π` of `φ` must contain an intermediate clause with complexity in
`(T, 2 * T]` for every threshold `1 ≤ T < M.μ ∅`. If every clause in this complexity band has
width at least `W` (the *boundary expansion* property), then every weak DAG refutation of `φ` has
width at least `W`. Combining this with `Mathmatica.BSWDAGFull.bsw_dag_size_lower_bound` yields an
end-to-end exponential size lower bound for all general DAG resolution refutations of `φ`.

## Main definitions

* `SubadditiveMeasure φ`: A subadditive complexity measure `μ : Clause n → ℕ` on clauses of `φ`
  satisfying `axiom_le_one`, `weaken_le`, and `resolve_le`.
* `HasBoundaryExpansion M T W`: The boundary-expansion property stating that every clause `c` with
  `T < M.μ c ≤ 2 * T` has cardinality at least `W`.

## Main results

* `exists_intermediate_measure_in_weak_dag`: Every weak DAG refutation of `φ` contains a clause `c`
  with `T < M.μ c` and `M.μ c ≤ 2 * T` for any `1 ≤ T < M.μ ∅`.
* `exists_half_measure_in_weak_dag`: Corollary for `2 ≤ M.μ ∅` producing a clause `c` with
  `M.μ ∅ < 2 * M.μ c` and `M.μ c ≤ M.μ ∅`.
* `dagWidth_ge_of_boundary_expansion`: Boundary expansion `HasBoundaryExpansion M T W` implies
  `W ≤ dagWidth π` for every weak DAG refutation `π` of `φ`.
* `boundary_expansion_dag_size_lower_bound`: End-to-end exponential size lower bound
  `(2 * n) ^ r ≤ (2 * n - k) ^ r * dagSize π` for every general DAG resolution refutation `π`
  of a bounded-width CNF formula satisfying boundary expansion.

## References

* E. Ben-Sasson and A. Wigderson, *Short proofs are narrow — resolution made simple*,
  Journal of the ACM 48 (2001), no. 2, 149–169.
-/

namespace Mathmatica.ExpanderWidth

open Mathmatica.BSWTradeoff
open Mathmatica.DAGResolution
open Mathmatica.BSWDAGFull

/-! ### Subadditive complexity measures -/

/-- A Ben-Sasson–Wigderson (2001, Section 4) subadditive complexity measure for a CNF formula
`φ`. Every axiom clause has measure at most `1`, clause weakening (`c₁ ⊆ c₂`) does not increase
the measure, and resolution is subadditive (`μ c ≤ μ c₁ + μ c₂`). -/
structure SubadditiveMeasure {n : ℕ} (φ : CNF n) where
  /-- Complexity measure assigned to each clause. -/
  μ : Clause n → ℕ
  /-- Every input clause of `φ` has complexity at most `1`. -/
  axiom_le_one : ∀ c ∈ φ, μ c ≤ 1
  /-- Weakening monotonicity: a weaker (superset) clause has no larger complexity. -/
  weaken_le : ∀ {c₁ c₂ : Clause n}, c₁ ⊆ c₂ → μ c₂ ≤ μ c₁
  /-- Resolution subadditivity: the complexity of a resolvent is at most the sum of its premises'
  complexities. -/
  resolve_le : ∀ {c₁ c₂ c : Clause n}, IsResolvent c₁ c₂ c → μ c ≤ μ c₁ + μ c₂

/-! ### Intermediate-measure clauses in weak DAG refutations -/

/-- **Intermediate-Measure Theorem for General Weak DAG Resolution**:
Let `M` be a subadditive complexity measure for `φ`, and let `T` be any threshold with `1 ≤ T`
and `T < M.μ ∅`. Then every weak DAG resolution refutation `π` of `φ` contains a clause `c ∈ π`
whose complexity lies in the intermediate band `T < M.μ c ≤ 2 * T`. -/
theorem exists_intermediate_measure_in_weak_dag {n T : ℕ} {φ : CNF n}
    (M : SubadditiveMeasure φ) (hT : 1 ≤ T) (hT_lt : T < M.μ ∅)
    {π : List (Clause n)} (hπ : IsWeakDAGRefutation φ π) :
    ∃ c ∈ π, T < M.μ c ∧ M.μ c ≤ 2 * T := by
  have hex : ∃ i : ℕ, ∃ hi : i < π.length, T < M.μ (π[i]'hi) := by
    obtain ⟨i₀, hi₀, heq⟩ := List.mem_iff_getElem.mp hπ.2
    exact ⟨i₀, hi₀, heq.symm ▸ hT_lt⟩
  let i := Nat.find hex
  obtain ⟨hi, hgt⟩ := Nat.find_spec hex
  have hmin : ∀ (j : ℕ) (hj : j < i), M.μ (π[j]'(lt_trans hj hi)) ≤ T := by
    intro j hj
    exact Nat.le_of_not_lt fun hlt => Nat.find_min hex hj ⟨lt_trans hj hi, hlt⟩
  refine ⟨π[i]'hi, List.getElem_mem hi, hgt, ?_⟩
  rcases hπ.1 i hi with hax | ⟨j, hj, hsub⟩ | ⟨j, k, hj, hk, hres⟩
  · have hle : M.μ (π[i]'hi) ≤ 1 := M.axiom_le_one _ hax
    omega
  · have hle : M.μ (π[i]'hi) ≤ M.μ (π[j]'(lt_trans hj hi)) := M.weaken_le hsub
    have hj_le : M.μ (π[j]'(lt_trans hj hi)) ≤ T := hmin j hj
    omega
  · have hle : M.μ (π[i]'hi) ≤ M.μ (π[j]'(lt_trans hj hi)) + M.μ (π[k]'(lt_trans hk hi)) :=
      M.resolve_le hres
    have hj_le : M.μ (π[j]'(lt_trans hj hi)) ≤ T := hmin j hj
    have hk_le : M.μ (π[k]'(lt_trans hk hi)) ≤ T := hmin k hk
    omega

/-- **Half-Measure Corollary**:
If `2 ≤ M.μ ∅`, then every weak DAG resolution refutation `π` of `φ` contains a clause `c ∈ π`
satisfying `M.μ ∅ < 2 * M.μ c` and `M.μ c ≤ M.μ ∅`. -/
theorem exists_half_measure_in_weak_dag {n : ℕ} {φ : CNF n}
    (M : SubadditiveMeasure φ) (hμ : 2 ≤ M.μ ∅)
    {π : List (Clause n)} (hπ : IsWeakDAGRefutation φ π) :
    ∃ c ∈ π, M.μ ∅ < 2 * M.μ c ∧ M.μ c ≤ M.μ ∅ := by
  have hT : 1 ≤ M.μ ∅ / 2 := by omega
  have hT_lt : M.μ ∅ / 2 < M.μ ∅ := by omega
  obtain ⟨c, hcπ, hgt, hle⟩ := exists_intermediate_measure_in_weak_dag M hT hT_lt hπ
  exact ⟨c, hcπ, by omega, by omega⟩

/-! ### Boundary expansion and width lower bounds -/

/-- A CNF formula `φ` satisfies `W`-boundary expansion with respect to a subadditive measure `M`
and threshold `T` if every clause whose complexity lies in `(T, 2 * T]` has cardinality at least
`W`. -/
def HasBoundaryExpansion {n : ℕ} {φ : CNF n} (M : SubadditiveMeasure φ) (T W : ℕ) : Prop :=
  ∀ c : Clause n, T < M.μ c → M.μ c ≤ 2 * T → W ≤ c.card

/-- **Width Lower Bound from Boundary Expansion**:
If `M` is a subadditive complexity measure for `φ` with `1 ≤ T < M.μ ∅` and `W`-boundary
expansion, then every general weak DAG resolution refutation `π` of `φ` has width at least `W`. -/
theorem dagWidth_ge_of_boundary_expansion {n T W : ℕ} {φ : CNF n}
    (M : SubadditiveMeasure φ) (hT : 1 ≤ T) (hT_lt : T < M.μ ∅)
    (hexp : HasBoundaryExpansion M T W)
    {π : List (Clause n)} (hπ : IsWeakDAGRefutation φ π) :
    W ≤ dagWidth π := by
  obtain ⟨c, hcπ, hgt, hle⟩ := exists_intermediate_measure_in_weak_dag M hT hT_lt hπ
  exact le_trans (hexp c hgt hle) (card_le_dagWidth hcπ)

/-! ### End-to-end exponential size lower bound for general DAG resolution -/

/-- **End-to-End Boundary-Expansion Exponential Size Lower Bound for General DAG Resolution**:
Let `0 < n` and `0 < k ≤ 2 * n`. Suppose every clause of `φ` has width at most `w₀`, and `φ`
admits a subadditive complexity measure `M` with `1 ≤ T < M.μ ∅` satisfying
`HasBoundaryExpansion M T (max w₀ k + r + 1)`. Then every general DAG resolution refutation `π`
of `φ` (and hence every CDCL proof of `φ`) satisfies the exponential size lower bound
`(2 * n) ^ r ≤ (2 * n - k) ^ r * dagSize π`. -/
theorem boundary_expansion_dag_size_lower_bound {n k w₀ r T : ℕ}
    (hn : 0 < n) (hk_pos : 0 < k) (hk : k ≤ 2 * n)
    (φ : CNF n) (hφ : ∀ c ∈ φ, c.card ≤ w₀)
    (M : SubadditiveMeasure φ) (hT : 1 ≤ T) (hT_lt : T < M.μ ∅)
    (hexp : HasBoundaryExpansion M T (max w₀ k + r + 1))
    (π : List (Clause n)) (hπ : IsDAGRefutation φ π) :
    (2 * n) ^ r ≤ (2 * n - k) ^ r * dagSize π := by
  refine bsw_dag_size_lower_bound hn hk_pos hk φ hφ ?_ π hπ
  intro π' hπ'
  have hw : max w₀ k + r + 1 ≤ dagWidth π' :=
    dagWidth_ge_of_boundary_expansion M hT hT_lt hexp hπ'
  omega

end Mathmatica.ExpanderWidth
