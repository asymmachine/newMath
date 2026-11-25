/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathmatica.RGComplexity
import Mathmatica.TwoSATPoly
import Mathmatica.BSWTradeoff
import Mathmatica.OGPBarrier
import Mathmatica.ExplicitBarriers

/-!
# Dynamical–Complexity Correspondence: Three Spontaneous Evolution Phases

This module formalizes a unified dynamical-systems framework connecting spontaneous dynamical
regimes of solver evolution to algorithmic complexity regimes:

1. **Abstract Solver Dynamics (`SolverDynamics`)**:
   A state space `M` equipped with a discrete evolution operator `step : M → M`, a target
   predicate `IsTarget : M → Prop`, and iterated orbits `D.orbit x k := D.step^[k] x`.

2. **Phase I — Periodic / Finite-Attractor / Renormalizable Phase (Phase I ⟹ P)**:
   - `HasFiniteAttractor`: an invariant finite set `A : Finset M` entered from every initial
     state within at most `B` steps.
   - `orbit_mem_attractor_of_ge` and `orbit_eventually_periodic_of_finite_attractor`: once
     inside `A`, the orbit remains in `A` and enters a periodic cycle of length at most
     `A.card` (via the pigeonhole principle `Fintype.exists_ne_map_eq_of_card_lt`).
   - `feigenbaum_log_depth_poly`: logarithmic RG depth `n = 2 ^ k` with bounded unstable
     expansion `δ ≤ 2 ^ c` yields polynomial complexity `C k ≤ n ^ c * C₀`.
   - `twoSAT_in_renormalizable_phase`: concrete Phase I witness via `TwoSATPoly`, showing
     that 2-SAT real-space decimation remains closed within `(2 * n + 1) ^ 2` clauses while
     preserving satisfiability.

3. **Phase II — Critical Phase Transition / Symmetry Breaking & OGP Stability Barrier**:
   - `InCriticalOGPPhase`: alias for `OGPBarrier.HasCoupledOGP`.
   - `phase_two_stable_barrier`: any `δ`-stable solver with `ν₁ + δ < ν₂` whose endpoints
     cross the overlap gap must fail on some intermediate instance.
   - `isingChain_in_critical_phase` and `isingChain_phase_two_failure_witness`: concrete
     Phase II witness via the 1D ferromagnetic Ising chain `ExplicitBarriers.isingChainCNF`.

4. **Phase III — Chaotic / Non-Renormalizable Phase (Phase III ⟹ Exponential Barrier)**:
   - `InChaoticResolutionPhase`: initial clause width at most `w₀` together with mandatory
     tree-like resolution width exceeding `w₀ + d`.
   - `phase_three_exponential_barrier`: direct exponential proof-size lower bound
     `2 ^ d < T.size` via `BSWTradeoff.bsw_tree_size_lower_bound`.

5. **Unified Three-Phase Summary (`ThreePhaseSummary`, `three_phase_correspondence`)**:
   Packages the Phase I, Phase II, and Phase III theorems into a single verified interface.
-/

namespace Mathmatica.DynamicalComplexity

open Mathmatica.SAT
open Mathmatica.OverlapGap
open Mathmatica.OGPBarrier
open Mathmatica.ExplicitBarriers

/-! ## 1. Abstract Solver Dynamical System -/

/-- An abstract discrete-time dynamical system modeling a solver evolving on a state space `M`,
equipped with a one-step evolution operator `step` and a target-state predicate `IsTarget`. -/
structure SolverDynamics (M : Type*) where
  /-- One-step evolution operator on the solver state space. -/
  step : M → M
  /-- Predicate identifying valid target (solution) states. -/
  IsTarget : M → Prop

namespace SolverDynamics

/-- The `k`-th iterate of initial state `x` under the solver dynamics `D`. -/
def orbit {M : Type*} (D : SolverDynamics M) (x : M) (k : ℕ) : M :=
  D.step^[k] x

@[simp]
lemma orbit_zero {M : Type*} (D : SolverDynamics M) (x : M) :
    D.orbit x 0 = x :=
  rfl

lemma orbit_succ {M : Type*} (D : SolverDynamics M) (x : M) (k : ℕ) :
    D.orbit x (k + 1) = D.step (D.orbit x k) :=
  Function.iterate_succ_apply' D.step k x

lemma orbit_add {M : Type*} (D : SolverDynamics M) (x : M) (a b : ℕ) :
    D.orbit x (a + b) = D.orbit (D.orbit x a) b := by
  unfold orbit
  rw [Nat.add_comm, Function.iterate_add_apply]

end SolverDynamics

/-! ## 2. Phase I: Periodic / Finite-Attractor / Renormalizable Phase -/

/-- A solver dynamical system `D` has a **finite attractor** `A : Finset M` with entry bound `B`
if `A` is forward-invariant under `D.step` and every initial state enters `A` within at most
`B` steps. -/
def HasFiniteAttractor {M : Type*} (D : SolverDynamics M) (A : Finset M) (B : ℕ) : Prop :=
  (∀ x ∈ A, D.step x ∈ A) ∧ (∀ x : M, ∃ k ≤ B, D.orbit x k ∈ A)

private lemma orbit_mem_of_invariant {M : Type*} {D : SolverDynamics M} {A : Finset M}
    (hInv : ∀ x ∈ A, D.step x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ m : ℕ, D.orbit x m ∈ A := by
  intro m
  induction m with
  | zero => exact hx
  | succ m ih =>
    rw [SolverDynamics.orbit_succ]
    exact hInv _ ih

/-- **Theorem 1a (Finite-Attractor Orbit Confinement)**:
If `HasFiniteAttractor D A B`, then for every initial state `x` and every time step `k ≥ B`,
the orbit state `D.orbit x k` remains inside the finite attractor `A`. -/
theorem orbit_mem_attractor_of_ge {M : Type*} {D : SolverDynamics M} {A : Finset M} {B : ℕ}
    (hA : HasFiniteAttractor D A B) (x : M) {k : ℕ} (hk : B ≤ k) :
    D.orbit x k ∈ A := by
  rcases hA.2 x with ⟨k₀, hk₀, hmem⟩
  have hle : k₀ ≤ k := le_trans hk₀ hk
  have hsplit : k = k₀ + (k - k₀) := (Nat.add_sub_of_le hle).symm
  rw [hsplit, SolverDynamics.orbit_add]
  exact orbit_mem_of_invariant hA.1 hmem (k - k₀)

/-- **Theorem 1b (Eventual Periodicity inside a Finite Attractor)**:
If `HasFiniteAttractor D A B`, then starting from time `B`, the orbit of any initial state `x`
revisits a state within at most `A.card` steps, entering a periodic cycle. -/
theorem orbit_eventually_periodic_of_finite_attractor {M : Type*} {D : SolverDynamics M}
    {A : Finset M} {B : ℕ} (hA : HasFiniteAttractor D A B) (x : M) :
    ∃ i j, i < j ∧ j ≤ A.card ∧ D.orbit x (B + i) = D.orbit x (B + j) := by
  let f : Fin (A.card + 1) → {y : M // y ∈ A} := fun t =>
    ⟨D.orbit x (B + t.val), orbit_mem_attractor_of_ge hA x (Nat.le_add_right B t.val)⟩
  have hcard : Fintype.card {y : M // y ∈ A} < Fintype.card (Fin (A.card + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact Nat.lt_succ_self A.card
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with ⟨a, b, hne, hEq⟩
  have hOrbEq : D.orbit x (B + a.val) = D.orbit x (B + b.val) :=
    congrArg Subtype.val hEq
  have hValNe : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hValNe with hlt | hgt
  · exact ⟨a.val, b.val, hlt, Nat.le_of_lt_succ b.isLt, hOrbEq⟩
  · exact ⟨b.val, a.val, hgt, Nat.le_of_lt_succ a.isLt, hOrbEq.symm⟩

/-- **Theorem 2 (Feigenbaum Logarithmic-Depth Polynomial Scaling)**:
If problem size satisfies `n = 2 ^ k` (logarithmic renormalization depth `k = log₂ n`) and
complexity grows at most exponentially in depth with rate `δ ≤ 2 ^ c` (`C k ≤ δ ^ k * C₀`),
then total complexity satisfies the polynomial bound `C k ≤ n ^ c * C₀`. -/
theorem feigenbaum_log_depth_poly (C : ℕ → ℕ) (n k c δ C₀ : ℕ)
    (hn : n = 2 ^ k) (hδ : δ ≤ 2 ^ c) (hC : C k ≤ δ ^ k * C₀) :
    C k ≤ n ^ c * C₀ := by
  calc
    C k ≤ δ ^ k * C₀ := hC
    _ ≤ (2 ^ c) ^ k * C₀ := Nat.mul_le_mul_right C₀ (Nat.pow_le_pow_left hδ k)
    _ = (2 ^ k) ^ c * C₀ := by rw [← pow_mul, Nat.mul_comm c k, pow_mul]
    _ = n ^ c * C₀ := by rw [hn]

/-- Inductive helper for Theorem 2: if each RG step expands complexity by at most a factor `δ`,
then after `k` steps `C k ≤ δ ^ k * C 0`. -/
theorem rg_bounded_expansion_nat (C : ℕ → ℕ) (δ : ℕ)
    (hstep : ∀ t, C (t + 1) ≤ δ * C t) :
    ∀ k, C k ≤ δ ^ k * C 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      C (k + 1) ≤ δ * C k := hstep k
      _ ≤ δ * (δ ^ k * C 0) := Nat.mul_le_mul_left δ ih
      _ = δ ^ (k + 1) * C 0 := by rw [pow_succ', Nat.mul_assoc]

/-- Concrete `RGComplexity.RGSolver` instance for single-variable 2-SAT decimation. -/
def twoSATRGSolver {n : ℕ} (v : Fin n) : RGComplexity.RGSolver (TwoSATPoly.FCNF n) where
  Sat := TwoSATPoly.Satisfiable
  R := TwoSATPoly.decimateVar v
  preserves_sat := TwoSATPoly.decimateVar_equisatisfiable v

/-- **Concrete Phase I Witness (2-SAT Real-Space Renormalization Closure)**:
For any 2-SAT formula `φ` over `n` variables and any elimination sequence `vs`, the effective
renormalized formula remains closed inside the polynomial clause bound `(2 * n + 1) ^ 2` and
is equisatisfiable with `φ`. -/
theorem twoSAT_in_renormalizable_phase {n : ℕ} (vs : List (Fin n))
    {φ : TwoSATPoly.FCNF n} (h2 : TwoSATPoly.Is2SAT φ) :
    (TwoSATPoly.decimateList vs φ).card ≤ (2 * n + 1) ^ 2 ∧
      (TwoSATPoly.Satisfiable (TwoSATPoly.decimateList vs φ) ↔ TwoSATPoly.Satisfiable φ) :=
  ⟨TwoSATPoly.decimateList_card_le vs h2, TwoSATPoly.decimateList_equisatisfiable vs φ⟩

/-! ## 3. Phase II: Critical Phase Transition & OGP Stability Barrier -/

/-- A path of CNF instances lies in the **Critical OGP Phase (Phase II)** if it exhibits the
Coupled Overlap Gap Property `HasCoupledOGP path T ν₁ ν₂`. -/
def InCriticalOGPPhase {n : ℕ} (path : ℕ → CNF n) (T ν₁ ν₂ : ℕ) : Prop :=
  HasCoupledOGP path T ν₁ ν₂

/-- **Theorem 3 (Phase II Stable-Algorithm Barrier)**:
In the critical OGP phase, any `δ`-stable solver with `ν₁ + δ < ν₂` whose endpoint outputs
are separated by at least `ν₂` must fail to satisfy some intermediate instance `path t`. -/
theorem phase_two_stable_barrier {n : ℕ} (A : CNF n → Assignment n)
    (path : ℕ → CNF n) (T ν₁ ν₂ δ : ℕ)
    (hPhase : InCriticalOGPPhase path T ν₁ ν₂)
    (hgap : ν₁ + δ < ν₂)
    (hStab : IsStableSolver A path T δ)
    (hSep : ν₂ ≤ hammingDist (A (path 0)) (A (path T))) :
    ∃ t ≤ T, ¬ Satisfies (path t) (A (path t)) :=
  ogp_stable_solver_failure_witness A path T ν₁ ν₂ δ hPhase hgap hStab hSep

/-- **Concrete Phase II Witness (Ferromagnetic Ising Chain)**:
Any interpolation path containing `isingChainCNF n` (`0 < n`) at every step lies in
`InCriticalOGPPhase path T 0 n`. -/
theorem isingChain_in_critical_phase {n : ℕ} (hn : 0 < n)
    (path : ℕ → CNF n) (T : ℕ)
    (hSub : ∀ t ≤ T, ∀ c ∈ isingChainCNF n, c ∈ path t) :
    InCriticalOGPPhase path T 0 n :=
  isingChainCNF_hasCoupledOGP hn path T hSub

/-- **Explicit Phase II Failure Witness for the Ferromagnetic Ising Chain**:
For `n ≥ 2` and `δ < n`, any `δ`-stable solver along a coupled Ising-chain path whose
endpoints select the all-`false` and all-`true` ground states fails on some intermediate
instance `path t` (`t ≤ T`). -/
theorem isingChain_phase_two_failure_witness {n : ℕ} (hn : 2 ≤ n)
    (A : CNF n → Assignment n) (path : ℕ → CNF n) (T δ : ℕ)
    (hδ : δ < n)
    (hSub : ∀ t ≤ T, ∀ c ∈ isingChainCNF n, c ∈ path t)
    (hStab : IsStableSolver A path T δ)
    (h0 : A (path 0) = (fun _ => false))
    (hT : A (path T) = (fun _ => true)) :
    ∃ t ≤ T, ¬ Satisfies (path t) (A (path t)) := by
  have hPos : 0 < n := by omega
  have hPhase : InCriticalOGPPhase path T 0 n :=
    isingChain_in_critical_phase hPos path T hSub
  have hgap : 0 + δ < n := by omega
  have hSep : n ≤ hammingDist (A (path 0)) (A (path T)) := by
    rw [h0, hT, hammingDist_const_false_true]
  exact phase_two_stable_barrier A path T 0 n δ hPhase hgap hStab hSep

/-! ## 4. Phase III: Chaotic / Non-Renormalizable Resolution Phase -/

/-- A CNF formula `φ` lies in the **Chaotic Resolution Phase (Phase III)** with initial width
bound `w₀` and width divergence `d` if every initial clause has width at most `w₀` while
every tree-like resolution refutation of `φ` requires width strictly greater than `w₀ + d`. -/
def InChaoticResolutionPhase {n : ℕ} (φ : BSWTradeoff.CNF n) (w₀ d : ℕ) : Prop :=
  (∀ c ∈ φ, c.card ≤ w₀) ∧ (∀ T : BSWTradeoff.ResTree φ ∅, w₀ + d < T.width)

/-- **Theorem 4 (Phase III Exponential Tree-Like Resolution Barrier)**:
Every tree-like resolution refutation of a formula in `InChaoticResolutionPhase φ w₀ d` has
exponential size strictly exceeding `2 ^ d`. -/
theorem phase_three_exponential_barrier {n : ℕ} {φ : BSWTradeoff.CNF n} {w₀ d : ℕ}
    (hPhase : InChaoticResolutionPhase φ w₀ d)
    (T : BSWTradeoff.ResTree φ ∅) :
    2 ^ d < T.size :=
  BSWTradeoff.bsw_tree_size_lower_bound d w₀ φ hPhase.1 hPhase.2 T

/-! ## 5. Unified Three-Phase Correspondence Summary -/

/-- Structured summary unifying the three dynamical–complexity correspondence phases:
- **Phase I**: Feigenbaum logarithmic-depth polynomial scaling and 2-SAT RG closure.
- **Phase II**: Ferromagnetic Ising-chain OGP stability barrier for stable solvers.
- **Phase III**: Ben-Sasson–Wigderson exponential lower bound from resolution width divergence. -/
structure ThreePhaseSummary : Prop where
  /-- Phase I (scaling law): logarithmic RG depth with bounded expansion yields polynomial cost. -/
  phaseI_feigenbaum :
    ∀ (C : ℕ → ℕ) (n k c δ C₀ : ℕ),
      n = 2 ^ k → δ ≤ 2 ^ c → C k ≤ δ ^ k * C₀ → C k ≤ n ^ c * C₀
  /-- Phase I (2-SAT witness): 2-SAT decimation stays within `(2 * n + 1) ^ 2` clauses. -/
  phaseI_twoSAT :
    ∀ (n : ℕ) (vs : List (Fin n)) (φ : TwoSATPoly.FCNF n),
      TwoSATPoly.Is2SAT φ →
        (TwoSATPoly.decimateList vs φ).card ≤ (2 * n + 1) ^ 2 ∧
          (TwoSATPoly.Satisfiable (TwoSATPoly.decimateList vs φ) ↔ TwoSATPoly.Satisfiable φ)
  /-- Phase II (Ising OGP witness): stable solvers fail across the ferromagnetic overlap gap. -/
  phaseII_ising_ogp :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ (A : CNF n → Assignment n) (path : ℕ → CNF n) (T δ : ℕ),
        δ < n →
        (∀ t ≤ T, ∀ c ∈ isingChainCNF n, c ∈ path t) →
        IsStableSolver A path T δ →
        A (path 0) = (fun _ => false) →
        A (path T) = (fun _ => true) →
        ∃ t ≤ T, ¬ Satisfies (path t) (A (path t))
  /-- Phase III (BSW chaos witness): width divergence forces exponential refutation size. -/
  phaseIII_chaotic_bsw :
    ∀ (n : ℕ) (φ : BSWTradeoff.CNF n) (w₀ d : ℕ),
      InChaoticResolutionPhase φ w₀ d →
        ∀ T : BSWTradeoff.ResTree φ ∅, 2 ^ d < T.size

/-- **Unified Three-Phase Correspondence Theorem**:
All three dynamical–complexity regimes (Phase I polynomial RG closure, Phase II OGP stability
barrier, and Phase III exponential resolution barrier) hold unconditionally. -/
theorem three_phase_correspondence : ThreePhaseSummary where
  phaseI_feigenbaum := fun C n k c δ C₀ hn hδ hC =>
    feigenbaum_log_depth_poly C n k c δ C₀ hn hδ hC
  phaseI_twoSAT := fun _ vs _ h2 =>
    twoSAT_in_renormalizable_phase vs h2
  phaseII_ising_ogp := fun _ hn A path T δ hδ hSub hStab h0 hT =>
    isingChain_phase_two_failure_witness hn A path T δ hδ hSub hStab h0 hT
  phaseIII_chaotic_bsw := fun _ _ _ _ hPhase T =>
    phase_three_exponential_barrier hPhase T

end Mathmatica.DynamicalComplexity
