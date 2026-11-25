import Mathmatica.OverlapGap

/-!
# OGP Stability Barrier: From Dynamical Continuity to Search Impossibility

This module bridges **Overlap Gap Property (OGP)** geometry (from `Mathmatica.OverlapGap`)
to **algorithmic impossibility of finding a satisfying state** for stable solvers (following
Gamarnik's OGP framework):

1. **Discrete Intermediate Value Theorem on `ℕ`** (`discrete_ivt_nat`):
   Any sequence `f : ℕ → ℕ` with upward step bound `f (t + 1) ≤ f t + δ` starting at `f 0 ≤ ν₁`
   and ending at `f T ≥ ν₂` (with `ν₁ + δ < ν₂`) must land strictly inside the gap `(ν₁, ν₂)`.
2. **Discrete IVT in Hamming Space** (`discrete_ivt_hamming`):
   A `δ`-stable trajectory in `Assignment n` cannot jump across a forbidden Hamming gap
   `(ν₁, ν₂)` of width `ν₂ - ν₁ > δ` without landing inside it.
3. **OGP Stability Barrier Theorem** (`ogp_rules_out_stable_solver`,
   `ogp_stable_solver_failure_witness`):
   Along any interpolation path satisfying Coupled OGP (`HasCoupledOGP`), if a `δ`-stable solver
   `A` has `ν₁ + δ < ν₂` and its endpoints are separated by at least `ν₂`, then `A` must fail
   to find a valid satisfying state on at least one instance `path t` (`t ≤ T`).
-/

namespace Mathmatica.OGPBarrier

open Mathmatica.SAT
open Mathmatica.OverlapGap

/-! ## 1. Discrete Intermediate Value Theorem -/

/-- **Discrete Intermediate Value Theorem on `ℕ`**:
If `f : ℕ → ℕ` has bounded upward steps `f (t + 1) ≤ f t + δ`, starts at `f 0 ≤ ν₁`,
and reaches `ν₂ ≤ f T` with `ν₁ + δ < ν₂`, then there exists `t ≤ T` strictly inside `(ν₁, ν₂)`. -/
theorem discrete_ivt_nat (f : ℕ → ℕ) (T ν₁ ν₂ δ : ℕ)
    (hgap : ν₁ + δ < ν₂)
    (hstep : ∀ t < T, f (t + 1) ≤ f t + δ)
    (h0 : f 0 ≤ ν₁) (hT : ν₂ ≤ f T) :
    ∃ t ≤ T, ν₁ < f t ∧ f t < ν₂ := by
  induction T with
  | zero => omega
  | succ k ih =>
    by_cases hk : ν₂ ≤ f k
    · rcases ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht)) hk with ⟨t, ht, hgt, hlt⟩
      exact ⟨t, Nat.le_succ_of_le ht, hgt, hlt⟩
    · have hk_lt : f k < ν₂ := Nat.lt_of_not_ge hk
      by_cases hk_gt : ν₁ < f k
      · exact ⟨k, Nat.le_succ k, hk_gt, hk_lt⟩
      · have hk_le : f k ≤ ν₁ := Nat.le_of_not_lt hk_gt
        have hlast : f (k + 1) ≤ f k + δ := hstep k (Nat.lt_succ_self k)
        omega

/-- **Discrete IVT in Hamming Space**:
Along any trajectory `traj : ℕ → Assignment n` with step bound
`hammingDist (traj t) (traj (t + 1)) ≤ δ`, if `ν₁ + δ < ν₂` and the endpoint satisfies
`ν₂ ≤ hammingDist (traj 0) (traj T)`, then some intermediate state `traj t` lies strictly
inside the Hamming gap `(ν₁, ν₂)` relative to `traj 0`. -/
theorem discrete_ivt_hamming {n : ℕ} (traj : ℕ → Assignment n) (T ν₁ ν₂ δ : ℕ)
    (hgap : ν₁ + δ < ν₂)
    (hstep : ∀ t < T, hammingDist (traj t) (traj (t + 1)) ≤ δ)
    (hT : ν₂ ≤ hammingDist (traj 0) (traj T)) :
    ∃ t ≤ T,
      ν₁ < hammingDist (traj 0) (traj t) ∧ hammingDist (traj 0) (traj t) < ν₂ := by
  let f : ℕ → ℕ := fun t => hammingDist (traj 0) (traj t)
  have hf0 : f 0 ≤ ν₁ := by
    change hammingDist (traj 0) (traj 0) ≤ ν₁
    rw [hammingDist_self]
    exact Nat.zero_le ν₁
  have hfstep : ∀ t < T, f (t + 1) ≤ f t + δ := by
    intro t ht
    have htri := hammingDist_triangle (traj 0) (traj t) (traj (t + 1))
    have hs := hstep t ht
    change hammingDist (traj 0) (traj (t + 1)) ≤ hammingDist (traj 0) (traj t) + δ
    omega
  exact discrete_ivt_nat f T ν₁ ν₂ δ hgap hfstep hf0 hT

/-! ## 2. Coupled OGP and Stable Solvers -/

/-- **Coupled Overlap Gap Property (`HasCoupledOGP`)**:
Along an interpolation path `path : ℕ → CNF n` of length `T`, every pair consisting of a
solution `σ` to `path 0` and a solution `τ` to `path t` (`t ≤ T`) avoids the forbidden
Hamming distance interval `(ν₁, ν₂)`. -/
def HasCoupledOGP {n : ℕ} (path : ℕ → CNF n) (T ν₁ ν₂ : ℕ) : Prop :=
  ν₁ < ν₂ ∧
  ∀ t ≤ T, ∀ σ τ : Assignment n,
    Satisfies (path 0) σ → Satisfies (path t) τ →
      hammingDist σ τ ≤ ν₁ ∨ ν₂ ≤ hammingDist σ τ

/-- **Algorithmic Stability (`IsStableSolver`)**:
A solver `A : CNF n → Assignment n` is `δ`-stable along `path` if adjacent instances
`path t` and `path (t + 1)` produce outputs within Hamming distance `δ`. -/
def IsStableSolver {n : ℕ} (A : CNF n → Assignment n)
    (path : ℕ → CNF n) (T δ : ℕ) : Prop :=
  ∀ t < T, hammingDist (A (path t)) (A (path (t + 1))) ≤ δ

/-! ## 3. OGP Stability Barrier Theorem -/

/-- **Main Theorem (OGP Rules Out Stable State-Finding Solvers)**:
Suppose an interpolation path satisfies `HasCoupledOGP path T ν₁ ν₂`, a solver `A` is
`δ`-stable along `path` with `ν₁ + δ < ν₂`, and the outputs at the endpoints `0` and `T`
are separated by at least `ν₂`. Then `A` cannot find a valid satisfying state for every
instance along the path. -/
theorem ogp_rules_out_stable_solver {n : ℕ} (A : CNF n → Assignment n)
    (path : ℕ → CNF n) (T ν₁ ν₂ δ : ℕ)
    (hOGP : HasCoupledOGP path T ν₁ ν₂)
    (hgap : ν₁ + δ < ν₂)
    (hStab : IsStableSolver A path T δ)
    (hSep : ν₂ ≤ hammingDist (A (path 0)) (A (path T))) :
    ¬ (∀ t ≤ T, Satisfies (path t) (A (path t))) := by
  intro hAll
  let traj : ℕ → Assignment n := fun t => A (path t)
  rcases discrete_ivt_hamming traj T ν₁ ν₂ δ hgap hStab hSep with ⟨t, ht, hgt, hlt⟩
  have hSat0 : Satisfies (path 0) (traj 0) := hAll 0 (Nat.zero_le T)
  have hSatt : Satisfies (path t) (traj t) := hAll t ht
  rcases hOGP.2 t ht (traj 0) (traj t) hSat0 hSatt with hle | hge
  · omega
  · omega

/-- **Corollary (Explicit Failure Witness)**:
Under the hypotheses of `ogp_rules_out_stable_solver`, there exists an index `t ≤ T`
such that `A (path t)` fails to satisfy `path t`. -/
theorem ogp_stable_solver_failure_witness {n : ℕ} (A : CNF n → Assignment n)
    (path : ℕ → CNF n) (T ν₁ ν₂ δ : ℕ)
    (hOGP : HasCoupledOGP path T ν₁ ν₂)
    (hgap : ν₁ + δ < ν₂)
    (hStab : IsStableSolver A path T δ)
    (hSep : ν₂ ≤ hammingDist (A (path 0)) (A (path T))) :
    ∃ t ≤ T, ¬ Satisfies (path t) (A (path t)) := by
  by_contra hNo
  apply ogp_rules_out_stable_solver A path T ν₁ ν₂ δ hOGP hgap hStab hSep
  intro t ht
  by_contra hUnsat
  exact hNo ⟨t, ht, hUnsat⟩

end Mathmatica.OGPBarrier
