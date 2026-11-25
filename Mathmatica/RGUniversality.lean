/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Renormalization Group Universality on the Stable Manifold

This file formalizes renormalization group (RG) universality on the stable manifold of a critical
fixed point via the Banach contraction mapping theorem (`ContractingWith` in Mathlib).

## Main definitions

* `Mathmatica.RGUniversality.ContractingRGFlow`: a renormalization group operator `R : S → S`
  acting as a contraction with constant `K < 1` on a nonempty complete metric space `S` modeling
  the stable manifold of critical systems.
* `Mathmatica.RGUniversality.ContractingRGFlow.universalFixedPoint`: the unique universal RG fixed
  point on `S`, obtained directly from `ContractingWith.fixedPoint`.

## Main results

* `Mathmatica.RGUniversality.ContractingRGFlow.universalFixedPoint_isFixedPt` and
  `Mathmatica.RGUniversality.ContractingRGFlow.eq_universalFixedPoint_of_isFixedPt`: existence and
  uniqueness of the universal fixed point.
* `Mathmatica.RGUniversality.rg_erases_microscopic_details`: for any two microscopic models
  `f₁, f₂ : S`, the distance between their RG iterates decays geometrically at rate `K ^ k` and
  converges to `0`.
* `Mathmatica.RGUniversality.rg_observable_universality`: for any macroscopic observable
  `Obs : S → ℝ` continuous at the universal fixed point `g` (such as a functional determining a
  Feigenbaum scaling constant), the RG flow starting from any microscopic model `f : S` converges
  to the same universal constant `Obs g`.

## References

* M. J. Feigenbaum, *Quantitative universality for a class of nonlinear transformations*,
  J. Stat. Phys. 19 (1978), 25–52.
* K. G. Wilson, *Renormalization group and critical phenomena*, Phys. Rev. B 4 (1971), 3174–3205.
-/

open Filter Function
open scoped Topology

namespace Mathmatica.RGUniversality

/-- A renormalization group flow restricted to a stable manifold `S` (modeled as a nonempty
complete metric space), given by a contracting RG operator `R : S → S` with contraction constant
`K < 1`. -/
structure ContractingRGFlow (S : Type*) [MetricSpace S] [CompleteSpace S] [Nonempty S] where
  /-- The renormalization group operator acting on the stable manifold. -/
  R : S → S
  /-- The contraction constant strictly less than `1`. -/
  K : NNReal
  /-- Proof that `R` is a contraction with constant `K`. -/
  hK : ContractingWith K R

namespace ContractingRGFlow

variable {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
variable (flow : ContractingRGFlow S)

/-- The unique universal fixed point of a contracting renormalization group flow on `S`. -/
noncomputable def universalFixedPoint : S :=
  flow.hK.fixedPoint flow.R

/-- The universal fixed point is invariant under the renormalization group operator `R`. -/
theorem universalFixedPoint_isFixedPt : IsFixedPt flow.R flow.universalFixedPoint :=
  flow.hK.fixedPoint_isFixedPt

/-- Any fixed point of the renormalization group operator `R` on `S` coincides with
`universalFixedPoint`. -/
theorem eq_universalFixedPoint_of_isFixedPt {g : S} (hg : IsFixedPt flow.R g) :
    g = flow.universalFixedPoint :=
  flow.hK.fixedPoint_unique hg

/-- Every RG trajectory on the stable manifold converges to the universal fixed point. -/
theorem tendsto_iterate_universalFixedPoint (f : S) :
    Tendsto (fun k => flow.R^[k] f) atTop (𝓝 flow.universalFixedPoint) :=
  flow.hK.tendsto_iterate_fixedPoint f

/-- A priori geometric error bound for convergence of RG iterates to the universal fixed point. -/
theorem apriori_dist_iterate_universalFixedPoint_le (f : S) (k : ℕ) :
    dist (flow.R^[k] f) flow.universalFixedPoint ≤
      dist f (flow.R f) * (flow.K : ℝ) ^ k / (1 - (flow.K : ℝ)) :=
  flow.hK.apriori_dist_iterate_fixedPoint_le f k

/-- Under `k` iterations of a contracting RG operator, the distance between any two microscopic
models contracts by at least `(K : ℝ) ^ k`. -/
theorem dist_iterate_le (f₁ f₂ : S) (k : ℕ) :
    dist (flow.R^[k] f₁) (flow.R^[k] f₂) ≤ (flow.K : ℝ) ^ k * dist f₁ f₂ := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', pow_succ', mul_assoc]
    calc
      dist (flow.R (flow.R^[k] f₁)) (flow.R (flow.R^[k] f₂))
          ≤ (flow.K : ℝ) * dist (flow.R^[k] f₁) (flow.R^[k] f₂) :=
        flow.hK.dist_le_mul (flow.R^[k] f₁) (flow.R^[k] f₂)
      _ ≤ (flow.K : ℝ) * ((flow.K : ℝ) ^ k * dist f₁ f₂) :=
        mul_le_mul_of_nonneg_left ih flow.K.coe_nonneg

end ContractingRGFlow

section Universality

variable {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]

/-- **RG Erases Microscopic Details (Geometric Convergence Theorem).**
For any two microscopic initial models `f₁, f₂ : S` on the stable manifold, the distance between
their RG iterates decays geometrically at rate `K ^ k` and converges to `0`. -/
theorem rg_erases_microscopic_details (flow : ContractingRGFlow S) (f₁ f₂ : S) :
    (∀ k : ℕ, dist (flow.R^[k] f₁) (flow.R^[k] f₂) ≤ (flow.K : ℝ) ^ k * dist f₁ f₂) ∧
      Tendsto (fun k => dist (flow.R^[k] f₁) (flow.R^[k] f₂)) atTop (𝓝 0) := by
  refine ⟨fun k => flow.dist_iterate_le f₁ f₂ k, ?_⟩
  have hK_lt_one : (flow.K : ℝ) < 1 := NNReal.coe_lt_one.mpr flow.hK.1
  have h_geom : Tendsto (fun k => (flow.K : ℝ) ^ k * dist f₁ f₂) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one flow.K.coe_nonneg hK_lt_one).mul_const (dist f₁ f₂)
  exact squeeze_zero (fun k => dist_nonneg) (fun k => flow.dist_iterate_le f₁ f₂ k) h_geom

/-- **RG Observable Universality Theorem.**
For any macroscopic observable `Obs : S → ℝ` continuous at the universal fixed point `g`, the RG
flow starting from any microscopic initial model `f : S` converges to the same universal constant
`Obs g`. -/
theorem rg_observable_universality (flow : ContractingRGFlow S) (Obs : S → ℝ)
    (hObs : ContinuousAt Obs flow.universalFixedPoint) (f : S) :
    Tendsto (fun k => Obs (flow.R^[k] f)) atTop (𝓝 (Obs flow.universalFixedPoint)) :=
  hObs.tendsto.comp (flow.tendsto_iterate_universalFixedPoint f)

/-- Any two microscopic initial models `f₁, f₂ : S` share the same universal RG limit for every
macroscopic observable continuous at the universal fixed point, so their observable discrepancy
vanishes in the RG limit. -/
theorem rg_observable_diff_tendsto_zero (flow : ContractingRGFlow S) (Obs : S → ℝ)
    (hObs : ContinuousAt Obs flow.universalFixedPoint) (f₁ f₂ : S) :
    Tendsto (fun k => Obs (flow.R^[k] f₁) - Obs (flow.R^[k] f₂)) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (rg_observable_universality flow Obs hObs f₁).sub
      (rg_observable_universality flow Obs hObs f₂)

end Universality

end Mathmatica.RGUniversality
