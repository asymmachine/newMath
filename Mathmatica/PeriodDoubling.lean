/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First Period-Doubling Bifurcation of the Logistic Map

This file formalizes the first period-doubling bifurcation (discrete time-translation symmetry
breaking) of the logistic map `f_μ(x) = μ * x * (1 - x)` at the critical parameter `μ = 3`, using
Mathlib's `Function.IsFixedPt`, `Function.IsPeriodicPt`, and `Function.minimalPeriod`.

## Main definitions

* `Mathmatica.PeriodDoubling.logistic`: the logistic map `x ↦ μ * x * (1 - x)`.
* `Mathmatica.PeriodDoubling.fixedPt`: the nontrivial fixed point `1 - 1 / μ` for `μ ≠ 0`.
* `Mathmatica.PeriodDoubling.periodTwoPos`, `Mathmatica.PeriodDoubling.periodTwoNeg`:
  the two explicit points of the period-2 orbit born for `μ > 3`.

## Main results

* `Mathmatica.PeriodDoubling.logistic_fixedPt`: `fixedPt μ` is a fixed point of `logistic μ`
  whenever `μ ≠ 0`.
* `Mathmatica.PeriodDoubling.deriv_logistic_fixedPt`: the multiplier at the nontrivial fixed point
  is `deriv (logistic μ) (fixedPt μ) = 2 - μ`.
* `Mathmatica.PeriodDoubling.abs_deriv_logistic_fixedPt_lt_one` and
  `Mathmatica.PeriodDoubling.one_lt_abs_deriv_logistic_fixedPt`: linear stability for `1 < μ < 3`
  and loss of stability for `3 < μ` (with critical flip multiplier `-1` at `μ = 3`).
* `Mathmatica.PeriodDoubling.minimalPeriod_periodTwoPos`: for `3 < μ`, `periodTwoPos μ` has
  exact minimal period `2` under `logistic μ`, witnessing discrete time-translation symmetry
  breaking.
-/

namespace Mathmatica.PeriodDoubling

/-! ### Logistic map and nontrivial fixed point -/

/-- The logistic map `f_μ(x) = μ * x * (1 - x)`. -/
def logistic (μ x : ℝ) : ℝ :=
  μ * x * (1 - x)

/-- The nontrivial fixed point `x*(μ) = 1 - 1 / μ` of the logistic map. -/
noncomputable def fixedPt (μ : ℝ) : ℝ :=
  1 - 1 / μ

/-- For `μ ≠ 0`, `fixedPt μ` is a fixed point of `logistic μ`. -/
theorem logistic_fixedPt {μ : ℝ} (hμ : μ ≠ 0) :
    Function.IsFixedPt (logistic μ) (fixedPt μ) := by
  simp only [Function.IsFixedPt, logistic, fixedPt]
  field_simp
  ring

/-! ### Derivative and linear stability transition at `μ = 3` -/

/-- The logistic map is differentiable everywhere with derivative `μ * (1 - 2 * x)`. -/
theorem hasDerivAt_logistic (μ x : ℝ) :
    HasDerivAt (logistic μ) (μ * (1 - 2 * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => μ * y) (μ * 1) x :=
    (hasDerivAt_id x).const_mul μ
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  change HasDerivAt (fun y : ℝ => μ * y * (1 - y)) (μ * (1 - 2 * x)) x
  convert h1.mul h2 using 1
  ring

/-- The derivative of `logistic μ` at `x` is `μ * (1 - 2 * x)`. -/
theorem deriv_logistic (μ x : ℝ) :
    deriv (logistic μ) x = μ * (1 - 2 * x) :=
  (hasDerivAt_logistic μ x).deriv

/-- The multiplier at the nontrivial fixed point `fixedPt μ` is `2 - μ` for `μ ≠ 0`. -/
theorem deriv_logistic_fixedPt {μ : ℝ} (hμ : μ ≠ 0) :
    deriv (logistic μ) (fixedPt μ) = 2 - μ := by
  rw [deriv_logistic, fixedPt]
  field_simp
  ring

/-- At the bifurcation threshold `μ = 3`, the fixed-point multiplier equals `-1`. -/
theorem deriv_logistic_fixedPt_three :
    deriv (logistic 3) (fixedPt 3) = -1 := by
  rw [deriv_logistic_fixedPt (by norm_num)]
  norm_num

/-- For `1 < μ < 3`, the nontrivial fixed point is linearly stable (`|f_μ'(x*)| < 1`). -/
theorem abs_deriv_logistic_fixedPt_lt_one {μ : ℝ} (h1 : 1 < μ) (h3 : μ < 3) :
    |deriv (logistic μ) (fixedPt μ)| < 1 := by
  have hμ : μ ≠ 0 := by linarith
  rw [deriv_logistic_fixedPt hμ, abs_lt]
  constructor <;> linarith

/-- For `3 < μ`, the nontrivial fixed point loses linear stability (`1 < |f_μ'(x*)|`). -/
theorem one_lt_abs_deriv_logistic_fixedPt {μ : ℝ} (h3 : 3 < μ) :
    1 < |deriv (logistic μ) (fixedPt μ)| := by
  have hμ : μ ≠ 0 := by linarith
  rw [deriv_logistic_fixedPt hμ, lt_abs]
  right
  linarith

/-! ### Birth of the period-2 orbit for `μ > 3` -/

/-- The upper point of the period-2 orbit of `logistic μ` for `μ > 3`. -/
noncomputable def periodTwoPos (μ : ℝ) : ℝ :=
  ((μ + 1) + Real.sqrt ((μ - 3) * (μ + 1))) / (2 * μ)

/-- The lower point of the period-2 orbit of `logistic μ` for `μ > 3`. -/
noncomputable def periodTwoNeg (μ : ℝ) : ℝ :=
  ((μ + 1) - Real.sqrt ((μ - 3) * (μ + 1))) / (2 * μ)

/-- For `3 < μ`, the lower period-2 point is strictly smaller than the upper period-2 point. -/
theorem periodTwoNeg_lt_pos {μ : ℝ} (hμ : 3 < μ) :
    periodTwoNeg μ < periodTwoPos μ := by
  unfold periodTwoNeg periodTwoPos
  have hdisc : 0 < (μ - 3) * (μ + 1) := by nlinarith
  have hsqrt : 0 < Real.sqrt ((μ - 3) * (μ + 1)) := Real.sqrt_pos.mpr hdisc
  have hden : 0 < 2 * μ := by linarith
  exact div_lt_div_of_pos_right (by linarith) hden

/-- For `3 < μ`, the two points of the period-2 orbit are distinct. -/
theorem periodTwoPos_ne_neg {μ : ℝ} (hμ : 3 < μ) :
    periodTwoPos μ ≠ periodTwoNeg μ :=
  ne_of_gt (periodTwoNeg_lt_pos hμ)

/-- For `3 < μ`, the logistic map sends `periodTwoPos μ` to `periodTwoNeg μ`. -/
theorem logistic_periodTwoPos {μ : ℝ} (hμ : 3 < μ) :
    logistic μ (periodTwoPos μ) = periodTwoNeg μ := by
  unfold logistic periodTwoPos periodTwoNeg
  set s := Real.sqrt ((μ - 3) * (μ + 1))
  have hμ0 : μ ≠ 0 := by linarith
  have hsq : s ^ 2 = (μ - 3) * (μ + 1) := Real.sq_sqrt (by nlinarith)
  field_simp [hμ0]
  linear_combination -hsq

/-- For `3 < μ`, the logistic map sends `periodTwoNeg μ` to `periodTwoPos μ`. -/
theorem logistic_periodTwoNeg {μ : ℝ} (hμ : 3 < μ) :
    logistic μ (periodTwoNeg μ) = periodTwoPos μ := by
  unfold logistic periodTwoPos periodTwoNeg
  set s := Real.sqrt ((μ - 3) * (μ + 1))
  have hμ0 : μ ≠ 0 := by linarith
  have hsq : s ^ 2 = (μ - 3) * (μ + 1) := Real.sq_sqrt (by nlinarith)
  field_simp [hμ0]
  linear_combination -hsq

/-- For `3 < μ`, `periodTwoPos μ` is a periodic point of period `2` for `logistic μ`. -/
theorem isPeriodicPt_periodTwoPos {μ : ℝ} (hμ : 3 < μ) :
    Function.IsPeriodicPt (logistic μ) 2 (periodTwoPos μ) := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ,
    Function.iterate_zero, Function.comp_apply, id_eq]
  rw [logistic_periodTwoPos hμ, logistic_periodTwoNeg hμ]

/-- For `3 < μ`, `periodTwoNeg μ` is a periodic point of period `2` for `logistic μ`. -/
theorem isPeriodicPt_periodTwoNeg {μ : ℝ} (hμ : 3 < μ) :
    Function.IsPeriodicPt (logistic μ) 2 (periodTwoNeg μ) := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ,
    Function.iterate_zero, Function.comp_apply, id_eq]
  rw [logistic_periodTwoNeg hμ, logistic_periodTwoPos hμ]

/-- For `3 < μ`, `periodTwoPos μ` is not a fixed point of `logistic μ`. -/
theorem not_isFixedPt_periodTwoPos {μ : ℝ} (hμ : 3 < μ) :
    ¬ Function.IsFixedPt (logistic μ) (periodTwoPos μ) := by
  intro hfix
  have heq : periodTwoPos μ = periodTwoNeg μ := by
    rw [← hfix.eq, logistic_periodTwoPos hμ]
  exact periodTwoPos_ne_neg hμ heq

/-- For `3 < μ`, `periodTwoNeg μ` is not a fixed point of `logistic μ`. -/
theorem not_isFixedPt_periodTwoNeg {μ : ℝ} (hμ : 3 < μ) :
    ¬ Function.IsFixedPt (logistic μ) (periodTwoNeg μ) := by
  intro hfix
  have heq : periodTwoPos μ = periodTwoNeg μ := by
    rw [← logistic_periodTwoNeg hμ, hfix.eq]
  exact periodTwoPos_ne_neg hμ heq

/-- Main theorem (discrete time-translation symmetry breaking): for `3 < μ`, the minimal period
of `periodTwoPos μ` under the logistic map `logistic μ` is strictly `2`. -/
theorem minimalPeriod_periodTwoPos {μ : ℝ} (hμ : 3 < μ) :
    Function.minimalPeriod (logistic μ) (periodTwoPos μ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Function.minimalPeriod_eq_prime (isPeriodicPt_periodTwoPos hμ)
    (not_isFixedPt_periodTwoPos hμ)

/-- Companion symmetry-breaking theorem: for `3 < μ`, the minimal period of `periodTwoNeg μ`
under `logistic μ` is strictly `2`. -/
theorem minimalPeriod_periodTwoNeg {μ : ℝ} (hμ : 3 < μ) :
    Function.minimalPeriod (logistic μ) (periodTwoNeg μ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Function.minimalPeriod_eq_prime (isPeriodicPt_periodTwoNeg hμ)
    (not_isFixedPt_periodTwoNeg hμ)

end Mathmatica.PeriodDoubling
