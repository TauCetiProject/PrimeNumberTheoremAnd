/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
## Special values of the completed Riemann zeta function

This file proves numerical nonvanishing of the entire completed zeta function at `0` and `1`,
using explicit Euler-Mascheroni and logarithmic bounds and the functional equation.
The Euler-Mascheroni formula for `Λ₀(1)` is in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## References

* [titchmarsh1986] and [edwards1974] for completed-zeta special values and the functional equation
-/

@[expose] public section

open Complex Set

open scoped BigOperators

/-- The entire completed zeta function `Λ₀` is nonzero at `1`.

This uses the Euler-Mascheroni formula for `Λ₀(1)` from `ZetaAsymp`, the lower bound
`27 / 50 < γ`, and an elementary numerical bound `log (4π) < 127 / 50`. -/
theorem completedRiemannZeta₀_one_ne_zero :
    completedRiemannZeta₀ (1 : ℂ) ≠ 0 := by
  have hpos :
      0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
    have hγ : (27 / 50 : ℝ) < Real.eulerMascheroniConstant := by
      refine lt_trans ?_ (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20)
      have hval : Real.eulerMascheroniSeq 20 =
          (55835135 / 15519504 : ℝ) - Real.log 21 := by
        norm_num [Real.eulerMascheroniSeq]
      rw [hval, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt',
        Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 21)]
      refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have hlog : Real.log (4 * Real.pi) < 127 / 50 := by
      rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 4 * Real.pi)]
      have hpi : 4 * Real.pi < 7854 / 625 := by
        nlinarith [Real.pi_lt_d4]
      refine hpi.trans (lt_of_lt_of_le ?_
        (Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (127 / 50 : ℝ)) 12))
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  have hreal :
      ((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  rw [completedRiemannZeta₀_one]
  simpa [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi), sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hreal

/-- The entire completed zeta function `Λ₀` is nonzero at `0`, by the functional equation and the
nonvanishing at `1`. -/
theorem completedRiemannZeta₀_zero_ne_zero :
    completedRiemannZeta₀ (0 : ℂ) ≠ 0 := by
  simpa [← completedRiemannZeta₀_one_sub (0 : ℂ)] using completedRiemannZeta₀_one_ne_zero
