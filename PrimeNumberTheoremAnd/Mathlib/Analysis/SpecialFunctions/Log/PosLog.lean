/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Positive-log estimates

Small estimates for `Real.log⁺` and for converting logarithmic growth bounds into exponential
bounds.
-/

@[expose] public section

namespace Real

/-- If `y ≤ exp x` and `0 ≤ x`, then `log (1 + y) ≤ x + log 2`. -/
theorem log_one_add_le_add_log_two_of_le_exp {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hxy : y ≤ exp x) :
    log (1 + y) ≤ x + log 2 := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hle : (1 : ℝ) + y ≤ 1 + exp x := by linarith
  have he : 1 ≤ |exp x| := by
    rw [abs_of_pos (exp_pos x)]
    exact one_le_exp_iff.mpr hx
  exact (log_le_log hpos hle).trans (by
    simpa only [posLog_eq_log he, log_exp] using (log_one_add_le_posLog (x := exp x)))

/-- A bound on `log (1 + y)` gives the corresponding exponential bound for `y`. -/
theorem le_exp_of_log_one_add_le {x y : ℝ} (hy : 0 ≤ y) (hxy : log (1 + y) ≤ x) :
    y ≤ exp x := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hone : 1 + y ≤ exp x := (log_le_iff_le_exp hpos).1 hxy
  linarith

/-- Lower bound for `log x` in terms of `log⁺ x⁻¹`. -/
theorem neg_posLog_inv_le_log (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
  linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]

end Real
