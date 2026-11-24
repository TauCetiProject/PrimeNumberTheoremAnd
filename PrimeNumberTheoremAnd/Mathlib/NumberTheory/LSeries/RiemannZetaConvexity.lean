/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Topology.MetricSpace.Basic
import TauCeti.NumberTheory.LSeries.Moebius

/-!
# Bounds for the Riemann zeta function

Vertical-line bounds for `riemannZeta`. Euler-product input is in
`PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta`.

## Main results

* `norm_riemannZeta_ratio_le_on_verticalLine`, `norm_riemannZeta_ratio_le_on_vertical_line` :
  convexity input on vertical lines
-/

@[expose] public section

open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex

/-!
### Vertical-line ratio bound
-/

/-- For `σ > 1`, the Euler product at `re s = 2σ` controls `‖ζ(2σ) / ζ σ‖` on the line `σ + it`. -/
theorem norm_riemannZeta_ratio_le_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖ ≤ ‖riemannZeta (verticalLine σ t)‖ := by
  have hs : 1 < (verticalLine σ t).re := by rw [verticalLine_re]; exact hσ
  have hs' : 1 < (σ : ℂ).re := by simpa using hσ
  have h := TauCeti.riemannZeta_eq_mul_LSeries_moebius_sq hs'
  have hL := right_ne_zero_of_mul (h ▸ riemannZeta_ne_zero_of_one_lt_re hs')
  calc
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖
        = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := by
      rw [h, div_mul_cancel_left₀ (left_ne_zero_of_mul (h ▸ riemannZeta_ne_zero_of_one_lt_re hs')),
        norm_inv, (HasProd.inv₀ ?_ (norm_ne_zero_iff.2 hL)).tprod_eq]
      convert (TauCeti.LSeries_moebius_sq_eulerProduct_hasProd hs').norm using 2 with p
      rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (by positivity), ← ofReal_one,
        ← ofReal_add, norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ :=
        tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine σ t hσ
    _ = ‖riemannZeta (verticalLine σ t)‖ := by
      simpa only [norm_inv] using (riemannZeta_eulerProduct_hasProd hs).norm.tprod_eq

/-- Convexity input at `σ = 3/2`: `‖ζ 3 / ζ (3/2)‖ ≤ ‖ζ (3/2 + it)‖`. -/
theorem norm_riemannZeta_ratio_le_on_vertical_line (t : ℝ) :
    ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖ ≤ ‖riemannZeta (verticalLine (3 / 2 : ℝ) t)‖ := by
  have hσ : 1 < (3 / 2 : ℝ) := by norm_num
  have h2 : (2 : ℂ) * ((3 / 2 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  simpa [h2, div_eq_mul_inv, mul_comm] using
    norm_riemannZeta_ratio_le_on_verticalLine (3 / 2 : ℝ) t hσ
