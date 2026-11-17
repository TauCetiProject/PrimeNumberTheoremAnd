/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Bounds for the Riemann zeta function

Strip bounds for `riemannZeta`, used in `ZetaFiniteOrder`. Euler-product input is in
`PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta`.

## Main results

* `norm_riemannZeta_le` : strip bound for the Λ₀ pipeline
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
  calc
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖
        = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ :=
          norm_riemannZeta_div_riemannZeta σ hσ
    _ ≤ ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ :=
        tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine σ t hσ
    _ = ‖riemannZeta (verticalLine σ t)‖ := by
      simpa [verticalLine] using (norm_riemannZeta_eulerProduct (verticalLine σ t) hs).symm

/-- Convexity input at `σ = 3/2`: `‖ζ 3 / ζ (3/2)‖ ≤ ‖ζ (3/2 + it)‖`. -/
theorem norm_riemannZeta_ratio_le_on_vertical_line (t : ℝ) :
    ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖ ≤ ‖riemannZeta (verticalLine (3 / 2 : ℝ) t)‖ := by
  have hσ : 1 < (3 / 2 : ℝ) := by norm_num
  have h2 : (2 : ℂ) * ((3 / 2 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  simpa [h2, div_eq_mul_inv, mul_comm] using
    norm_riemannZeta_ratio_le_on_verticalLine (3 / 2 : ℝ) t hσ

/-!
### Abel strip bounds
-/

/-- On `zetaAbelContinuationDomain`, `‖ζ s‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / re s`. -/
theorem norm_riemannZeta_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  rw [riemannZeta_eq_zetaAbelContinuationFormula s
    (zetaAbelContinuationDomain_re_pos hs) hs.1]
  exact norm_zetaAbelContinuationFormula_le s (zetaAbelContinuationDomain_re_pos hs)
