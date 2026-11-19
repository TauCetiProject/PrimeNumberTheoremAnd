/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Field
import TauCeti.NumberTheory.LSeries.Moebius

/-!
# Extra Riemann zeta API

Vertical lines, prime-power bounds, and Euler-product identities supporting strip
and convexity bounds in `RiemannZetaConvexity`.

## Main results

* `verticalLine`, `verticalLine_re`
* `Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical`
* `norm_riemannZeta_eulerProduct`, `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine`
-/

@[expose] public section

open scoped BigOperators Topology
open Complex Filter Real Set

/-- The point `σ + it` on the vertical line with real part `σ`. -/
def verticalLine (σ t : ℝ) : ℂ := σ + t * Complex.I

lemma verticalLine_re (σ t : ℝ) : (verticalLine σ t).re = σ := by
  simp [verticalLine]

namespace Nat.Primes

/-- Compare inverse Euler factors on the vertical line `σ + it` with `1 < σ`. -/
lemma inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical (p : Nat.Primes) (σ t : ℝ)
    (hσ : 1 < σ) :
    (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      (‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖)⁻¹ := by
  have hpos : 0 < ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ :=
    norm_pos_iff.mpr (Complex.one_sub_prime_cpow_ne_zero p.prop (by rwa [verticalLine_re]))
  have htriangle :
      ‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖ ≤ 1 + ((p : ℕ) : ℝ) ^ (-σ) := by
    simpa [Complex.norm_natCast_cpow_of_pos p.property.pos, verticalLine] using
      (norm_sub_le (1 : ℂ) (((p : ℕ) : ℂ) ^ (-verticalLine σ t)))
  simpa [one_div] using one_div_le_one_div_of_le hpos htriangle

end Nat.Primes

section RiemannZetaEulerProduct

open Nat.Primes

theorem norm_riemannZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
  calc
    ‖riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      rw [riemannZeta_eulerProduct_tprod hs]
    _ = ∏' p : Nat.Primes, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      exact Multipliable.norm_tprod (riemannZeta_eulerProduct_hasProd hs).multipliable
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
      congr 1; ext p; simp [norm_inv]

/-- On the vertical line `re s = σ > 1`, the real product `∏_p (1 + p^{-σ})^{-1}` is dominated
by the Euler product at `σ + it`. -/
theorem tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ := by
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hf₀ : ∀ p : Nat.Primes, 0 < (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := fun _ => by positivity
  have hs' : 1 < (σ : ℂ).re := by simpa using hσ
  have hL := right_ne_zero_of_mul (TauCeti.riemannZeta_eq_mul_LSeries_moebius_sq hs' ▸
    riemannZeta_ne_zero_of_one_lt_re hs')
  have hf : Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := by
    refine (HasProd.inv₀ ?_ (norm_ne_zero_iff.2 hL)).multipliable
    convert (TauCeti.LSeries_moebius_sq_eulerProduct_hasProd hs').norm using 2 with p
    rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (by positivity), ← ofReal_one, ← ofReal_add,
      norm_real, Real.norm_of_nonneg (by positivity)]
  have hg : Multipliable fun p : Nat.Primes => (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
    simpa only [norm_inv] using (riemannZeta_eulerProduct_hasProd hs).multipliable.norm
  apply le_of_tendsto_of_tendsto' hf.hasProd hg.hasProd
  intro v
  exact Finset.prod_le_prod₀ (fun p _ => (hf₀ p).le) fun p _ =>
    Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical p σ t hσ

end RiemannZetaEulerProduct

end
