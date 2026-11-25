/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.AbsMax
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
import TauCeti.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Topology.Algebra.InfiniteSum.Group
public import TauCeti.Analysis.Complex.GrowthOrder.Exponential
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorNativeProduct
import TauCeti.Analysis.Complex.Hadamard.FiniteOrder
import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct
import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Normed.Group.SummableNormInvRpow

/-!
# Hadamard factorization from a logarithmic growth bound

`hadamard_factorization_of_growth` states Tau Ceti's finite-order Hadamard factorization
(`TauCeti.finite_order_hadamard`) for the divisor-indexed product `divisorCanonicalProduct`: an
entire `f` with a logarithmic growth bound of order `ρ` factors as `exp(P) · z^k · ∏ E_m`. Tau Ceti
supplies the factorization over all nonzero complex numbers and the degree bound on its exponent;
`divisorCanonicalProduct_eq_tprod_analyticOrderNatAt` identifies the products.

## Main results

* `hadamard_factorization_of_growth` : entire `f` with log-growth of order `ρ` is a Weierstrass
  product times `exp(P)`

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

/-- Hadamard factorization from a global logarithmic growth bound, from Tau Ceti's factorization
over the nonzero complex numbers and its degree bound for the exponent. -/
theorem hadamard_factorization_of_growth {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  obtain ⟨C, hC0, hC⟩ := hgrowth
  have h := TauCeti.orderLE_of_eventually_log_one_add_norm_le_mul_rpow (.of_forall hC)
  have hρn : ρ < ⌊ρ⌋₊ + 1 := Nat.lt_floor_add_one ρ
  have hsum := h.summable_analyticOrderNatAt_mul_norm_inv_rpow hentire hρn
  obtain ⟨g, hg, hfg⟩ := hentire.exists_eq_pow_mul_exp_mul_tprod_nonzero_weierstrassFactor_div_pow
    hnot (p := fun _ ↦ ⌊ρ⌋₊) fun R _ ↦ hsum.natCast_mul_div_pow_succ (by positivity) le_rfl R
  obtain ⟨P, hP, rfl⟩ := h.exists_eq_polynomial_eval_of_eq_pow_mul_exp_mul_tprod hentire hρn hg hfg
  refine ⟨P, Polynomial.degree_le_of_natDegree_le hP, fun z ↦ ?_⟩
  rw [hfg z, divisorCanonicalProduct_eq_tprod_analyticOrderNatAt hentire
    (summable_norm_inv_pow_divisorZeroIndex₀_of_growth hρ hentire ⟨C, hC0, hC⟩) z]
  ring

end Complex.Hadamard
