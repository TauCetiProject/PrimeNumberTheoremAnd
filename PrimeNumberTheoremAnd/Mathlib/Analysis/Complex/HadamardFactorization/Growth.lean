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
import TauCeti.Analysis.Complex.CanonicalProduct.GoodCircle
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

`hadamardQuotient_norm_le_exp_rpow_of_growth` bounds the zero-free quotient
`H = f / (z^k · ∏ E_m)` on the circles of Cartan's good-circle estimate
`Complex.exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div` from Tau Ceti,
in place of Tao's good-circle averaging step, and extends the bound to discs by Mathlib's
`Complex.norm_le_of_forall_mem_frontier_norm_le`.

## Main results

* `hadamard_factorization_of_growth` : entire `f` with log-growth of order `ρ` is a Weierstrass
  product times `exp(P)`
* `hadamardQuotient_norm_le_exp_rpow_of_growth` : the zero-free quotient has exponential growth
  of any order larger than `ρ`

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

/-- The Hadamard quotient inherits a finite-order exponential norm bound. -/
theorem hadamardQuotient_norm_le_exp_rpow_of_growth {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f) (hH_entire : Differentiable ℂ H)
    (_hnot : ∃ z : ℂ, f z ≠ 0)
    (_h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
  have hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ) (τ := τ)
      hρ hτ hentire ⟨Cf, hCfpos, hCf⟩
  set K : ℝ := ((Real.log 2 + 12 * Real.sqrt 6 + m) * 4 ^ τ + m + 2) *
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hK : 0 ≤ K := mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ by positivity)
  refine ⟨(Cf + K) * 3 ^ τ, mul_pos (by linarith) (by positivity), fun z ↦ ?_⟩
  -- Tau Ceti's good circle: a radius `r ∈ (R, 2R]` on which the canonical product is not small.
  obtain ⟨r, hr, hgood⟩ :=
    Complex.exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div m
      (hmρ.trans hτ.le) hτ_lt.le hsumτ (R := max ‖z‖ 1) (by positivity)
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr.1.le
  have hrτ : r ^ τ ≤ (1 + r) ^ τ := Real.rpow_le_rpow (by linarith) (by linarith) hτ_nonneg
  have hcircle (u : ℂ) (hu : ‖u‖ = r) : ‖H u‖ ≤ Real.exp ((Cf + K) * (1 + r) ^ τ) := by
    have hP := hgood u hu
    have hf : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
      rw [← hu]
      exact (le_add_of_nonneg_left zero_le_one).trans (Real.le_exp_of_log_le ((hCf u).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg u])
          hτ.le) hCfpos.le)))
    have hpow : 1 ≤ ‖u ^ analyticOrderNatAt f 0‖ := by rw [norm_pow, hu]; exact one_le_pow₀ hr1
    have key : ‖H u‖ * Real.exp (-(K * r ^ τ)) ≤ Real.exp (Cf * (1 + r) ^ τ) := by
      calc ‖H u‖ * Real.exp (-(K * r ^ τ))
          ≤ ‖H u‖ * (‖u ^ analyticOrderNatAt f 0‖ *
              ‖divisorCanonicalProduct m f (Set.univ : Set ℂ) u‖) := by
            gcongr
            exact hP.trans (le_mul_of_one_le_left (norm_nonneg _) hpow)
        _ = ‖f u‖ := by rw [hfactor u, norm_mul, norm_mul, mul_assoc]
        _ ≤ _ := hf
    rw [← le_div_iff₀ (Real.exp_pos _), ← Real.exp_sub] at key
    exact key.trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hrτ hK]))
  have hrpos : 0 < r := by linarith
  have hball : ‖H z‖ ≤ Real.exp ((Cf + K) * (1 + r) ^ τ) := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      hH_entire.diffContOnCl (fun u hu ↦ hcircle u ?_)
      (subset_closure (show z ∈ Metric.ball (0 : ℂ) r by
        rw [Metric.mem_ball, dist_zero_right]; exact (le_max_left _ _).trans_lt hr.1))
    simpa only [frontier_ball (0 : ℂ) hrpos.ne', Metric.mem_sphere, dist_zero_right] using hu
  have hr3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
    have : max ‖z‖ 1 ≤ 1 + ‖z‖ := max_le (by linarith) (by linarith [norm_nonneg z])
    linarith [hr.2, norm_nonneg z]
  refine hball.trans (Real.exp_le_exp.mpr ?_)
  rw [mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hr3 hτ_nonneg) (by linarith)

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
