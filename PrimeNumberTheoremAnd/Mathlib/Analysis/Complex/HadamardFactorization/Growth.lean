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

/-!
# Hadamard factorization from a logarithmic growth bound

Assembles the Hadamard quotient, divisor summability, Cartan bounds, and exponential-polynomial
growth into `hadamard_factorization_of_growth`. The pipeline is:

1. `Summability` — Jensen / `logCounting` bounds imply divisor-indexed product convergence
2. `HadamardFactorization` — entire zero-free Hadamard quotient `H = f / (z^k · ∏ E_m)`
3. This file — good-circle bounds on `H`, then native exponential-order polynomial rigidity
4. `Order` — upgrade to `EntireOfOrderAtMost` and genus `⌊ρ⌋`

All products use `divisorCanonicalProduct` centered at `0` with multiplicities from
`MeromorphicOn.divisor`.

Compared with Tao's proof of the finite-order Hadamard theorem, this file replaces the
good-circle averaging argument by Cartan's good-circle estimate
`Complex.exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div` from Tau Ceti.
The purpose is the same:
obtain sufficiently many circles on which the canonical product is not too small, so the zero-free
Hadamard quotient has polynomial exponential growth.  Thus the route is:
Jensen/zero counting (Tao Theorem 2 and Proposition 8) → canonical-product convergence (forward
Exercise 19 input) → Cartan minimum-modulus alternative to the good-circle step → finite-order
Hadamard (Theorem 22).

## Main results

* `hadamard_factorization_of_growth` : entire `f` with log-growth of order `ρ` is a Weierstrass
  product times `exp(P)`
* `TauCeti.OrderLE.exists_eq_cexp_polynomial_eval_of_forall_ne_zero` : its zero-free quotient
  is a polynomial exponential
* the good-circle bounds extend to discs by Mathlib’s
  `Complex.norm_le_of_forall_mem_frontier_norm_le`

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

/-- Hadamard factorization from a global logarithmic growth bound.

The minimum-modulus step in this proof is supplied by Cartan's good-circle estimate; this is an
alternative to Tao's good-circle averaging step, with the same role in bounding the zero-free
Hadamard quotient. -/
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
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (summable_norm_inv_pow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
        hρ hentire hgrowth)
  rcases exists_entire_nonzero_hadamardQuotient (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  obtain ⟨τ, hτ, hτ_lt⟩ := exists_between (Nat.lt_floor_add_one (a := ρ))
  have hτ_nonneg : 0 ≤ τ := hρ.trans hτ.le
  have hfloorτ' : Nat.floor τ = Nat.floor ρ :=
    (Nat.floor_eq_iff hτ_nonneg).mpr ⟨(Nat.floor_le hρ).trans hτ.le, hτ_lt⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hmρ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    hadamardQuotient_norm_le_exp_rpow_of_growth (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ hmρ hτ hτ_lt hτ_nonneg hentire hH_entire hnot h_sum hgrowth hfactor
  obtain ⟨C, hC, hbound⟩ := hH_bound_rpow
  have horder : TauCeti.OrderLE H τ := by
    apply TauCeti.orderLE_def.mpr
    intro p hp
    refine (IsBigO.of_bound 1 ?_).trans
      (TauCeti.isBigO_exp_mul_norm_rpow (C * 2 ^ τ) hp)
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    have hpow : (1 + ‖z‖) ^ τ ≤ 2 ^ τ * ‖z‖ ^ τ := by
      simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)] using
        Real.rpow_le_rpow (by positivity) (by linarith : 1 + ‖z‖ ≤ 2 * ‖z‖) hτ_nonneg
    simpa only [Real.norm_eq_abs, Real.abs_exp, one_mul, mul_assoc] using
      (hbound z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hC.le))
  obtain ⟨P, hP, hHP⟩ :=
    horder.exists_eq_cexp_polynomial_eval_of_forall_ne_zero hH_entire hH_ne
  have hPnat : P.natDegree ≤ m := by simpa only [hfloorτ] using hP
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)

end Complex.Hadamard
