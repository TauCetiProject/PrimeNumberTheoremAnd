/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

import TauCeti.Analysis.SpecialFunctions.Complex.Log.Taylor
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax


/-!
## Pointwise inverse bounds for Weierstrass factors in Cartan-type arguments

This file proves the near-regime inverse estimate used in Cartan/minimum-modulus arguments for
Hadamard factorization. It combines `Complex.CartanBound.log_norm_one_sub_div_ge_neg_phi` with the
Weierstrass factor formula and a finite Taylor-sum bound.

The estimate is stated in a form convenient for divisor-indexed zero enumerations.
-/

@[expose] public section

noncomputable section

namespace Complex.Hadamard

open Complex Real

/-!
### Near regime: `‖(E_m(u/a))⁻¹‖` controlled by `φ(r/‖a‖)` plus an exponent term.
-/

lemma norm_inv_weierstrassFactor_le_exp_near
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(weierstrassFactor m (u / a))⁻¹‖
      ≤ Real.exp (CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
    CartanBound.log_norm_one_sub_div_ge_neg_phi (hur := hur) (ha := ha) (hr := hr)
  have hbase : Real.log ‖1 - u / a‖ - ‖logTaylor (m + 1) (-(u / a))‖ ≤
      Real.log ‖weierstrassFactor m (u / a)‖ := by
    by_cases hz : u / a = 1
    · simp [hz]
    have hne : ‖1 - u / a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
    rw [weierstrassFactor_def, norm_mul, Complex.norm_exp,
      Real.log_mul hne (Real.exp_pos _).ne', Real.log_exp]
    simpa only [Complex.neg_re, sub_eq_add_neg] using
      sub_le_sub_left (Complex.re_le_norm (logTaylor (m + 1) (-(u / a))))
        (Real.log ‖1 - u / a‖)
  have hlogE :
      Real.log ‖weierstrassFactor m (u / a)‖
        ≥ -CartanBound.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    have hpls : ‖logTaylor (m + 1) (-(u / a))‖ ≤ (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      rw [← norm_neg, neg_logTaylor_succ_neg_eq_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (max 1 (‖u / a‖ ^ m)) fun k hk ↦ ?_).trans_eq
        (by simp)
      rw [norm_div, norm_pow, ← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]
      refine (div_le_self (by positivity)
        (le_add_of_nonneg_left (Nat.cast_nonneg k))).trans ?_
      rw [← (one_pow m : (1 : ℝ) ^ m = 1), ← max_pow_of_nonneg zero_le_one (norm_nonneg (u / a))]
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)))
    linarith [hbase, hlog_one, hpls]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
    rw [← (one_pow m : (1 : ℝ) ^ m = 1),
      ← max_pow_of_nonneg zero_le_one (norm_nonneg (u / a)), ← Real.rpow_natCast]
    refine (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hmτ).trans ?_
    rw [Real.rpow_max zero_le_one (norm_nonneg _) ((Nat.cast_nonneg m).trans hmτ),
      Real.one_rpow]
    simpa only [norm_div, hur, one_pow] using
      max_le_add_of_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg (u / a)) τ)
  have hneglog :
      -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

end Complex.Hadamard
