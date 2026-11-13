/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
public import Mathlib.Analysis.Real.Pi.Bounds
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity


/-!
# Reflection and pole-removed growth for the Riemann zeta function

This file proves a growth bound for the removable extension of `(s - 1)ζ(s)` and
records reflected functional-equation identities. Global growth of the entire completed
function `completedRiemannZeta₀` (Λ₀) is supplied by the native Hurwitz zeta growth theorem
at parameter zero.

Note: Mathlib distinguishes between:
- `completedRiemannZeta₀` : the entire function Λ₀(s)
- `completedRiemannZeta` : Λ(s) = Λ₀(s) - 1/s - 1/(1-s), which has simple poles at 0 and 1

The key ingredients are:
* Mathlib's functional equations for completed and uncompleted zeta functions
* Mathlib's entire removable extension `DirichletCharacter.LFunctionTrivChar₁`
* Stirling-type bounds for `Complex.Gamma`
* `norm_riemannZeta_le` from `RiemannZetaConvexity` for strip bounds on `ζ`

## Main results

* `zeta_minus_pole_entire_growth` : a coarse global bound for the removable extension of
  `(s - 1)ζ(s)`.

## References

* [tao246bComplexAnalysis], Theorem 22 and Exercise 23, for the order-one growth input used in
  the finite-order Hadamard strategy for completed zeta functions
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function growth
  background; the formalized object here is the additive pole-removal `Λ₀`, not Riemann's `ξ`

## Tags

Riemann zeta function, completed zeta function, finite order, Hadamard factorization
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace Complex

/-! ### Finite order of the completed zeta function -/

/-- The functional equation lets one work in the half-plane `1 / 2 ≤ re z`. -/
lemma exists_completedRiemannZeta₀_right_halfPlane (z : ℂ) :
    ∃ w : ℂ,
      completedRiemannZeta₀ w = completedRiemannZeta₀ z ∧
        (2⁻¹ : ℝ) ≤ w.re ∧ ‖w‖ ≤ 1 + ‖z‖ := by
  refine ⟨if z.re < (2⁻¹ : ℝ) then 1 - z else z, ?_, ?_, ?_⟩
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z) = 1 - z := by
        simp [hzr]
      simpa [hw] using (completedRiemannZeta₀_one_sub z)
    · simp [hzr]
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have : (if z.re < (2⁻¹ : ℝ) then 1 - z else z).re = 1 - z.re := by
        simp [hzr]
      linarith [this, hzr]
    · simpa [hzr] using le_of_not_gt hzr
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z) = 1 - z := by
        simp [hzr]
      have : ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := by
        simpa using (norm_sub_le (1 : ℂ) z)
      simpa [hw, norm_one, add_comm, add_left_comm, add_assoc] using this
    · simp [hzr]

/-- If `re z ≤ σ₀`, then `1 - σ₀ ≤ re (1 - z)` for `σ₀ = zetaAbelContinuationReLower`. -/
lemma one_sub_re_ge_one_sub_zetaAbelContinuationReLower_of_re_le {z : ℂ}
    (hz : z.re ≤ zetaAbelContinuationReLower) :
    (1 - zetaAbelContinuationReLower) ≤ (1 - z).re := by
  have hz' : z.re ≤ (1 / 10 : ℝ) := by
    dsimp [zetaAbelContinuationReLower] at hz
    exact hz
  have h : (9 / 10 : ℝ) ≤ 1 - z.re := by linarith [hz']
  calc (1 - zetaAbelContinuationReLower : ℝ)
      = (9 / 10 : ℝ) := by
        norm_num [zetaAbelContinuationReLower, one_sub_zetaAbelContinuationReLower]
    _ ≤ 1 - z.re := h
    _ = (1 - z).re := by simp [Complex.sub_re]

/-- The zeta functional equation written with a reflected variable `w = 1 - z`. -/
lemma riemannZeta_eq_reflected {z w : ℂ} (hw : w = 1 - z)
    (hw_ne_neg : ∀ n : ℕ, w ≠ -n) (hw_ne_one : w ≠ 1) :
    riemannZeta z =
      2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) *
        riemannZeta w := by
  have h := riemannZeta_one_sub (s := w) (hs := hw_ne_neg) (hs' := hw_ne_one)
  have hsub : 1 - w = z := by
    rw [hw]
    ring
  simpa [hsub, mul_assoc, mul_left_comm, mul_comm] using h

/-- The large coefficient in the reflected zeta estimate is dominated by the chosen constant. -/
lemma reflected_zeta_coefficient_le {C CΓ : ℝ} (hCΓ : 0 ≤ CΓ)
    (hC : max (40 : ℝ) (20 * CΓ + 500) ≤ C) :
    (2 + CΓ + 2 + 40 : ℝ) ≤ C := by
  have : (20 * CΓ + 500 : ℝ) ≤ C := le_trans (le_max_right _ _) hC
  nlinarith [this, hCΓ]

/-- Reflected functional-equation factors obey the global zeta growth majorant. -/
lemma norm_mul_riemannZeta_le_exp_of_reflected {z w : ℂ} {A CΓ C : ℝ}
    (hw : w = 1 - z)
    (hzeta_fe : riemannZeta z = 2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) *
      riemannZeta w)
    (hpow_le1 : ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1)
    (hw_norm_le : ‖w‖ ≤ A) (hA1 : 1 ≤ A) (hA2_nonneg : 0 ≤ A ^ (2 : ℝ))
    (hΓw : ‖Complex.Gamma w‖ ≤ rexp (CΓ * A ^ (2 : ℝ)))
    (hcosw : ‖Complex.cos (π * w / 2)‖ ≤ rexp (2 * A ^ (2 : ℝ)))
    (hζw : ‖riemannZeta w‖ ≤ rexp (40 * A ^ (2 : ℝ)))
    (hcoef : (2 + CΓ + 2 + 40 : ℝ) ≤ C) :
    ‖(z - 1) * riemannZeta z‖ ≤ rexp (C * A ^ (2 : ℝ)) := by
  have hprod :
      ‖(z - 1) * riemannZeta z‖ ≤
        (‖w‖ * 2) * ‖Complex.Gamma w‖ *
          ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
    have hz1 : (z - 1 : ℂ) = -w := by
      rw [hw]
      ring
    have hζ :
        ‖riemannZeta z‖ ≤
          ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
            Complex.cos (π * w / 2) * riemannZeta w‖ := by
      simp [hzeta_fe]
    calc
      ‖(z - 1) * riemannZeta z‖
          ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by simp
      _ ≤ ‖z - 1‖ *
            ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
              Complex.cos (π * w / 2) * riemannZeta w‖ := by
          gcongr
      _ = ‖w‖ *
            ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
              Complex.cos (π * w / 2) * riemannZeta w‖ := by
          simp [hz1]
      _ ≤ ‖w‖ * ((2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ *
            ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
            ‖riemannZeta w‖) := by
          have :
              ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
                  Complex.cos (π * w / 2) * riemannZeta w‖
                ≤ (2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ *
                  ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
                  ‖riemannZeta w‖ := by
            simp [mul_assoc, mul_left_comm, mul_comm]
          gcongr
      _ ≤ ‖w‖ * ((2 : ℝ) * 1 * ‖Complex.Gamma w‖ *
            ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖) := by
          gcongr
      _ = (‖w‖ * 2) * ‖Complex.Gamma w‖ *
            ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
          ring
  have hw2 : ‖w‖ * 2 ≤ rexp (2 * A ^ (2 : ℝ)) := by
    simpa [Real.rpow_two, sq] using Real.two_mul_le_exp_two_mul_sq hw_norm_le hA1
  have hmul_exp :
      (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
          ‖riemannZeta w‖ ≤
        rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) := by
    have h := Real.mul_four_le_exp_add (a := ‖w‖ * 2) (b := ‖Complex.Gamma w‖)
      (c := ‖Complex.cos (π * w / 2)‖) (d := ‖riemannZeta w‖)
      (A := 2 * A ^ (2 : ℝ)) (B := CΓ * A ^ (2 : ℝ))
      (C := 2 * A ^ (2 : ℝ)) (D := 40 * A ^ (2 : ℝ))
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hw2 hΓw hcosw hζw
    have hsum :
        2 * A ^ (2 : ℝ) + CΓ * A ^ (2 : ℝ) +
            2 * A ^ (2 : ℝ) + 40 * A ^ (2 : ℝ) =
          (2 + CΓ + 2 + 40) * A ^ (2 : ℝ) := by
      ring
    exact h.trans_eq (congrArg rexp hsum)
  have hdom :
      rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) ≤ rexp (C * A ^ (2 : ℝ)) := by
    refine (Real.exp_le_exp).2 ?_
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hA2_nonneg
  exact le_trans (le_trans hprod hmul_exp) hdom

/-- A coarse global growth bound for the removable extension of `(s - 1)ζ(s)`.

The proof combines the half-plane zeta bound, the functional equation, and the Gamma strip bound. -/
theorem zeta_minus_pole_entire_growth :
    ∃ C > 0, ∀ z : ℂ,
      Real.log (1 + ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖) ≤ C * (1 + ‖z‖) ^ (2 : ℝ) := by
  have hcont :
      ContinuousOn (DirichletCharacter.LFunctionTrivChar₁ 1) (Metric.closedBall (0 : ℂ) 3) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn
  obtain ⟨M, hM_nonneg, hM⟩ := exists_norm_bound_on_closedBall hcont
  obtain ⟨CΓ, hCΓ_pos, hΓ⟩ := Complex.Gamma.stirling_bound_re_ge_zero
  let C : ℝ := max (Real.log (1 + M) + 10) (max (40 : ℝ) (20 * CΓ + 500))
  refine ⟨C + Real.log 2, ?_, ?_⟩
  · have hCpos : (0 : ℝ) < C := by
      have : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
      exact lt_of_lt_of_le this (le_trans (le_max_right _ _) (le_max_right _ _))
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro z
    set A : ℝ := 1 + ‖z‖
    have hA1 : (1 : ℝ) ≤ A := by dsimp [A]; linarith [norm_nonneg z]
    have hA2_nonneg : 0 ≤ A ^ (2 : ℝ) := by positivity
    by_cases hz_small : ‖z‖ ≤ 3
    · have hnorm : ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖ ≤ M := hM z hz_small
      have hlog :
          Real.log (1 + ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖) ≤ Real.log (1 + M) := by
        refine Real.log_le_log (by positivity) ?_
        linarith
      have hC1 : Real.log (1 + M) ≤ C + Real.log 2 := by
        have : Real.log (1 + M) + 10 ≤ C := by
          simp [C]
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have hpow : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
        Real.one_le_rpow hA1 (by norm_num)
      have hC_nonneg : 0 ≤ C + Real.log 2 := by
        have hCpos : (0 : ℝ) < C := by
          have hpos' : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
          have hmax : (0 : ℝ) < max (40 : ℝ) (20 * CΓ + 500) :=
            lt_of_lt_of_le hpos' (le_max_right _ _)
          have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
            simp [C]
          exact lt_of_lt_of_le hmax hle
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      calc
        Real.log (1 + ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖)
            ≤ Real.log (1 + M) := hlog
        _ ≤ C + Real.log 2 := hC1
        _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
              simpa [mul_one] using (mul_le_mul_of_nonneg_left hpow hC_nonneg)
    · have hz_large : 3 < ‖z‖ := lt_of_not_ge hz_small
      have hz_ne1 : z ≠ 1 := by
        intro h
        have : (‖z‖ : ℝ) = 1 := by simp [h]
        linarith [hz_large]
      have hzeta_def : (DirichletCharacter.LFunctionTrivChar₁ 1) z = (z - 1) * riemannZeta z := by
        simp [DirichletCharacter.LFunctionTrivChar₁, DirichletCharacter.LFunctionTrivChar,
          Function.update_of_ne hz_ne1]
      have hmain :
          ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) := by
        by_cases hz_re : zetaAbelContinuationReLower < z.re
        · have hs_dom := mem_zetaAbelContinuationDomain_of_re hz_ne1
            (by simpa [zetaAbelContinuationReLower] using hz_re)
          have hζ := norm_riemannZeta_le z hs_dom
          have hzm1_le : ‖z - 1‖ ≤ A := by
            simpa [A, add_comm] using norm_sub_le z (1 : ℂ)
          have hfrac : ‖z‖ / z.re ≤ 10 * ‖z‖ := norm_div_re_le_ten_mul_norm_of_mem hs_dom
          have hpoly :
              ‖(z - 1) * riemannZeta z‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
            have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
            have hz_le_A : ‖z‖ ≤ A := by dsimp [A]; linarith [hz0]
            have hζ' : ‖riemannZeta z‖ ≤ 1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖ := by
              calc
                ‖riemannZeta z‖ ≤ 1 + ‖1 / (z - 1)‖ + ‖z‖ / z.re := hζ
                _ ≤ 1 + ‖1 / (z - 1)‖ + 10 * ‖z‖ := by gcongr
            have hmul_inv : ‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖ = 1 := by
              have hz1' : z - 1 ≠ (0 : ℂ) := sub_ne_zero.2 hz_ne1
              simp [hz1']
            have hterm3 : ‖z - 1‖ * (10 * ‖z‖) ≤ A * (10 * ‖z‖) :=
              mul_le_mul_of_nonneg_right hzm1_le (by positivity)
            have hApos : (0 : ℝ) ≤ A := le_trans (by norm_num) hA1
            have hA2 : A * (10 * ‖z‖) ≤ 10 * (A ^ (2 : ℕ)) := by
              have : A * ‖z‖ ≤ A * A := by nlinarith [hz_le_A]
              nlinarith [this]
            have hstep : A + 1 + A * (10 * ‖z‖) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
              have hA1' : A + 1 ≤ 2 * A := by nlinarith [hA1]
              have hstep1 : A + 1 + A * (10 * ‖z‖) ≤ 2 * A + 10 * (A ^ (2 : ℕ)) := by
                nlinarith [hA1', hA2]
              have hA_le_sq : A ≤ (A ^ (2 : ℕ)) := by
                simpa [pow_two] using (mul_le_mul_of_nonneg_right hA1 hApos)
              have hstep2 : 2 * A + 10 * (A ^ (2 : ℕ)) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
                nlinarith [hA_le_sq]
              exact le_trans hstep1 hstep2
            calc
              ‖(z - 1) * riemannZeta z‖ ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by simp
              _ ≤ ‖z - 1‖ * (1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖) := by gcongr
              _ = ‖z - 1‖ + (‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖) + ‖z - 1‖ * (10 * ‖z‖) := by ring
              _ ≤ A + 1 + A * (10 * ‖z‖) := by nlinarith [hzm1_le, hmul_inv, hterm3]
              _ ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := hstep
              _ = (40 : ℝ) * A ^ (2 : ℝ) := by simp
          have hC_ge : (40 : ℝ) ≤ C := by
            have h1 : (40 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) := le_max_left _ _
            have h2 : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
              simp [C]
            exact le_trans h1 h2
          have hle : (40 : ℝ) * A ^ (2 : ℝ) ≤ C * A ^ (2 : ℝ) := by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC_ge hA2_nonneg)
          have : ‖(z - 1) * riemannZeta z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) :=
            le_trans (le_trans hpoly hle) (Real.le_exp_self _)
          simpa [hzeta_def] using this
        · have hz_re_le : z.re ≤ zetaAbelContinuationReLower := le_of_not_gt hz_re
          let w : ℂ := 1 - z
          have hw_re_ge : (1 - zetaAbelContinuationReLower) ≤ w.re :=
            one_sub_re_ge_one_sub_zetaAbelContinuationReLower_of_re_le hz_re_le
          have hw_re0 : 0 ≤ w.re := by
            have : (0 : ℝ) < 1 - zetaAbelContinuationReLower := by
              rw [one_sub_zetaAbelContinuationReLower]; norm_num
            linarith [hw_re_ge]
          have hw_re1 : zetaAbelContinuationReLower < w.re :=
            lt_of_lt_of_le
              (by norm_num [zetaAbelContinuationReLower, one_sub_zetaAbelContinuationReLower])
              hw_re_ge
          have hw_ne1 : w ≠ 1 := by
            simpa [w] using Complex.one_sub_ne_one_of_norm_pos (lt_trans (by norm_num) hz_large)
          have hw_ne_neg : ∀ n : ℕ, w ≠ -n := by
            exact Complex.ne_neg_nat_of_re_pos (lt_trans zetaAbelContinuationReLower_pos hw_re1)
          have hzeta_fe :
              riemannZeta z =
                2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w := by
            exact riemannZeta_eq_reflected (by simp [w]) hw_ne_neg hw_ne1
          have hpow_le1 : ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 :=
            Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one hw_re0
          have hw_norm_le : ‖w‖ ≤ A := by
            simpa [w, A] using norm_sub_le (1 : ℂ) z
          have hw_norm_ge1 : (1 : ℝ) ≤ ‖w‖ := by
            simpa [w] using one_le_norm_one_sub_of_norm_gt_three hz_large
          have hΓw : ‖Complex.Gamma w‖ ≤ Real.exp (CΓ * A ^ (2 : ℝ)) := by
            have hΓ0 := hΓ w hw_re0 hw_norm_ge1
            have hlog_le : Real.log (1 + ‖w‖) ≤ A := by
              have : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) - 1 := by
                have : (0 : ℝ) < 1 + ‖w‖ := by positivity
                simpa using (Real.log_le_sub_one_of_pos this)
              have : Real.log (1 + ‖w‖) ≤ ‖w‖ := by simpa [sub_eq_add_neg] using this
              exact le_trans this hw_norm_le
            have hmul : ‖w‖ * Real.log (1 + ‖w‖) ≤ A ^ (2 : ℝ) := by
              have : ‖w‖ * Real.log (1 + ‖w‖) ≤ A * A := by nlinarith [hw_norm_le, hlog_le]
              simpa [pow_two] using this
            have hexp : CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ CΓ * A ^ (2 : ℝ) := by
              have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
              nlinarith [hmul, hC0]
            exact le_trans hΓ0 (Real.exp_le_exp.mpr hexp)
          have hcosw : ‖Complex.cos (π * w / 2)‖ ≤ Real.exp (2 * A ^ (2 : ℝ)) := by
            have h1 := norm_cos_le_exp_abs_im (π * w / 2)
            have him : |(π * w / 2).im| ≤ 2 * A ^ (2 : ℝ) := by
              have : |(π * w / 2).im| ≤ ‖π * w / 2‖ := Complex.abs_im_le_norm _
              have hnorm : ‖π * w / 2‖ = (Real.pi / 2) * ‖w‖ := by
                have hrew : (π * w / 2 : ℂ) = (π / 2) * w := by
                  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                calc
                  ‖π * w / 2‖ = ‖(π / 2) * w‖ := by simp [hrew]
                  _ = ‖(π / 2)‖ * ‖w‖ := by simp
                  _ = (Real.pi / 2) * ‖w‖ := by simp
              have hpi : (Real.pi / 2 : ℝ) ≤ 2 := by
                have : (Real.pi : ℝ) ≤ 4 := by linarith [Real.pi_lt_four.le]
                nlinarith
              have him1 : |(π * w / 2).im| ≤ 2 * ‖w‖ := by
                calc
                  |(π * w / 2).im| ≤ ‖π * w / 2‖ := this
                  _ = (Real.pi / 2) * ‖w‖ := hnorm
                  _ ≤ 2 * ‖w‖ := by gcongr
              have him2 : 2 * ‖w‖ ≤ 2 * A ^ (2 : ℝ) := by
                have : ‖w‖ ≤ A ^ (2 : ℝ) := by
                  have : A ≤ A ^ (2 : ℝ) := by
                    have := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
                    simpa [Real.rpow_one] using this
                  exact le_trans hw_norm_le this
                nlinarith [this]
              exact le_trans him1 him2
            exact le_trans h1 (Real.exp_le_exp.mpr him)
          have hζw : ‖riemannZeta w‖ ≤ Real.exp (40 * A ^ (2 : ℝ)) := by
            have hw_dom := mem_zetaAbelContinuationDomain_of_re hw_ne1 (by linarith [hw_re1])
            have hζ0 := norm_riemannZeta_le w hw_dom
            have hfrac : ‖w‖ / w.re ≤ 10 * ‖w‖ := norm_div_re_le_ten_mul_norm_of_mem hw_dom
            have hpoly : ‖riemannZeta w‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
              have : ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := by
                calc
                  ‖riemannZeta w‖ ≤ 1 + ‖1 / (w - 1)‖ + ‖w‖ / w.re := hζ0
                  _ ≤ 1 + ‖1 / (w - 1)‖ + 10 * ‖w‖ := by gcongr
                  _ ≤ 2 + 10 * ‖w‖ := by
                        have hw1 : w - 1 = -z := by
                          dsimp [w]
                          ring
                        have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (by norm_num) (le_of_lt hz_large)
                        have hinv_le : ‖(1 : ℂ) / (w - 1)‖ ≤ 1 := by
                          have hinv : (‖z‖ : ℝ)⁻¹ ≤ (1 : ℝ) := by
                            simpa using (inv_le_one_of_one_le₀ (a := (‖z‖ : ℝ)) hz1)
                          simpa [div_eq_mul_inv, hw1] using hinv
                        nlinarith [hinv_le]
              calc
                ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := this
                _ ≤ 2 + 10 * A := by gcongr
                _ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
                      simp [pow_two]
                      nlinarith [hA1]
            exact le_trans hpoly (Real.le_exp_self _)
          have hcoef : (2 + CΓ + 2 + 40 : ℝ) ≤ C := by
            exact reflected_zeta_coefficient_le hCΓ_pos.le (le_max_right _ _)
          have : ‖(z - 1) * riemannZeta z‖ ≤ rexp (C * A ^ (2 : ℝ)) :=
            norm_mul_riemannZeta_le_exp_of_reflected (by simp [w]) hzeta_fe hpow_le1
              hw_norm_le hA1 hA2_nonneg hΓw hcosw hζw hcoef
          simpa [hzeta_def] using this
      have hC0 : 0 ≤ C := by
        have h0 : (0 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) :=
          le_trans (by norm_num) (le_max_left _ _)
        have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by simp [C]
        exact le_trans h0 hle
      have hB0 : 0 ≤ C * A ^ (2 : ℝ) := mul_nonneg hC0 hA2_nonneg
      have hlog :
          Real.log (1 + ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖) ≤
            C * A ^ (2 : ℝ) + Real.log 2 :=
        Real.log_one_add_le_add_log_two_of_le_exp (norm_nonneg _) hB0 hmain
      have hA2_ge1 : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
        Real.one_le_rpow hA1 (by norm_num)
      calc
        Real.log (1 + ‖(DirichletCharacter.LFunctionTrivChar₁ 1) z‖)
            ≤ C * A ^ (2 : ℝ) + Real.log 2 := hlog
        _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
              have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              -- use `Real.log 2 ≤ Real.log 2 * A^2` since `A^2 ≥ 1`
              have : Real.log 2 ≤ Real.log 2 * A ^ (2 : ℝ) := by
                simpa [one_mul] using (mul_le_mul_of_nonneg_left hA2_ge1 hlog2)
              nlinarith [this]


end Complex
