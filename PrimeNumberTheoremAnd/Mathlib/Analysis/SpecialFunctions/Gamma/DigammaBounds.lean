/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Digamma bounds on right half-plane strips

Tau Ceti's sectorial estimate compares digamma with the principal logarithm.
On a right half-plane strip the error is uniformly bounded, while the logarithm
has at most logarithmic growth in the imaginary height.
-/

@[expose] public section

open Filter Topology Finset Nat

namespace Complex

/-- Digamma is analytic on the open right half-plane. -/
theorem analyticOnNhd_digamma_re_pos : AnalyticOnNhd ℂ digamma {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hregular : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [digamma_def, logDeriv, Pi.div_def] using
    (analyticAt_Gamma hregular).deriv.div (analyticAt_Gamma hregular) (Gamma_ne_zero hregular)

/-- Digamma has logarithmic growth on every vertical strip in the right half-plane. -/
theorem exists_norm_digamma_le_log {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖digamma z‖ ≤ C * Real.log (|z.im| + 2) := by
  let D := 5 / a + |Real.log a| + Real.log (|b| + 1) + Real.pi / 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.log (|b| + 1) := Real.log_nonneg (by linarith [abs_nonneg b])
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D / Real.log 2 + 1, by positivity, fun z hza hzb => ?_⟩
  have hre : 0 < z.re := ha.trans_le hza
  have hnorm : a ≤ ‖z‖ := hza.trans (re_le_norm z)
  have hnorm0 : 0 < ‖z‖ := ha.trans_le hnorm
  have harg : |z.arg| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hre.le
  have herr : ‖digamma z - Complex.log z‖ ≤ 5 / a := by
    have h := norm_digamma_sub_log_le_of_abs_arg_le (s := z) (δ := Real.pi / 2)
      (by positivity) (by linarith [Real.pi_pos]) (by linarith [harg])
    simp only [Real.cos_pi_div_two] at h
    norm_num at h
    exact h.trans (div_le_div_of_nonneg_left (by norm_num) ha hnorm)
  have hloglo : Real.log a ≤ Real.log ‖z‖ := Real.log_le_log ha hnorm
  have hnormhi : ‖z‖ ≤ (|b| + 1) * (|z.im| + 2) := by
    have h := norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre] at h
    have hb : 0 ≤ |b| := abs_nonneg b
    have hi : 0 ≤ |z.im| := abs_nonneg z.im
    have hzb' : z.re ≤ |b| := hzb.trans (le_abs_self b)
    nlinarith [mul_nonneg hb hi]
  have hloghi : Real.log ‖z‖ ≤ Real.log (|b| + 1) + Real.log (|z.im| + 2) := by
    simpa only [Real.log_mul (by positivity : |b| + 1 ≠ 0)
      (by positivity : |z.im| + 2 ≠ 0)] using Real.log_le_log hnorm0 hnormhi
  have hL : Real.log 2 ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
  have hlogabs : |Real.log ‖z‖| ≤
      |Real.log a| + Real.log (|b| + 1) + Real.log (|z.im| + 2) := by
    apply abs_le.mpr
    constructor
    · have := neg_abs_le (Real.log a)
      linarith
    · linarith [abs_nonneg (Real.log a)]
  have hlognorm : ‖Complex.log z‖ ≤
      |Real.log a| + Real.log (|b| + 1) + Real.log (|z.im| + 2) + Real.pi / 2 := by
    have h := norm_le_abs_re_add_abs_im (Complex.log z)
    rw [Complex.log_re, Complex.log_im] at h
    linarith
  have hbound : ‖digamma z‖ ≤ D + Real.log (|z.im| + 2) := by
    have h := norm_add_le (digamma z - Complex.log z) (Complex.log z)
    rw [sub_add_cancel] at h
    dsimp [D]
    linarith
  calc
    ‖digamma z‖ ≤ D + Real.log (|z.im| + 2) := hbound
    _ ≤ (D / Real.log 2 + 1) * Real.log (|z.im| + 2) := by
      have h := mul_le_mul_of_nonneg_left hL (div_nonneg hD hlog2.le)
      have hcancel : D / Real.log 2 * Real.log 2 = D := by field_simp
      rw [hcancel] at h
      nlinarith

/-- The growth bound for `digamma (w / 2)` on vertical strips, the form consumed by
explicit-formula contour integrals. -/
theorem exists_norm_digamma_div_two_le_log {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b →
      ‖digamma (w / 2)‖ ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_digamma_le_log (a := a / 2) (b := b / 2) (by linarith)
  refine ⟨C, hC, fun w hwa hwb => ?_⟩
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hre2 : (w / 2).re = w.re / 2 := by rw [h2, div_ofReal_re]
  have him2 : (w / 2).im = w.im / 2 := by rw [h2, div_ofReal_im]
  have h := hbound (w / 2) (by rw [hre2]; linarith) (by rw [hre2]; linarith)
  refine le_trans h ?_
  have him_le : |(w / 2).im| + 2 ≤ |w.im| + 2 := by
    rw [him2, abs_div]
    have h4 : (0 : ℝ) ≤ |w.im| := abs_nonneg _
    have h5 : |(2 : ℝ)| = 2 := by norm_num
    rw [h5]
    linarith
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him_le) hC.le

end Complex
