/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Topology.Homotopy.PuncturedStarConvex
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelKernel
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.NumberTheory.LSeries.SumCoeff
import TauCeti.Analysis.MellinTransform.UpperTail

/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the full half-plane `{re s > 0}`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The fixed strip threshold `σ₀ = 1/10`, its domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on the full punctured right half-plane is proved by analytic
continuation from `re s > 1`, where it follows from Mathlib's partial-summation integral
`LSeries_eq_mul_integral'` and `⌊u⌋ = u - {u}`.

The kernel lives in `RiemannZetaAbelKernel`.

## Main results

* `zetaAbelContinuationDomain`, `zetaAbelContinuationFormula`
* `riemannZeta_eq_zetaAbelContinuationFormula`
* `norm_zetaAbelContinuationFormula_le`, `analyticOn_zetaAbelContinuationFormula`
-/

@[expose] public section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- Fixed positive strip threshold used for quantitative bounds from the Abel formula. -/
noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  change 0 < (1 / 10 : ℝ)
  norm_num

theorem one_sub_zetaAbelContinuationReLower :
    (1 - zetaAbelContinuationReLower : ℝ) = 9 / 10 := by
  change (1 - 1 / 10 : ℝ) = 9 / 10
  norm_num

/-- Quantitative substrip `{s : ℂ | s ≠ 1 ∧ re s > 1/10}` for uniform Abel-formula bounds. -/
def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem zetaAbelContinuationDomain_re_pos {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) :
    0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs.2

theorem mem_zetaAbelContinuationDomain_of_re {s : ℂ} (hs_ne : s ≠ 1)
    (hs_re : zetaAbelContinuationReLower < s.re) : s ∈ zetaAbelContinuationDomain :=
  ⟨hs_ne, hs_re⟩

/-- On `zetaAbelContinuationDomain`, `‖z‖ / re z ≤ 10 * ‖z‖`. -/
theorem norm_div_re_le_ten_mul_norm_of_mem {z : ℂ} (hz : z ∈ zetaAbelContinuationDomain) :
    ‖z‖ / z.re ≤ 10 * ‖z‖ := by
  rw [div_eq_mul_inv, mul_comm]
  gcongr
  calc
    z.re⁻¹ = 1 / z.re := by rw [one_div]
    _ ≤ 1 / zetaAbelContinuationReLower :=
      one_div_le_one_div_of_le zetaAbelContinuationReLower_pos (le_of_lt hz.2)
    _ = 10 := by
      change (1 / (1 / 10 : ℝ)) = 10
      norm_num

/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

theorem riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hs1 : -s + 1 ≠ 0 := fun h ↦ by simp [neg_add_eq_zero.mp h] at hs
  have hpow : (-s).re < -1 := by simpa using hs
  have hfract (u : ℝ) : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [norm_real, Real.norm_eq_abs, Int.abs_fract] using (Int.fract_lt_one u).le
  have hL : LocallyIntegrableOn (fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ)) (Ici 1) :=
    (locallyIntegrableOn_const (1 : ℝ)).mono
      measurable_fract.complex_ofReal.aestronglyMeasurable
      (Eventually.of_forall fun u ↦ by simpa only [norm_one] using hfract u)
  have hO : (fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ)) =O[atTop] fun u ↦ u ^ (0 : ℝ) :=
    .of_bound 1 (Eventually.of_forall fun u ↦ by
      simpa only [Real.rpow_zero, norm_one, one_mul] using hfract u)
  have hK : IntegrableOn (zetaAbelFractKernel s) (Ioi 1) := by
    change IntegrableOn (fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) (Ioi 1)
    simpa only [neg_add', sub_eq_add_neg] using
      TauCeti.integrableOn_mul_cpow_of_isBigO hL hO (zero_lt_one.trans hs)
  have hsum : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) :=
    Asymptotics.isBigO_of_le _ fun n ↦ by simp
  have hint : ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (-s) - zetaAbelFractKernel s t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hfl : (⌊t⌋₊ : ℂ) = t - ((Int.fract t : ℝ) : ℂ) := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor (zero_le_one.trans ht.le)]
      push_cast
      ring
    simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
      mul_one, hfl, zetaAbelFractKernel, neg_add', sub_mul]
    rw [cpow_sub _ _ ht0, cpow_one, mul_div_cancel₀ _ ht0]
  rw [← LSeries_one_eq_riemannZeta hs, LSeries_eq_mul_integral' _ zero_le_one hs hsum, hint,
    integral_sub (integrableOn_Ioi_cpow_of_lt hpow zero_lt_one) hK,
    integral_Ioi_cpow_of_lt hpow zero_lt_one, zetaAbelContinuationFormula, ofReal_one, one_cpow]
  have hs1' : s - 1 ≠ 0 := by rw [show s - 1 = -(-s + 1) by ring]; exact neg_ne_zero.mpr hs1
  field_simp
  ring

/-- The Abel formula satisfies its standard norm bound whenever the real part is positive. -/
theorem norm_zetaAbelContinuationFormula_le (s : ℂ) (hs_re : 0 < s.re) :
    ‖zetaAbelContinuationFormula s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  have hI : ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ 1 / s.re := by
    have h := TauCeti.norm_integral_mul_cpow_le_of_bound
      (g := fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ)) (C := 1) (fun u _ ↦ ?_) hs_re
    · simpa only [zetaAbelFractKernel, neg_add', sub_eq_add_neg] using h
    · simpa only [norm_real, Real.norm_eq_abs, Int.abs_fract] using (Int.fract_lt_one u).le
  have hint : ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / s.re := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hI (norm_nonneg s)
  have hsplit :
      ‖zetaAbelContinuationFormula s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
    simp only [zetaAbelContinuationFormula, one_div]
    calc
      ‖1 + (s - 1)⁻¹ - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ‖1 + (s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1 + (s - 1)⁻¹) (-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1 : ℂ) ((s - 1)⁻¹)
        · exact (norm_mul_le (-s) (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)).trans_eq
            (by rw [norm_neg])
  calc
    ‖zetaAbelContinuationFormula s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := hsplit
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := add_le_add_right hint _
    _ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by simp [one_div]

/-- The Abel continuation formula is analytic on the punctured right half-plane. -/
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula {s : ℂ | s ≠ 1 ∧ 0 < s.re} := by
  simp only [AnalyticOn, Set.mem_ofPred_eq]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  have hO : (fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ)) =O[atTop] fun u ↦ u ^ (0 : ℝ) := by
    refine .of_bound 1 (Eventually.of_forall fun u ↦ ?_)
    simpa only [Real.rpow_zero, norm_one, one_mul, norm_real, Real.norm_eq_abs,
      Int.abs_fract] using (Int.fract_lt_one u).le
  have hI := (TauCeti.differentiableOn_integral_mul_cpow_of_isBigO hO).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs_re)
  refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
    (analyticAt_id.mul ?_)
  · exact sub_ne_zero.mpr hs_ne
  · simpa only [zetaAbelFractKernel, neg_add', sub_eq_add_neg] using hI

/-- The Abel integral formula agrees with `ζ` throughout the punctured right half-plane. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs_re : 0 < s.re) (hs_ne : s ≠ 1) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  let U : Set ℂ := {z | z ≠ 1 ∧ 0 < z.re}
  have hUo : IsOpen U :=
    isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hUp : IsPreconnected U := by
    have hp : (0 : ℝ) < (1 : ℂ).re := by norm_num
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp
      (isOpen_lt continuous_const Complex.continuous_re) (1 : ℂ) hp
    have hpath : IsPathConnected ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
      isPathConnected_iff_pathConnectedSpace.mpr
        (((convex_halfSpace_re_gt 0).starConvex hp).pathConnectedSpace_diff_singleton
          (by simp [Complex.rank_real_complex]) (half_pos hr)
          ((Metric.sphere_subset_ball (half_lt_self hr)).trans hsub))
    convert hpath.isConnected.isPreconnected using 1
    ext z
    simp [U, and_comm]
  have hζ : AnalyticOnNhd ℂ riemannZeta U := by
    exact analyticOn_riemannZeta.mono (fun _ hz ↦ hz.1)
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula U := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF hUp (by norm_num [U]) hEq) ⟨hs_ne, hs_re⟩
