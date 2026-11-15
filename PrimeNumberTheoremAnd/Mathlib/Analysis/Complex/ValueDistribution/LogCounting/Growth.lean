/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Logarithmic counting from entire-function growth

Bounds on `logCounting` of the zero divisor from a logarithmic growth hypothesis on an entire
function. Used in Hadamard divisor summability and finite-order factorization.

## Main results

* `Function.locallyFinsuppWithin.logCounting_divisor_le_of_log_growth` : log-growth of order `ρ`
  controls log-counting on disks
* `Function.locallyFinsuppWithin.massClosedBall₀`, `log_two_mul_massClosedBall₀_le_logCounting` :
  compare zero mass in a ball with log-counting at twice the radius

## Tags

logarithmic counting, Jensen's formula, finite order, Hadamard factorization
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

/--
A logarithmic growth bound on an entire function controls its divisor log-counting on a disk.
-/
theorem logCounting_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    logCounting_divisor_eq_circleAverage_sub_const
      (fun z ↦ (hf.analyticAt z).meromorphicAt) hR
  have hf_sphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact log_norm_le_of_log_one_add_growth_on_sphere hC hz
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt hbound_circle
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
For non-negative locally finite support, twice the ball radius gives enough log-weight to dominate
`log 2` times the mass in the ball (excluding the origin).
-/
theorem log_two_mul_massClosedBall₀_le_logCounting {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * massClosedBall₀ D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let r := 2 * R
  have hr0 : 0 < r := by dsimp [r]; positivity
  let Dr := toClosedBall r D
  let S := ((finiteSupport (toClosedBall R D)
    (isCompact_closedBall (0 : E) |R|)).toFinset).filter fun z => z ≠ (0 : E)
  let v (z : E) : ℝ := if z ∈ S then log 2 * (D z : ℝ) else 0
  let w (z : E) : ℝ := (Dr z : ℝ) * log (r * ‖z‖⁻¹)
  have hvsub : Function.support v ⊆ (S : Set E) := by
    intro z hz
    by_contra h
    exact (Function.mem_support.mp hz) (by change z ∉ S at h; simp only [v, ite_eq_right h])
  have hvfin : (Function.support v).Finite := S.finite_toSet.subset hvsub
  have hwfin : (Function.support w).Finite :=
    (finiteSupport Dr (isCompact_closedBall (0 : E) |r|)).subset (by
      intro z hz
      apply Function.mem_support.mpr
      intro h
      exact (Function.mem_support.mp hz) (by simp [w, h]))
  have hw (z : E) : 0 ≤ w z := by
    by_cases hz : Dr z = 0
    · simp [w, hz]
    have hb := Dr.supportWithinDomain (Function.mem_support.mpr hz)
    have heq : Dr z = D z := toClosedBall_eval_within D hb
    have hn : ‖z‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr0] using hb
    exact mul_nonneg (by exact_mod_cast heq ▸ hDnonneg z)
      (log_nonneg_mul_inv_norm_of_norm_le hn)
  have hvw : v ≤ w := by
    intro z
    by_cases hz : z ∈ S
    · have hz0 := (Finset.mem_filter.mp hz).2
      have hzR := (finiteSupport (toClosedBall R D)
        (isCompact_closedBall (0 : E) |R|)).mem_toFinset.mp (Finset.mem_filter.mp hz).1
      have hn : ‖z‖ ≤ R := by
        simpa only [mem_closedBall, dist_zero_right, abs_of_pos hR0] using
          (toClosedBall R D).supportWithinDomain hzR
      have hb : z ∈ closedBall (0 : E) |r| := by
        simp only [mem_closedBall, dist_zero_right, abs_of_pos hr0]
        exact hn.trans (by dsimp [r]; linarith)
      have heq : Dr z = D z := toClosedBall_eval_within D hb
      change (if z ∈ S then log 2 * (D z : ℝ) else 0) ≤ _
      rw [ite_eq_left hz]
      change log 2 * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹)
      rw [heq]
      simpa only [r, mul_comm] using mul_le_mul_of_nonneg_right
        (log_two_le_log_two_mul_mul_inv_norm_of_norm_le hz0 hn)
        (show (0 : ℝ) ≤ (D z : ℝ) by exact_mod_cast hDnonneg z)
    · simpa only [v, ite_eq_right hz] using hw z
  have hmass : ∑ᶠ z, v z = log 2 * massClosedBall₀ D R := by
    rw [finsum_eq_sum_of_support_subset v hvsub]
    change (∑ z ∈ S, v z) = log 2 * ∑ z ∈ S, (D z : ℝ)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z hz => by simp only [v, ite_eq_left hz]
  have hc : 0 ≤ (D 0 : ℝ) * log r :=
    mul_nonneg (by exact_mod_cast hDnonneg 0) (log_nonneg (by dsimp [r]; linarith))
  calc
    log 2 * massClosedBall₀ D R = ∑ᶠ z, v z := hmass.symm
    _ ≤ ∑ᶠ z, w z := finsum_le_finsum hvfin hwfin hvw
    _ ≤ (∑ᶠ z, w z) + (D 0 : ℝ) * log r := le_add_of_nonneg_right hc
    _ = logCounting D (2 * R) := rfl


theorem massClosedBall₀_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    log_two_mul_massClosedBall₀_le_logCounting
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    simpa using logCounting_divisor_le_of_log_growth (f := f) (ρ := ρ) (C := C) hf hC
      (R := 2 * R) h2R0
  have hmul :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'

end Function.locallyFinsuppWithin
