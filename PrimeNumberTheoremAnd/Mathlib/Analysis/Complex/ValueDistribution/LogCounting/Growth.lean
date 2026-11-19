/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Logarithmic counting from entire-function growth

Bounds on `logCounting` of the zero divisor from a logarithmic growth hypothesis on an entire
function. Used in Hadamard divisor summability and finite-order factorization.

## Main results

* `log_two_mul_massClosedBall₀_le_logCounting` :
  compare the native nonzero multiplicity sum with log-counting at twice the radius

## Tags

logarithmic counting, Jensen's formula, finite order, Hadamard factorization
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
For non-negative locally finite support, twice the ball radius gives enough log-weight to dominate
`log 2` times the mass in the ball (excluding the origin).
-/
theorem log_two_mul_massClosedBall₀_le_logCounting {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * (∑ᶠ z ∈ closedBall (0 : E) |R| \ {0}, (D z : ℝ)) ≤ logCounting D (2 * R) := by
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
      (by
        by_cases hz0 : z = 0
        · simp [hz0]
        · apply Real.log_nonneg
          rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hz0)]
          exact hn)
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
      have hlog2 : log 2 ≤ log ((2 * R) * ‖z‖⁻¹) := by
        apply Real.log_le_log (by norm_num)
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hz0)]
        exact mul_le_mul_of_nonneg_left hn (by norm_num)
      simpa only [r, mul_comm] using mul_le_mul_of_nonneg_right hlog2
        (show (0 : ℝ) ≤ (D z : ℝ) by exact_mod_cast hDnonneg z)
    · simpa only [v, ite_eq_right hz] using hw z
  have hmass : ∑ᶠ z, v z = log 2 *
      (∑ᶠ z ∈ closedBall (0 : E) |R| \ {0}, (D z : ℝ)) := by
    have hsum : (∑ᶠ z ∈ closedBall (0 : E) |R| \ {0}, (D z : ℝ)) =
        ∑ z ∈ S, (D z : ℝ) := by
      apply finsum_cond_eq_sum_of_cond_iff
      intro z hz
      have hDz : D z ≠ 0 := by exact_mod_cast hz
      simp [S, Function.mem_support, toClosedBall_apply,
        locallyFinsuppWithin.restrict_apply, hDz]
    rw [finsum_eq_sum_of_support_subset v hvsub, hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z hz ↦ by simp only [v, ite_eq_left hz]
  have hc : 0 ≤ (D 0 : ℝ) * log r :=
    mul_nonneg (by exact_mod_cast hDnonneg 0) (log_nonneg (by dsimp [r]; linarith))
  calc
    log 2 * (∑ᶠ z ∈ closedBall (0 : E) |R| \ {0}, (D z : ℝ)) = ∑ᶠ z, v z := hmass.symm
    _ ≤ ∑ᶠ z, w z := finsum_le_finsum hvfin hwfin hvw
    _ ≤ (∑ᶠ z, w z) + (D 0 : ℝ) * log r := le_add_of_nonneg_right hc
    _ = logCounting D (2 * R) := rfl


theorem massClosedBall₀_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    (∑ᶠ z ∈ closedBall (0 : ℂ) |R| \ {0},
        (divisor f Set.univ z : ℝ))
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * (∑ᶠ z ∈ closedBall (0 : ℂ) |R| \ {0},
        (divisor f Set.univ z : ℝ))
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    log_two_mul_massClosedBall₀_le_logCounting
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    have hm : Meromorphic f := fun z ↦ (hf.analyticAt z).meromorphicAt
    rw [logCounting_divisor_eq_circleAverage_sub_const hm h2R0.ne', sub_eq_add_neg]
    refine add_le_add (circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm (fun z _ ↦ hm z)) ?_) (neg_le_abs _)
    intro z hz
    exact (le_max_right 0 (log ‖f z‖)).trans ((posLog_le_log_one_add (norm_nonneg _)).trans
      ((mem_sphere_zero_iff_norm.mp hz) ▸ hC z))
  have hmul :
      (log 2) * (∑ᶠ z ∈ closedBall (0 : ℂ) |R| \ {0},
        (divisor f Set.univ z : ℝ))
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      (∑ᶠ z ∈ closedBall (0 : ℂ) |R| \ {0},
        (divisor f Set.univ z : ℝ)) * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'

end Function.locallyFinsuppWithin
