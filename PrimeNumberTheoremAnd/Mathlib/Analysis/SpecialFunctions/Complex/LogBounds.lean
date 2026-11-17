/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Analysis.SpecialFunctions.Complex.Log.Taylor

/-!
# Logarithm estimates for Weierstrass products

This file develops the finite truncation and tail estimates for the logarithm series
`-log (1 - z)`.  These estimates are the local analytic input for bounding Weierstrass
factors and canonical products.
-/

public section

open scoped BigOperators

namespace Real

/-- If `0 ≤ r ≤ 1 / 2`, then the geometric-factor denominator is bounded by `2`. -/
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

open scoped BigOperators in
/-- On the open unit disk, `-log (1 - z)` is the `tsum` with index shift `n ↦ n + 1`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

/-- The tail `∑_{k>m} z^k / k`, as `∑' k, z^(m+1+k)/(m+1+k)`. -/
noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
    (summable_nat_add_iff (m + 1)).2 (hasSum_taylorSeries_neg_log hz).summable

/-- Decompose the logarithm series into its first `m` terms and the remaining tail. -/
lemma neg_log_one_sub_eq_neg_logTaylor_neg_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = (-logTaylor (m + 1) (-z)) + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, neg_logTaylor_succ_neg_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf


/-- A coarse geometric-series bound for the logarithm tail. This intentionally drops the
extra denominator `m + 1 + k`; the weaker estimate is the form used by the Weierstrass-factor
bounds below. -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  have htail : logTail m z = -(log (1 - z) - logTaylor (m + 1) (-z)) := by
    have h := neg_log_one_sub_eq_neg_logTaylor_neg_add_logTail hz m
    linear_combination -h
  rw [htail, norm_neg]
  have h := norm_log_sub_logTaylor_le m (z := -z) (by simpa using hz)
  simp only [norm_neg, ← sub_eq_add_neg] at h
  refine h.trans ?_
  simpa only [div_eq_mul_inv] using
    div_le_self (by positivity : 0 ≤ ‖z‖ ^ (m + 1) * (1 - ‖z‖)⁻¹)
      (by norm_num : (1 : ℝ) ≤ (m : ℝ) + 1)

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

lemma norm_logTaylor_neg_le_nat_mul_max_one_norm_pow (m : ℕ) (z : ℂ) :
    ‖logTaylor (m + 1) (-z)‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  rw [← norm_neg, neg_logTaylor_succ_neg_eq_sum]
  calc
    ‖∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)‖ ≤
        ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [norm_div, norm_pow, ← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]
      refine (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg k))).trans ?_
      calc
        ‖z‖ ^ (k + 1) ≤ max 1 ‖z‖ ^ (k + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
        _ ≤ max 1 ‖z‖ ^ m :=
          pow_le_pow_right₀ (le_max_left _ _) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))
        _ = max 1 (‖z‖ ^ m) := by
          rw [max_pow_of_nonneg zero_le_one (norm_nonneg _)]; simp
    _ = (m : ℝ) * max 1 (‖z‖ ^ m) := by simp



end Complex
