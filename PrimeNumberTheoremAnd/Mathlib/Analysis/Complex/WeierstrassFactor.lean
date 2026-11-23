/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Taylor

/-!
# Weierstrass elementary factors

Tau Ceti's Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (`Complex.weierstrassFactor`) come with their
normalization, simple zero, the sharp bound `‖E_m(z) - 1‖ ≤ ‖z‖^(m+1)` on the closed unit
disk and lower bounds for `log ‖E_m(z)‖`. This file adds the logarithmic-tail formula and locally
uniform convergence of products of scaled factors of arbitrary genus.

## Main results

* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-∑' k, z ^ (m + 1 + k) / (m + 1 + k))`
-/

public section

noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-- On `‖z‖ < 1` with `z ≠ 1`, the elementary factor is the exponential of its negative tail. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-(∑' k, z ^ (m + 1 + k) / (m + 1 + k))) := by
  let tail : ℂ := ∑' k, z ^ (m + 1 + k) / (m + 1 + k)
  rw [weierstrassFactor_def]
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + (-logTaylor (m + 1) (-z)) = -tail := by
    have hdecomp : -log (1 - z) = (-logTaylor (m + 1) (-z)) +
        tail := by
      have h := (hasSum_taylorSeries_neg_log hz).summable.sum_add_tsum_nat_add (m + 1)
      rw [(hasSum_taylorSeries_neg_log hz).tsum_eq] at h
      simpa [tail, neg_logTaylor_succ_neg_eq_sum, Finset.sum_range_succ',
        Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h.symm
    calc
      log (1 - z) + (-logTaylor (m + 1) (-z))
          = log (1 - z) + ((-logTaylor (m + 1) (-z)) + tail) - tail := by ring
      _ = log (1 - z) + (-log (1 - z)) - tail := by rw [hdecomp]
      _ = -tail := by ring
  simpa only [tail] using congrArg Complex.exp hsum

/-! ## Locally uniform convergence of products of scaled factors -/

lemma summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) := by
  have hpow : Summable (fun n : ℕ => (‖a n‖ ^ (m + 1))⁻¹) := by
    simpa only [inv_pow] using h_sum
  have ht := hpow.tendsto_atTop_of_pos (f := fun n => ‖a n‖ ^ (m + 1))
    (fun n => pow_pos (norm_pos_iff.mpr (h_nonzero n)) (m + 1))
  have hs : Summable (fun n : ℕ => 4 * ‖z‖ ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
    simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
      h_sum.mul_left (4 * ‖z‖ ^ (m + 1))
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [ht.eventually_ge_atTop ((‖z‖ * 2) ^ (m + 1))] with n hn
  have hz : ‖z‖ ≤ ‖a n‖ / 2 := (le_div_iff₀ (by norm_num)).2
    ((pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (Nat.succ_ne_zero m)).1 hn)
  have h : ‖z / a n‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ (by linarith [norm_nonneg (a n)]) (norm_nonneg (a n))
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (norm_weierstrassFactor_sub_one_le m h).trans ?_
  rw [norm_div, div_pow, mul_div_assoc]
  exact le_mul_of_one_le_left (by positivity) (by norm_num)

lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    have hza : ‖z‖ ≤ ‖a n‖ / 2 := (hR z hz).trans hn
    have h : ‖z / a n‖ ≤ 1 := by
      rw [norm_div]
      exact div_le_one_of_le₀ (by linarith [norm_nonneg (a n)]) (norm_nonneg (a n))
    calc
      ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ ‖z / a n‖ ^ (m n + 1) :=
        norm_weierstrassFactor_sub_one_le (m n) h
      _ ≤ 4 * ‖z‖ ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
        rw [norm_div, div_pow, mul_div_assoc]
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
      _ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
        have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
        refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact ((differentiable_weierstrassFactor (m n)).continuous.comp
      (continuous_id.div_const (a n))).continuousOn.fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (by
        intro R hR
        have hpow : Summable (fun n : ℕ => (‖a n‖ ^ (m + 1))⁻¹) := by
          simpa only [inv_pow] using h_sum
        have ht := hpow.tendsto_atTop_of_pos (f := fun n => ‖a n‖ ^ (m + 1))
          (fun n => pow_pos (norm_pos_iff.mpr (h_nonzero n)) (m + 1))
        filter_upwards [ht.eventually_ge_atTop ((R * 2) ^ (m + 1))] with n hn
        exact (le_div_iff₀ (by norm_num)).2
          ((pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (Nat.succ_ne_zero m)).1 hn))
      (by
        intro R _hR
        simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
          h_sum.mul_left (4 * R ^ (m + 1)))

end Complex
