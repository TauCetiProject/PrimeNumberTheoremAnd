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
disk and lower bounds for `log ‖E_m(z)‖`. This file adds the logarithmic-tail formula.

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

end Complex
