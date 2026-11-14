/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Improper-integral estimates

Power-integral evaluations and bounds on finite intervals.
-/

@[expose] public section

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem integral_interval_rpow_neg_one_sub {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · rw [show (-1 - ε) + 1 = -ε by ring]
    ring
  · simpa [uIcc_of_le hmn] using
      (show ¬(m ≤ 0 ∧ 0 ≤ n) by rintro ⟨h, _⟩; linarith)

theorem integral_interval_rpow_neg_le {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  rw [integral_interval_rpow_neg_one_sub hε hm hmn, div_eq_mul_one_div, mul_comm]
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (le_trans zero_le_one (le_trans hm hmn)) _)
