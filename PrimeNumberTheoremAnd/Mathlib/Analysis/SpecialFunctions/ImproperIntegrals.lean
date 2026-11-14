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
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    exact (not_le.mpr (lt_of_lt_of_le zero_lt_one hm)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by simpa [uIcc_of_le hmn] using h0notIcc
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    exact (ne_of_gt hε) (by linarith [h])
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    simpa using integral_rpow (a := m) (b := n) (r := -1 - ε) (Or.inr ⟨hrne, h0not⟩)
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := hint
    _ = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by ring

theorem integral_interval_rpow_neg_le {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  rw [integral_interval_rpow_neg_one_sub hε hm hmn, div_eq_mul_one_div, mul_comm]
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (le_trans zero_le_one (le_trans hm hmn)) _)
