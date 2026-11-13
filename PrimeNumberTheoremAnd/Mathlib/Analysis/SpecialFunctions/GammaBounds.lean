/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Algebra.Order.Star.Real

/-!
# Bounds for `Complex.Gamma`

A bound for Gamma on a positive-real-part strip, from the native Euler comparison and recurrence.
-/

@[expose] public section

noncomputable section

open Complex Real Set Metric
open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Complex
namespace Gamma

/-- If `0 < a ≤ re w ≤ 1`, then `‖Γ(w)‖ ≤ 1 / a + √π`. -/
lemma norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  have hw_pos : 0 < w.re := ha_pos.trans_le hw
  have hw0 : w ≠ 0 := by
    intro h
    simpa only [h, Complex.zero_re, lt_self_iff_false] using hw_pos
  have hsucc : ‖Complex.Gamma (w + 1)‖ ≤ 1 :=
    Complex.Gamma.norm_le_one (by simp only [Complex.add_re, Complex.one_re]; linarith)
      (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hstrong : ‖Complex.Gamma w‖ ≤ 1 / a := by
    apply (le_div_iff₀ ha_pos).mpr
    calc
      ‖Complex.Gamma w‖ * a ≤ ‖Complex.Gamma w‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_left (hw.trans (Complex.re_le_norm w)) (norm_nonneg _)
      _ = ‖Complex.Gamma (w + 1)‖ := by rw [Complex.Gamma_add_one w hw0, norm_mul, mul_comm]
      _ ≤ 1 := hsucc
  exact hstrong.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))

end Gamma
end Complex

end
