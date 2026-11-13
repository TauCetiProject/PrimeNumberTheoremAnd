/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gamma bounds from the Euler integral

Pointwise bounds for `Real.Gamma` and `Complex.Gamma` used in finite-order estimates for
completed zeta functions. These follow from the Euler integral representation and convexity on
`[1, 2]`, without Binet's kernel.

## Main results

* `Real.Gamma.le_one_of_mem_Icc` : `Γ(x) ≤ 1` for `x ∈ [1, 2]`
* `Complex.Gamma.norm_le_one` : `‖Γ z‖ ≤ 1` for `1 ≤ re z ≤ 2`

## References

* [DLMF], §5.2.1 for the Euler integral representation
-/

open Real Complex Set MeasureTheory

@[expose] public section

noncomputable section

namespace Real
namespace Gamma

/-- For `x ∈ [1, 2]`, `Γ(x) ≤ 1` since `Γ(1) = Γ(2) = 1` and the function is convex. -/
theorem le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) : Gamma x ≤ 1 := by
  have hsegment : x ∈ segment ℝ (1 : ℝ) 2 := by
    simpa only [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)] using (show x ∈ Icc 1 2 from ⟨hlo, hhi⟩)
  simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using
    Real.convexOn_Gamma.le_on_segment (by norm_num) (by norm_num) hsegment

end Gamma
end Real

namespace Complex
namespace Gamma

/-- For `1 ≤ re z ≤ 2`, `‖Γ z‖ ≤ 1`. -/
theorem norm_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) : ‖Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc
    ‖Gamma z‖ ≤ Real.Gamma z.re := Complex.norm_Gamma_le_Gamma_re hz_pos
    _ ≤ 1 := Real.Gamma.le_one_of_mem_Icc hlo hhi

/-- Squared form of `Complex.norm_Gamma_le_Gamma_re`. -/
theorem norm_sq_le_Gamma_re_sq {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h := Complex.norm_Gamma_le_Gamma_re hz
  have hΓ : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
  simpa [pow_two] using mul_le_mul h h (norm_nonneg _) hΓ

/-- Squared comparison against the real-axis value at `re z`. -/
theorem norm_sq_le_norm_sq_Gamma_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_le_Gamma_re_sq hz_pos
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Gamma_ofReal z.re, norm_real]
    exact abs_of_pos (Real.Gamma_pos_of_pos hz_pos)
  rw [habs]
  exact h

end Gamma
end Complex

end
