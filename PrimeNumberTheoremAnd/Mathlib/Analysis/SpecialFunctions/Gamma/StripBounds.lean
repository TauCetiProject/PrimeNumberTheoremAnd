/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.HalfPlane
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite-order bound for the archimedean Gamma factor

A finite-order bound for Deligne's real Gamma factor `Complex.Gammaℝ` on the closed right
half-plane outside the unit disk. The Stirling-type input is Tau Ceti's
`Complex.exists_norm_Gamma_mul_le_exp_mul_log`, combined with `Complex.norm_Gammaℝ`.
-/

@[expose] public section

noncomputable section

namespace Complex.Gammaℝ.Stirling

/-- Finite order bound for Γ_ℝ. -/
theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := Complex.exists_norm_Gamma_mul_le_exp_mul_log (c := 1 / 2) (by norm_num)
  refine ⟨C + 1, 2, by linarith, by norm_num, fun s hs_re hs_norm ↦ ?_⟩
  rw [Complex.norm_Gammaℝ, show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    ((hC s hs_re hs_norm).trans (Real.exp_le_exp.mpr ?_))
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hlog : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖s‖)
  have h := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC_pos.le (norm_nonneg s))
  rw [Real.rpow_two]
  nlinarith only [h, sq_nonneg ‖s‖]

end Complex.Gammaℝ.Stirling
