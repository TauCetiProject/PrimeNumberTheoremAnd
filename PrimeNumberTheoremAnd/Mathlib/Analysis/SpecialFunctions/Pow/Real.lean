module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-power estimates

Elementary logarithmic and real-power inequalities used in decay and growth estimates.
-/
@[expose] public section

namespace Real

/-- For `1 < u` and `ε > 0`, `log u * u^(-1-ε) ≤ (2/ε) * u^(-1-ε/2)`. -/
theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlog_bound : Real.log u ≤ (2 / ε) * u ^ (ε / 2) := by
    convert Real.log_le_rpow_div hu0.le (half_pos hε) using 1
    ring
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right hlog_bound (Real.rpow_pos_of_pos hu0 _).le
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real
