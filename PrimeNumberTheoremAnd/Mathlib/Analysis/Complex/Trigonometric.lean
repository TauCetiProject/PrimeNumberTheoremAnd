module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Complex trigonometric bounds

Elementary exponential bounds for complex trigonometric functions.
-/

@[expose] public section

namespace Complex

/-- `‖cos z‖` is controlled by `exp |im z|`. -/
lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have hp : ‖exp (z * I)‖ ≤ Real.exp |z.im| := by
    simpa [norm_exp, mul_re] using Real.exp_le_exp.mpr (neg_le_abs z.im)
  have hn : ‖exp (-z * I)‖ ≤ Real.exp |z.im| := by
    simpa [norm_exp, mul_re] using Real.exp_le_exp.mpr (le_abs_self z.im)
  rw [cos, Complex.norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    ‖exp (z * I) + exp (-z * I)‖ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      norm_add_le_of_le hp hn
    _ = Real.exp |z.im| * 2 := by ring

end Complex
