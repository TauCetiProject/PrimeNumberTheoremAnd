module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Window error bounds for the sin-div sinc kernel

For a complex-valued function `g` with a uniform derivative bound `D`, the windowed
error term

`(if u = 0 then 0 else sin (T * u) / (π * u)) • (g (x - u) - g x)`

is controlled pointwise by `D / π`, uniformly in the height `T`, and consequently its
integral over `[-1, 1]` is bounded by `(D / π) · vol (Ioc (-1) 1)`.  These supply the
local-window hypothesis of `norm_fourierInvTrunc_le_of_windowed_sin_div_bounds`.
-/

public section

open MeasureTheory Set

/-- Pointwise bound on the sin-div windowed error term: scaling by the normalized sinc
kernel and a mean-value estimate on `g (x - u) - g x` gives a bound `D / π` that is
independent of the height `T`. -/
theorem sin_div_error_pointwise_bound
    {g : ℝ → ℂ} {D x T u : ℝ}
    (hgdiff : Differentiable ℝ g)
    (hderiv : ∀ y : ℝ, ‖deriv g y‖ ≤ D) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
        (g (x - u) - g x)‖ ≤ D / Real.pi := by
  have hD : 0 ≤ D := (norm_nonneg (deriv g 0)).trans (hderiv 0)
  by_cases hu : u = 0
  · simp [hu, div_nonneg hD Real.pi_pos.le]
  · rw [ite_eq_right hu, norm_smul]
    have hscalar :
        ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 1 / (Real.pi * |u|) := by
      simpa only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos] using
        div_le_div_of_nonneg_right (Real.abs_sin_le_one (T * u))
          (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    have hdiff : ‖g (x - u) - g x‖ ≤ D * |u| := by
      simpa only [sub_sub_cancel_left, norm_neg, Real.norm_eq_abs] using
        (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (fun y _ ↦ hgdiff y) (fun y _ ↦ hderiv y)
          (x := x) (y := x - u) (Set.mem_univ _) (Set.mem_univ _)
    have hupper_nonneg : 0 ≤ 1 / (Real.pi * |u|) := by positivity
    calc
      ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ * ‖g (x - u) - g x‖
          ≤ (1 / (Real.pi * |u|)) * (D * |u|) := by
            exact mul_le_mul hscalar hdiff (norm_nonneg _) hupper_nonneg
      _ = D / Real.pi := by
            field_simp [Real.pi_ne_zero, abs_pos.mpr hu]
