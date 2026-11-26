module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import TauCeti.Analysis.Fourier.Inversion
import TauCeti.Analysis.MellinTransform.TruncatedInversion

/-!
# Bilateral Laplace inversion

This file collects bilateral Laplace transform infrastructure used by the
explicit-formula contour arguments.
-/

open Real Complex Set MeasureTheory Filter FourierTransform
open scoped FourierTransform Topology

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The bilateral Laplace transform on a vertical complex line. -/
def laplaceTransformBilateral (f : ℝ → E) (s : ℂ) : E :=
  ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) • f x

/-- The truncated inverse bilateral Laplace integral in the multiplication
`x^s` form used by Perron and explicit-formula arguments. -/
def laplaceIntegralCpowTrunc (f : ℝ → ℂ) (sigma x T : ℝ) : ℂ :=
  (1 / (2 * (π : ℂ))) *
    ∫ t in (-T)..T, laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I) *
      (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I)

def fourierInvTrunc (F : ℝ → E) (x T : ℝ) : E :=
  (1 / (2 * π) : ℝ) •
    ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) • F (t / (2 * π))

def laplaceInvLineTrunc (sigma : ℝ) (F : ℂ → E) (x T : ℝ) : E :=
  (1 / (2 * π) : ℝ) •
    ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
      F ((sigma : ℂ) + (t : ℂ) * I)

/-- The bilateral Laplace transform of `f` is the Mellin transform of `t ↦ f (-log t)`. -/
theorem laplaceTransformBilateral_eq_mellin (f : ℝ → E) (s : ℂ) :
    laplaceTransformBilateral f s = mellin (fun t ↦ f (-Real.log t)) s := by
  rw [laplaceTransformBilateral, mellin,
    ← integral_neg_eq_self (fun x : ℝ ↦ Complex.exp (-s * x) • f x),
    ← integral_comp_log_Ioi_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  rw [← smul_assoc, Complex.real_smul, cpow_sub _ _ (ofReal_ne_zero.2 ht.ne'), cpow_one,
    cpow_def_of_ne_zero (ofReal_ne_zero.2 ht.ne'), ← ofReal_log ht.le]
  congr 1
  push_cast
  ring_nf

/-- On a vertical line, the bilateral Laplace transform is the Fourier transform
of the exponentially weighted function (Mathlib's `mellin_eq_fourier`). -/
theorem laplaceTransformBilateral_eq_fourier (f : ℝ → E) (s : ℂ) :
    laplaceTransformBilateral f s =
      𝓕 (fun x : ℝ => Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) (s.im / (2 * π)) := by
  rw [laplaceTransformBilateral_eq_mellin, mellin_eq_fourier]
  simp_rw [Real.log_exp, neg_neg, ← Complex.coe_smul, Complex.ofReal_exp]
  push_cast
  rfl

/-- Continuity of the bilateral Laplace integral along a vertical line, under
integrability of the exponentially weighted source on that line. -/
theorem continuous_laplaceTransformBilateral_verticalLine_of_integrable
    {f : ℝ → ℂ} {sigma : ℝ}
    (hf_int : Integrable (fun y : ℝ => exp (-((sigma : ℂ) * (y : ℂ))) * f y)) :
    Continuous (fun t : ℝ => laplaceTransformBilateral f ((sigma : ℂ) - (t : ℂ) * I)) := by
  have h := (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf_int).comp
      (show Continuous (fun t : ℝ ↦ -t / (2 * Real.pi)) by fun_prop)
  change Continuous (fun t : ℝ ↦ 𝓕 (fun y : ℝ ↦
    exp (-((sigma : ℂ) * (y : ℂ))) * f y) (-t / (2 * Real.pi))) at h
  apply h.congr
  intro t
  symm
  rw [laplaceTransformBilateral_eq_fourier]
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
    sub_zero, sub_im, mul_im, zero_sub, add_zero, smul_eq_mul, neg_mul]


/-- The truncated inverse Fourier integral at height `T` is the `𝐞`-normalized truncated
inverse Fourier integral at height `T / (2π)`. -/
theorem fourierInvTrunc_eq_intervalIntegral_fourierChar (F : ℝ → E) (x T : ℝ) :
    fourierInvTrunc F x T = ∫ t in -(T / (2 * π))..T / (2 * π), 𝐞 (t * x) • F t := by
  rw [← neg_div, ← intervalIntegral.inv_smul_integral_comp_div, fourierInvTrunc, one_div]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 3
  push_cast
  field_simp

/-- Uniform finite-tail control for the damped one-sided sinc integral. -/
theorem norm_intervalIntegral_exp_neg_mul_sinc_tail_le
    {a R B : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hRB : R ≤ B) :
    ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hB_pos : 0 < B := hR_pos.trans_le hRB
  have hpos (t : ℝ) (ht : t ∈ Set.Icc R B) : 0 < t := hR_pos.trans_le ht.1
  have hanti : AntitoneOn (fun t : ℝ => Real.exp (-a * t) * t⁻¹) (Set.Icc R B) := by
    intro x hx y hy hxy
    exact mul_le_mul
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxy)]))
      (inv_anti₀ (hpos x hx) hxy) (inv_nonneg.mpr (hpos y hy).le) (Real.exp_pos _).le
  obtain ⟨c, _hc, hmean⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
      (f := fun t : ℝ => Real.exp (-a * t) * t⁻¹) (g := Real.sin) hRB
      (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hB_pos.le)) hanti
      (Real.continuous_sin.intervalIntegrable R B)
  have heq : (∫ x in R..B, Real.exp (-a * x) * Real.sinc x) =
      ∫ x in R..B, (Real.exp (-a * x) * x⁻¹) * Real.sin x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [Real.sinc_of_ne_zero (hpos x ((Set.uIcc_of_le hRB) ▸ hx)).ne']
    ring
  have hsin : ‖∫ x in R..c, Real.sin x‖ ≤ 2 := by
    rw [integral_sin]
    refine (norm_sub_le _ _).trans ?_
    simpa only [Real.norm_eq_abs, one_add_one_eq_two] using
      add_le_add (Real.abs_cos_le_one R) (Real.abs_cos_le_one c)
  have hamp : 0 ≤ Real.exp (-a * R) * R⁻¹ := by positivity
  have hexp : Real.exp (-a * R) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha.le hR_pos.le])
  rw [heq, hmean, norm_mul, Real.norm_eq_abs, abs_of_nonneg hamp]
  calc
    _ ≤ (Real.exp (-a * R) * R⁻¹) * 2 := mul_le_mul_of_nonneg_left hsin hamp
    _ ≤ R⁻¹ * 2 := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (inv_nonneg.mpr hR_pos.le) hexp) (by norm_num)
    _ ≤ 4 * R⁻¹ := by nlinarith [inv_nonneg.mpr hR_pos.le]

theorem integral_Ioi_exp_neg_mul_sin (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x = 1 / (a ^ 2 + 1) := by
  let z : ℂ := (-(a : ℂ)) + Complex.I
  have hzre : z.re < 0 := by simp [z, ha]
  have hint : Integrable (fun x : ℝ => Complex.exp (z * x)) (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im (μ := volume.restrict (Set.Ioi 0)) hint
  have hpoint : (fun x : ℝ => Real.exp (-a * x) * Real.sin x) =
      fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x
        = ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
          rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
          simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
          rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = 1 / (a ^ 2 + 1) := by
          simp [z, Complex.div_im, Complex.normSq]
          ring

/-- The exponentially damped sinc function is integrable on the positive
half-line. -/
theorem integrableOn_exp_neg_mul_sinc (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi 0) := by
  change Integrable (fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
    (volume.restrict (Set.Ioi 0))
  have h_exp : Integrable (fun x : ℝ => Real.exp (-a * x))
      (volume.restrict (Set.Ioi 0)) := by
    change IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
    simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
  refine h_exp.mono ?_ ?_
  · exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (volume.restrict (Set.Ioi 0)))
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one x)

/-- Uniform half-line tail control for the damped one-sided sinc integral. -/
theorem norm_integral_Ioi_exp_neg_mul_sinc_tail_le
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) :
    ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi R) := by
    exact (integrableOn_exp_neg_mul_sinc a ha).mono_set (Set.Ioi_subset_Ioi hR_pos.le)
  have htend :=
    intervalIntegral_tendsto_integral_Ioi
      (f := fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
      (a := R) (b := fun B : ℝ => B) hint Filter.tendsto_id
  have hnorm :
      Filter.Tendsto
        (fun B : ℝ => ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖)
        Filter.atTop
        (nhds ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖) :=
    continuous_norm.tendsto
      (∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x) |>.comp htend
  have hbound : ∀ᶠ B : ℝ in Filter.atTop,
      ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop R] with B hRB
    exact norm_intervalIntegral_exp_neg_mul_sinc_tail_le ha hR hRB
  exact le_of_tendsto hnorm hbound

/-- Positive half-line exponential tail with a variable decay constant. -/
theorem integral_Ioi_exp_neg_mul_const (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) = Real.exp (-a * x) / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith : -x < 0) a
  calc
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x)
        = ∫ u : ℝ in Set.Ioi a, Real.exp ((-x) * u) := by
          congr with u
          ring_nf
    _ = Real.exp (-a * x) / x := by
          rw [h]
          field_simp [hx.ne']

/-- The pointwise representation of the damped sinc kernel by an exponential
tail integral. -/
theorem integral_Ioi_exp_neg_mul_const_mul_sin (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x =
      Real.exp (-a * x) * Real.sinc x := by
  rw [integral_mul_const]
  rw [integral_Ioi_exp_neg_mul_const a x hx]
  rw [Real.sinc_of_ne_zero hx.ne']
  field_simp [hx.ne']

/-- Product-integrability of the damped sine kernel on `(0,∞) × (a,∞)`.
The proof integrates the `u`-tail first and bounds the inner norm by
`exp (-a*x)` using `|sin x| ≤ x` for `x > 0`. -/
theorem integrable_exp_neg_mul_sin_prod_Ioi (a : ℝ) (ha : 0 < a) :
    Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a))) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let ν := volume.restrict (Set.Ioi a)
  change Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν)
  have hsm : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν) := by
    exact (by fun_prop : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν))
  rw [integrable_prod_iff hsm]
  constructor
  · dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Integrable (fun u : ℝ => Real.exp (-u * x) * Real.sin x) ν
    have h_exp : Integrable (fun u : ℝ => Real.exp (-u * x)) ν := by
      dsimp [ν]
      change IntegrableOn (fun u : ℝ => Real.exp (-u * x)) (Set.Ioi a)
      simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) a
    exact h_exp.mul_const (Real.sin x)
  · have h_exp_a : Integrable (fun x : ℝ => Real.exp (-a * x)) μ := by
      dsimp [μ]
      change IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0)
      simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
    refine h_exp_a.mono ?_ ?_
    · exact hsm.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have h_exp_x : Integrable (fun y : ℝ => Real.exp (-y * x)) ν := by
        dsimp [ν]
        change IntegrableOn (fun y : ℝ => Real.exp (-y * x)) (Set.Ioi a)
        simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx0) a
      have h_lhs : Integrable
          (fun y : ℝ => ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖) ν := by
        simpa [Function.uncurry] using (h_exp_x.mul_const (Real.sin x)).norm
      have h_rhs : Integrable (fun y : ℝ => Real.exp (-y * x) * x) ν :=
        h_exp_x.mul_const x
      calc
        ‖∫ y : ℝ, ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν‖
            = ∫ y : ℝ, ‖Function.uncurry
                (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              exact integral_nonneg fun y => norm_nonneg _
        _ ≤ ∫ y : ℝ, Real.exp (-y * x) * x ∂ν := by
              refine integral_mono_ae h_lhs h_rhs ?_
              filter_upwards with y
              rw [Function.uncurry, Real.norm_eq_abs, abs_mul,
                abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_left
                (by simpa [abs_of_pos hx0] using (Real.abs_sin_le_abs (x := x)))
                (Real.exp_pos _).le
        _ = Real.exp (-a * x) := by
              dsimp [ν]
              rw [integral_mul_const]
              rw [integral_Ioi_exp_neg_mul_const a x hx0]
              field_simp [hx0.ne']
        _ = ‖Real.exp (-a * x)‖ := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The Laplace-regularized one-sided sinc integral. This is the Abelian input
for the classical `∫₀ᴬ sinc -> π/2` route. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ := by
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x
        = ∫ x : ℝ in Set.Ioi 0,
            ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact (integral_Ioi_exp_neg_mul_const_mul_sin a x hx).symm
    _ = ∫ u : ℝ in Set.Ioi a,
          ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x :=
          integral_integral_swap (integrable_exp_neg_mul_sin_prod_Ioi a ha)
    _ = ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact integral_Ioi_exp_neg_mul_sin u (lt_trans ha hu)
    _ = Real.arctan a⁻¹ := by
          simpa only [one_div, add_comm] using
            integral_Ioi_inv_one_add_sq.trans (Real.arctan_inv_of_pos ha).symm

/-- Abel limit of the Laplace-regularized sinc integral as the damping tends
to zero from the right. -/
theorem tendsto_integral_Ioi_exp_neg_mul_sinc_nhdsGT_zero :
    Filter.Tendsto
      (fun a : ℝ => ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) := by
  have hinv : Filter.Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have harctan : Filter.Tendsto (fun a : ℝ => Real.arctan a⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) :=
    (Real.tendsto_arctan_atTop.comp hinv).mono_right nhdsWithin_le_nhds
  refine harctan.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv a ha).symm

/-- The truncated inverse Laplace line integral of a Laplace transform is a truncated inverse
Fourier integral (Tau Ceti's `intervalIntegral_cpow_smul_mellin_eq` at `e^{-x}`). -/
theorem laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  have hx : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hcpow (z : ℂ) : (Real.exp (-x) : ℂ) ^ (-z) = Complex.exp (z * x) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hx.ne'), ← ofReal_log hx.le, Real.log_exp]
    push_cast; ring_nf
  have h := TauCeti.intervalIntegral_cpow_smul_mellin_eq (fun t ↦ f (-Real.log t)) sigma hx T
  simp_rw [hcpow, ← laplaceTransformBilateral_eq_mellin, Real.log_exp, neg_neg,
    ← Complex.coe_smul, Complex.ofReal_exp] at h
  rw [Complex.coe_smul] at h
  rw [laplaceInvLineTrunc, fourierInvTrunc_eq_intervalIntegral_fourierChar, h]
  push_cast
  simp_rw [neg_mul]

/-- Principal-value Laplace inversion reduced to the corresponding truncated
Fourier convergence theorem for the exponentially weighted source. -/
theorem laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (sigma : ℝ) (f : ℝ → E) {x : ℝ}
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (x : ℂ))) • f x))) :
    Filter.Tendsto
      (fun T : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T)
      Filter.atTop (nhds (f x)) := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  have hlim' : Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (g x)) := by
    simpa [g] using hlim
  have hscaled : Filter.Tendsto
      (fun T : ℝ =>
        Complex.exp ((sigma : ℂ) * (x : ℂ)) • fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x)) :=
    hlim'.const_smul (Complex.exp ((sigma : ℂ) * (x : ℂ)))
  have htarget : Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x = f x := by
    simp [g, ← smul_assoc, ← Complex.exp_add]
  rw [htarget] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with T
  exact (laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc sigma f x T).symm

/-- The truncated multiplication-form inverse Laplace integral is the truncated
vector-valued inverse Laplace line integral at `log x`. -/
theorem laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    laplaceIntegralCpowTrunc f sigma x T =
      laplaceInvLineTrunc sigma (laplaceTransformBilateral f) (Real.log x) T := by
  unfold laplaceIntegralCpowTrunc laplaceInvLineTrunc
  simp_rw [smul_eq_mul]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  · push_cast
    field_simp [Real.pi_ne_zero]
    rfl
  · apply intervalIntegral.integral_congr
    intro t _ht
    change laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I) =
      Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (Real.log x : ℂ)) *
        laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I)
    rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ofReal_log hx.le]
    ring_nf

/-- Principal-value Laplace inversion in the multiplication `x^s` form, reduced
to truncated Fourier convergence for the exponentially weighted source. -/
theorem laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  have hlim' : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) • f (Real.log x))) := by
    simpa [smul_eq_mul] using hlim
  have hcore := laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma f (x := Real.log x) hlim'
  refine hcore.congr' ?_
  filter_upwards with T
  exact (laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma f hx T).symm

theorem laplaceIntegralCpowTrunc_tendsto_of_sinc_kernel
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hdir : Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ,
            (2 * T * Real.sinc (T * (Real.log x - y)) : ℂ) •
              (Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  refine laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc sigma f hx (hdir.congr fun T ↦ ?_)
  rw [fourierInvTrunc_eq_intervalIntegral_fourierChar,
    hg.intervalIntegral_fourierInv_fourier_eq_integral_sinc,
    ← integral_sub_left_eq_self _ volume (Real.log x), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [sub_sub_cancel, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp

theorem laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma : ℝ) (f : ℝ → ℂ) {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (π * u) : ℂ) •
            (Complex.exp (-((sigma : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                f (Real.log x - u) -
              Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))
      volume (-R) R) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  have hq' : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ)⁻¹ •
      (Complex.exp (-((sigma : ℂ) * ((Real.log x - u : ℝ) : ℂ))) * f (Real.log x - u) -
        Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x))) volume (-R) R := by
    convert hq.const_mul (π : ℂ) using 2 with u
    by_cases hu : u = 0
    · simp [hu]
    · simp only [hu, ite_false, smul_eq_mul]
      field_simp
  refine laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc sigma f hx
    (((hg.tendsto_intervalIntegral_fourierInv_fourier hR.ne' hq').comp
      (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 * π by positivity))).congr fun T ↦ ?_)
  simp [fourierInvTrunc_eq_intervalIntegral_fourierChar]

/-- Continuity of the bilateral Laplace integral along the `σ + tI` vertical line,
under integrability of the exponentially weighted source. Companion to
`continuous_laplaceTransformBilateral_verticalLine_of_integrable` (the `σ - tI` form). -/
theorem continuous_laplaceTransformBilateral_verticalLine_add_of_integrable
    {φ : ℝ → ℂ} {σ : ℝ}
    (hφ_int : Integrable (fun y : ℝ => exp (-((σ : ℂ) * (y : ℂ))) * φ y)) :
    Continuous
      (fun t : ℝ => laplaceTransformBilateral φ ((σ : ℂ) + (t : ℂ) * I)) := by
  have h := continuous_laplaceTransformBilateral_verticalLine_of_integrable hφ_int
  convert h.comp continuous_neg using 1
  ext t
  congr 1
  simp
