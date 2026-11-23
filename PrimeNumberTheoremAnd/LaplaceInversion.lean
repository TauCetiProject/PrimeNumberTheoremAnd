module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Fourier.RiemannLebesgue
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral

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

/-- On a vertical line, the bilateral Laplace transform is the Fourier transform
of the exponentially weighted function. -/
theorem laplaceTransformBilateral_eq_fourier (f : ℝ → E) (s : ℂ) :
    laplaceTransformBilateral f s =
      𝓕 (fun x : ℝ => Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) (s.im / (2 * π)) := by
  calc
    laplaceTransformBilateral f s
      = ∫ x : ℝ, Complex.exp (-(s.im : ℂ) * (x : ℂ) * I) •
          (Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) := by
        unfold laplaceTransformBilateral
        congr
        ext x
        conv => lhs; rw [← re_add_im s]
        rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
        norm_cast
        push_cast
        ring_nf
    _ = 𝓕 (fun x : ℝ => Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) (s.im / (2 * π)) := by
      rw [Real.fourier_eq']
      congr
      ext x
      congr 1
      have h2pi : (2 * (π : ℝ) : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
      rw [Real.inner_apply]
      push_cast
      field_simp [h2pi]

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


theorem fourierInvTrunc_fourier_eq_integral_integral
    (f : ℝ → E) (x T : ℝ) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ t in (-T)..T,
          ∫ y : ℝ, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y := by
  unfold fourierInvTrunc
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro t _ht
  change Complex.exp (((t * x : ℝ) : ℂ) * I) • 𝓕 f (t / (2 * π)) =
    ∫ y : ℝ, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← MeasureTheory.integral_smul]
  congr with y
  rw [← smul_assoc]
  congr 1
  rw [smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- The truncated oscillatory Fourier kernel is product-integrable when the
source is integrable. This is the finite-height Fubini input for principal-value
inversion. -/
theorem integrable_truncated_fourier_kernel_prod
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun z : ℝ × ℝ => Complex.exp (((z.1 * (x - z.2) : ℝ) : ℂ) * I) • f z.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℂ))
      (volume.restrict (Set.Ioc (-T) T)) := by
    exact MeasureTheory.integrable_const (1 : ℂ)
  have hprod := hconst.smul_prod hf
  refine hprod.mono ?_ ?_
  · exact (by fun_prop : Continuous
        (fun z : ℝ × ℝ => Complex.exp (((z.1 * (x - z.2) : ℝ) : ℂ) * I)))
        |>.aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_snd
  · filter_upwards with z
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp

/-- Fubini swaps the finite-height inverse Fourier integral into the standard
Dirichlet-kernel form. The hypothesis `0 ≤ T` is the only orientation condition
needed for the interval integral. -/
theorem fourierInvTrunc_fourier_eq_integral_kernel
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) (hT : 0 ≤ T) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ y : ℝ,
          ∫ t in (-T)..T, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y := by
  rw [fourierInvTrunc_fourier_eq_integral_integral]
  congr 1
  have hle : -T ≤ T := by linarith
  rw [intervalIntegral.integral_of_le hle]
  rw [MeasureTheory.integral_integral_swap
    (integrable_truncated_fourier_kernel_prod (E := E) hf x T)]
  congr with y
  rw [← intervalIntegral.integral_of_le hle]

/-- Scaled finite-height exponential integral, written with the normalized
`sinc` kernel and no removable-singularity case split. -/
theorem integral_exp_mul_I_scaled_sinc (a T : ℝ) :
    ∫ t in (-T)..T, Complex.exp (((t * a : ℝ) : ℂ) * I) =
      (2 * T * Real.sinc (T * a) : ℂ) := by
  by_cases ha : a = 0
  · subst a
    simp
    ring
  · rw [intervalIntegral.integral_comp_mul_right (fun t : ℝ => Complex.exp ((t : ℂ) * I)) ha]
    rw [neg_mul, integral_exp_mul_I_eq_sinc]
    simp only [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha]

theorem fourierInvTrunc_fourier_eq_sinc_kernel
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) (x T : ℝ) (hT : 0 ≤ T) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y := by
  rw [fourierInvTrunc_fourier_eq_integral_kernel hf x T hT]
  congr 1
  congr with y
  rw [intervalIntegral.integral_smul_const]
  rw [integral_exp_mul_I_scaled_sinc]

theorem fourierInvTrunc_tendsto_of_sinc_kernel
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x : ℝ}
    (hdir : Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 f) x T)
      Filter.atTop (nhds (f x)) := by
  refine hdir.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (fourierInvTrunc_fourier_eq_sinc_kernel hf x T hT).symm

/-- The normalized sinc kernel integral in translated coordinates, with the
removable singularity of `sin (T * u) / (π * u)` exposed. -/
theorem normalized_sinc_kernel_integral_comp_sub_left_sin_div
    (f : ℝ → E) (x T : ℝ) :
    (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y =
      ∫ u : ℝ,
        (if u = 0 then (T / π : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u) := by
  have htranslate :
      (∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y) =
        ∫ u : ℝ, (2 * T * Real.sinc (T * u) : ℂ) • f (x - u) := by
    let g : ℝ → E := fun u => (2 * T * Real.sinc (T * u) : ℂ) • f (x - u)
    have h := integral_sub_left_eq_self g volume x
    simpa [g] using h
  rw [htranslate]
  rw [← integral_smul]
  congr with u
  rw [← smul_assoc, RCLike.real_smul_eq_coe_mul]
  congr 1
  by_cases hu : u = 0 <;>
    by_cases hT : T = 0 <;>
    simp [Real.sinc, hu, hT] <;>
    field_simp [hu, hT, Real.pi_ne_zero]

/-- The value assigned at the removable singularity of `sin (T * u) / (π * u)`
does not affect the whole-line kernel integral. -/
theorem normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae
    (f : ℝ → E) (x T : ℝ) :
    (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y =
      ∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u) := by
  rw [normalized_sinc_kernel_integral_comp_sub_left_sin_div]
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by simp [ae_iff, measure_singleton]] with u hu
  rw [ite_eq_right hu, ite_eq_right hu]

/-- Differentiability at the target point makes the local sine-error quotient
interval-integrable on every positive window. -/
theorem intervalIntegrable_local_quotient_of_differentiableAt
    {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hf_cont : ContinuousOn f (Set.Icc (x - R) (x + R)))
    (hf_diff : DifferentiableAt ℝ f x) :
    IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R := by
  let qds : ℝ → E := fun u => (-1 / π : ℂ) • dslope f x (x - u)
  have hmem : Set.Icc (x - R) (x + R) ∈ nhds x := by
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hds : ContinuousOn (dslope f x) (Set.Icc (x - R) (x + R)) :=
    (continuousOn_dslope hmem).2 ⟨hf_cont, hf_diff⟩
  have hmap : MapsTo (fun u : ℝ => x - u) (Set.Icc (-R) R) (Set.Icc (x - R) (x + R)) := by
    intro u hu
    rw [Set.mem_Icc] at hu ⊢
    constructor <;> linarith
  have hcomp : ContinuousOn (fun u : ℝ => dslope f x (x - u)) (Set.Icc (-R) R) := by
    exact hds.comp (by fun_prop) hmap
  have hqds_cont : ContinuousOn qds (Set.Icc (-R) R) :=
    hcomp.const_smul (-1 / π : ℂ)
  have hle : -R ≤ R := by linarith
  have hqds_int : IntervalIntegrable qds volume (-R) R :=
    ContinuousOn.intervalIntegrable_of_Icc hle hqds_cont
  refine hqds_int.congr_ae ?_
  rw [Filter.EventuallyEq]
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by simp [ae_iff, measure_singleton]]
    with u hu _hu_mem
  dsimp [qds]
  have hne : x - u ≠ x := by grind
  rw [ite_eq_right hu, dslope_of_ne f hne, slope_def_module,
    show x - u - x = -u by ring,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E), smul_smul]
  congr 1
  push_cast
  field_simp [hu, Real.pi_ne_zero]
  rfl

/-- Local quotient integrability gives interval-integrability of the finite
sine-kernel error term. -/
theorem intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
    {f : ℝ → E} {x R : ℝ}
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R)
    (T : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x))
      volume (-R) R := by
  let q : ℝ → E := fun u =>
    if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)
  have hsinq : IntervalIntegrable (fun u : ℝ => (Real.sin (T * u) : ℂ) • q u)
      volume (-R) R := by
    refine hq.continuousOn_smul ?_
    fun_prop
  refine hsinq.congr ?_
  intro u _hu
  dsimp [q]
  symm
  by_cases hu : u = 0
  · simp [hu]
  · simp only [ite_eq_right hu, div_eq_mul_inv, one_mul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E), smul_smul]
    rfl

/-- Local quotient integrability gives the finite-window Riemann-Lebesgue
cancellation for the sine-kernel error term. -/
theorem tendsto_intervalIntegral_sin_div_kernel_error_of_intervalIntegrable_quotient
    {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0) := by
  let q : ℝ → E := fun u =>
    if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)
  let qWindow : ℝ → E := Set.Ioc (-R) R |>.indicator q
  have hle : -R ≤ R := by linarith
  have hqIoc : IntegrableOn q (Set.Ioc (-R) R) := by
    simpa [q] using (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hq
  have hqWindow : Integrable qWindow := by
    exact hqIoc.integrable_indicator measurableSet_Ioc
  have hlim : Filter.Tendsto
      (fun T : ℝ => ∫ v : ℝ, (Real.sin (T * v) : ℂ) • qWindow v)
      Filter.atTop (nhds 0) := by
    refine (hqWindow.tendsto_integral_sin_smul_atTop.comp
      ((tendsto_div_const_atTop_of_pos (by positivity : (0 : ℝ) < 2 * π)).2 tendsto_id)).congr
      fun T ↦ ?_
    have hT : 2 * π * (T / (2 * π)) = T := by field_simp
    simp only [Function.comp_apply, id, hT]
  refine hlim.congr' ?_
  filter_upwards with T
  have hinterval :
      (∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x)) =
        ∫ u in (-R)..R, (Real.sin (T * u) : ℂ) • q u := by
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp [q]
    by_cases hu : u = 0
    · simp [hu]
    · simp only [ite_eq_right hu, div_eq_mul_inv, one_mul]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E), smul_smul]
      rfl
  rw [hinterval, intervalIntegral.integral_of_le hle]
  dsimp [qWindow]
  rw [← integral_indicator measurableSet_Ioc]
  congr with u
  by_cases hu : u ∈ Set.Ioc (-R) R
  · simp [Set.indicator_of_mem hu]
  · simp [Set.indicator_of_notMem hu]

/-- The removable sine kernel is bounded by its height. -/
theorem norm_sin_div_kernel_le_abs_height (T u : ℝ) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))‖ ≤
      |T| / π := by
  by_cases hu : u = 0
  · rw [ite_eq_left hu]
    simpa using (div_nonneg (abs_nonneg T) Real.pi_pos.le)
  · rw [ite_eq_right hu]
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs]
    have hsin : |Real.sin (T * u)| ≤ |T| * |u| := by
      simpa [abs_mul] using (Real.abs_sin_le_abs (x := T * u))
    calc
      |Real.sin (T * u)| / (|π| * |u|)
          ≤ (|T| * |u|) / (|π| * |u|) :=
            div_le_div_of_nonneg_right hsin
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |T| / π := by
        rw [abs_of_pos Real.pi_pos]
        field_simp [abs_pos.mpr hu, Real.pi_ne_zero]

/-- The sine kernel times an integrable source remains integrable. -/
theorem integrable_sin_div_kernel_smul_of_integrable
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) := by
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  let C : ℂ := (|T| / π : ℝ)
  have hC_nonneg : 0 ≤ |T| / π := div_nonneg (abs_nonneg T) Real.pi_pos.le
  have hboundInt : Integrable (fun u : ℝ => C • f (x - u)) := hfx.smul C
  refine hboundInt.mono ?_ ?_
  · have hscalar_meas : Measurable
        (fun u : ℝ =>
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) := by
      refine Measurable.ite measurableSet_eq measurable_const ?_
      fun_prop
    exact hscalar_meas.aestronglyMeasurable.smul hfx.aestronglyMeasurable
  · filter_upwards with u
    rw [norm_smul, norm_smul]
    have hCnorm : ‖C‖ = |T| / π := by
      rw [show C = ((|T| / π : ℝ) : ℂ) by rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC_nonneg]
    rw [hCnorm]
    exact mul_le_mul (norm_sin_div_kernel_le_abs_height T u) le_rfl
      (norm_nonneg _) hC_nonneg

/-- The fixed-window tail quotient is bounded by an integrable translate. -/
lemma norm_tail_quotient_le
    {f : ℝ → E} (x : ℝ) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖(Set.Ioc (-R) R)ᶜ.indicator
        (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
          f (x - u)) u‖ ≤
      (1 / (π * R)) * ‖f (x - u)‖ := by
  by_cases huSet : u ∈ (Set.Ioc (-R) R)ᶜ
  · rw [Set.indicator_of_mem huSet]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using huSet
    have hR_abs : R ≤ |u| := by
      by_contra h
      have hu' : |u| < R := lt_of_not_ge h
      exact hu_not ⟨(abs_lt.mp hu').1, (abs_lt.mp hu').2.le⟩
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := by
        exact ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [ite_eq_right hu_ne, norm_smul]
    have hscalar : ‖(1 / (π * u) : ℂ)‖ ≤ 1 / (π * R) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs, one_div]
      rw [abs_of_pos Real.pi_pos]
      have hden : π * R ≤ π * |u| :=
        mul_le_mul_of_nonneg_left hR_abs Real.pi_pos.le
      have hden_pos : 0 < π * R := mul_pos Real.pi_pos hR
      simpa [mul_comm, mul_left_comm, mul_assoc] using inv_anti₀ hden_pos hden
    exact mul_le_mul hscalar le_rfl (norm_nonneg _)
      (div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le)
  · rw [Set.indicator_of_notMem huSet]
    simpa using mul_nonneg (div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le)
      (norm_nonneg (f (x - u)))

/-- The fixed-window tail quotient is integrable for every integrable source. -/
theorem integrable_tail_quotient_of_integrable
    {f : ℝ → E} (hf : Integrable f) (x : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable ((Set.Ioc (-R) R)ᶜ.indicator
      (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
        f (x - u))) := by
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  let C : ℂ := (1 / (π * R) : ℝ)
  have hC_nonneg : 0 ≤ 1 / (π * R) :=
    div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le
  have hboundInt : Integrable (fun u : ℝ => C • f (x - u)) := hfx.smul C
  refine hboundInt.mono ?_ ?_
  · have hscalar_meas : Measurable
        (fun u : ℝ => if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) := by
      refine Measurable.ite measurableSet_eq measurable_const ?_
      fun_prop
    exact (hscalar_meas.aestronglyMeasurable.smul hfx.aestronglyMeasurable).indicator
      measurableSet_Ioc.compl
  · filter_upwards with u
    rw [norm_smul]
    have hCnorm : ‖C‖ = 1 / (π * R) := by
      rw [show C = ((1 / (π * R) : ℝ) : ℂ) by rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC_nonneg]
    rw [hCnorm]
    exact norm_tail_quotient_le (E := E) x hR u

/-- The fixed-window tail of the sine kernel tends to zero for integrable
sources. -/
theorem tendsto_sin_div_kernel_tail_of_integrable
    {f : ℝ → E} (hf : Integrable f) {x R : ℝ} (hR : 0 < R) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0) := by
  let qTail : ℝ → E := (Set.Ioc (-R) R)ᶜ.indicator
    (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
      f (x - u))
  have hqTail : Integrable qTail := by
    simpa [qTail] using integrable_tail_quotient_of_integrable (E := E) hf x hR
  have hlim : Filter.Tendsto
      (fun T : ℝ => ∫ v : ℝ, (Real.sin (T * v) : ℂ) • qTail v)
      Filter.atTop (nhds 0) := by
    refine (hqTail.tendsto_integral_sin_smul_atTop.comp
      ((tendsto_div_const_atTop_of_pos (by positivity : (0 : ℝ) < 2 * π)).2 tendsto_id)).congr
      fun T ↦ ?_
    have hT : 2 * π * (T / (2 * π)) = T := by field_simp
    simp only [Function.comp_apply, id, hT]
  refine hlim.congr' ?_
  filter_upwards with T
  let k : ℝ → E := fun u =>
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f (x - u)
  have hk : Integrable k :=
    integrable_sin_div_kernel_smul_of_integrable (E := E) hf x T
  have hle : -R ≤ R := by linarith
  symm
  calc
    (∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) -
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)
        = ∫ u in (Set.Ioc (-R) R)ᶜ, k u := by
          rw [intervalIntegral.integral_of_le hle]
          have hdecomp := integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hk
          dsimp [k] at hdecomp
          rw [← hdecomp]
          abel
    _ = ∫ u : ℝ, (Set.Ioc (-R) R)ᶜ.indicator k u := by
          rw [integral_indicator measurableSet_Ioc.compl]
    _ = ∫ u : ℝ, (Real.sin (T * u) : ℂ) • qTail u := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp [k, qTail]
          by_cases hs : u ∈ (Set.Ioc (-R) R)ᶜ
          · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
            by_cases hu : u = 0
            · simp [hu]
            · simp only [ite_eq_right hu, div_eq_mul_inv, one_mul]
              rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E), smul_smul]
              rfl
          · simp only [Set.indicator_of_notMem hs, smul_zero]

/-- Uniform fixed-window tail bound for the sine kernel. Outside `(-R, R]`,
the denominator gives a `1 / (π R)` bound, independent of the height and
translation. -/
theorem norm_sin_div_kernel_tail_le_integral_norm
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖(∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) -
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)‖ ≤
      (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
  let k : ℝ → E := fun u =>
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f (x - u)
  have hk : Integrable k :=
    integrable_sin_div_kernel_smul_of_integrable (E := E) hf x T
  have hle : -R ≤ R := by linarith
  have htail_eq :
      (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u) =
        ∫ u in (Set.Ioc (-R) R)ᶜ, k u := by
    rw [intervalIntegral.integral_of_le hle]
    have hdecomp := integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hk
    dsimp [k] at hdecomp
    rw [← hdecomp]
    abel
  rw [htail_eq]
  let C : ℝ := 1 / (π * R)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  have hbound_int : Integrable (fun u : ℝ => C * ‖f (x - u)‖) :=
    hfx.norm.const_mul C
  have hmono : ∀ᵐ u ∂(volume.restrict (Set.Ioc (-R) R)ᶜ),
      ‖k u‖ ≤ C * ‖f (x - u)‖ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc.compl] with u hucomp
    dsimp [k, C]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using hucomp
    have hR_abs : R ≤ |u| := by
      by_contra h
      have hu' : |u| < R := lt_of_not_ge h
      exact hu_not ⟨(abs_lt.mp hu').1, (abs_lt.mp hu').2.le⟩
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [ite_eq_right hu_ne, norm_smul]
    have hscalar : ‖(Real.sin (T * u) / (π * u) : ℂ)‖ ≤ C := by
      dsimp [C]
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one (T * u)
      have hden : π * R ≤ π * |u| :=
        mul_le_mul_of_nonneg_left hR_abs Real.pi_pos.le
      have hden_pos : 0 < π * R := mul_pos Real.pi_pos hR
      calc
        |Real.sin (T * u)| / (π * |u|) ≤ 1 / (π * |u|) := by
          exact div_le_div_of_nonneg_right hsin
            (mul_nonneg Real.pi_pos.le (abs_nonneg u))
        _ ≤ 1 / (π * R) := by
          simpa [one_div] using inv_anti₀ hden_pos hden
    exact mul_le_mul hscalar le_rfl (norm_nonneg _) hC_nonneg
  have hnorm_le : ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖ ≤
      ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
    calc
      ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖
          ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, ‖k u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
        exact integral_mono_ae (hk.norm.mono_measure Measure.restrict_le_self)
          (hbound_int.mono_measure Measure.restrict_le_self) hmono
  have hset_le : (∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖) ≤
      ∫ u : ℝ, C * ‖f (x - u)‖ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _u => mul_nonneg hC_nonneg (norm_nonneg _)) hbound_int
  have htranslate : (∫ u : ℝ, C * ‖f (x - u)‖) = C * ∫ u : ℝ, ‖f u‖ := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun u : ℝ => ‖f u‖) volume x]
  exact hnorm_le.trans (hset_le.trans_eq htranslate)

/-- Finite symmetric-window split for the `sin (T * u) / (π * u)` kernel.
This is the valid algebraic surface for the principal-value mass term before
taking an improper limit. -/
theorem intervalIntegral_sin_div_kernel_split
    [CompleteSpace E]
    (f : ℝ → E) (x T R : ℝ)
    (hconst : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      volume (-R) R)
    (herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x))
      volume (-R) R) :
    (∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) =
      (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
  calc
    (∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u))
        = ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          change
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                f (x - u) =
              (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
                (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                  (f (x - u) - f x)
          rw [show f (x - u) = f x + (f (x - u) - f x) by abel]
          rw [smul_add]
          congr 1
          abel_nf
    _ = (∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x) +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
          rw [intervalIntegral.integral_add hconst herr]
    _ = (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
          rw [intervalIntegral.integral_smul_const]

/-- Scaling reduces the finite-window mass of `sin (T * u) / (π * u)` to the
normalized symmetric sine integral at height `T * R`. -/
theorem intervalIntegral_sin_div_kernel_scalar_mass_eq_scaled (T R : ℝ) :
    (∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) =
      (1 / (π : ℂ)) *
        ∫ v in (T * (-R))..(T * R),
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
  let g : ℝ → ℂ := fun v => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)
  have hpoint : (fun u : ℝ =>
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) =
      fun u : ℝ => (1 / (π : ℂ)) * (T • g (T * u)) := by
    funext u
    by_cases hT : T = 0
    · simp [hT, g]
    by_cases hu : u = 0
    · simp [hu, g]
    have hTu : T * u ≠ 0 := mul_ne_zero hT hu
    simp [g, hu, hTu]
    field_simp [Real.pi_ne_zero, hT, hu]
  calc
    (∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
        = ∫ u in (-R)..R, (1 / (π : ℂ)) * (T • g (T * u)) := by
          rw [hpoint]
    _ = (1 / (π : ℂ)) * ∫ u in (-R)..R, T • g (T * u) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (1 / (π : ℂ)) * (T • ∫ u in (-R)..R, g (T * u)) := by
          rw [intervalIntegral.integral_smul]
    _ = (1 / (π : ℂ)) * ∫ v in (T * (-R))..(T * R), g v := by
          rw [intervalIntegral.smul_integral_comp_mul_left]
    _ = (1 / (π : ℂ)) *
        ∫ v in (T * (-R))..(T * R),
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
          rfl

/-- Windowed bound for finite-height Fourier inversion. The mass term, local
principal-value window, and far-field tail are separated so applications can
supply uniform bounds for the first two and use the built-in tail estimate. -/
theorem norm_fourierInvTrunc_le_of_windowed_sin_div_bounds
    [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) {x T R B L M : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R)
    (hfx : ‖f x‖ ≤ B)
    (hmass : ‖∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)‖ ≤ M)
    (herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x)) volume (-R) R)
    (hlocal : ‖∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x)‖ ≤ L) :
    ‖fourierInvTrunc (𝓕 f) x T‖ ≤
      M * B + L + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
  let K : ℝ → ℂ := fun u =>
    if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)
  have hwhole : fourierInvTrunc (𝓕 f) x T = ∫ u : ℝ, K u • f (x - u) := by
    rw [fourierInvTrunc_fourier_eq_sinc_kernel (E := E) hf x T hT]
    simpa [K] using normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae (E := E) f x T
  have hconst : IntervalIntegrable (fun u : ℝ => K u • f x) volume (-R) R := by
    let g : ℝ → E := fun u ↦ ((T / π * Real.sinc (T * u) : ℝ) : ℂ) • f x
    refine ((show Continuous g by fun_prop).intervalIntegrable (-R) R).congr_ae ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by simp [ae_iff, measure_singleton]] with u hu
    by_cases hT0 : T = 0
    · simp [g, K, hT0]
    · simp [g, K, hu, Real.sinc_of_ne_zero (mul_ne_zero hT0 hu)]
      field_simp [Real.pi_ne_zero, hT0, hu]
  have hsplit := intervalIntegral_sin_div_kernel_split (E := E) f x T R hconst
    (by simpa [K] using herr)
  have hwindow_bound : ‖∫ u in (-R)..R, K u • f (x - u)‖ ≤ M * B + L := by
    calc
      ‖∫ u in (-R)..R, K u • f (x - u)‖
          = ‖(∫ u in (-R)..R, K u) • f x +
              ∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := by
            rw [show (∫ u in (-R)..R, K u • f (x - u)) =
                (∫ u in (-R)..R, K u) • f x +
                ∫ u in (-R)..R, K u • (f (x - u) - f x) by simpa [K] using hsplit]
      _ ≤ ‖(∫ u in (-R)..R, K u) • f x‖ +
            ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := norm_add_le _ _
      _ ≤ M * B + L := by
        have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) hmass
        have hterm : ‖(∫ u in (-R)..R, K u) • f x‖ ≤ M * B := by
          rw [norm_smul]
          exact mul_le_mul (by simpa [K] using hmass) hfx (norm_nonneg _) hM_nonneg
        have hloc : ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ ≤ L := by
          simpa [K] using hlocal
        linarith
  have htail := norm_sin_div_kernel_tail_le_integral_norm (E := E) hf x T hR
  rw [hwhole]
  let W : E := ∫ u in (-R)..R, K u • f (x - u)
  let Tail : E := (∫ u : ℝ, K u • f (x - u)) - W
  have hdecomp : (∫ u : ℝ, K u • f (x - u)) = W + Tail := by
    dsimp [W, Tail]
    abel
  calc
    ‖∫ u : ℝ, K u • f (x - u)‖ = ‖W + Tail‖ := by rw [hdecomp]
    _ ≤ ‖W‖ + ‖Tail‖ := norm_add_le _ _
    _ ≤ (M * B + L) + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
      have hW : ‖W‖ ≤ M * B + L := by simpa [W] using hwindow_bound
      have hTail : ‖Tail‖ ≤ (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
        dsimp [Tail, W, K]
        simpa [K] using htail
      linarith
    _ = M * B + L + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by ring

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

/-- Scalar finite-window mass of the principal-value sine kernel. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  have h := ((Complex.continuous_ofReal.tendsto _).comp
    ((TauCeti.Contour.tendsto_integral_sin_mul_div_neg_self_atTop one_pos).comp
      (tendsto_id.atTop_mul_const hR))).const_mul (1 / (π : ℂ))
  rw [one_div_mul_cancel (by exact_mod_cast Real.pi_ne_zero)] at h
  refine h.congr fun T => ?_
  simp only [Function.comp_apply, id, one_mul]
  rw [intervalIntegral_sin_div_kernel_scalar_mass_eq_scaled, mul_neg,
    ← intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_congr fun v _ => ?_
  by_cases hv : v = 0 <;> simp [hv]

/-- The scalar finite-window sine-kernel mass is eventually bounded by `2`. -/
theorem eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ T in Filter.atTop,
      ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 2 := by
  have hlim := tendsto_intervalIntegral_sin_div_kernel_scalar_mass hR
  have hnear : ∀ᶠ T in Filter.atTop,
      dist (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) (1 : ℂ) < 1 :=
    hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)
  filter_upwards [hnear] with T hT
  have hnorm_sub : ‖(∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
        (1 : ℂ)‖ < 1 := by
    simpa [dist_eq_norm] using hT
  calc
    ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖
        = ‖(1 : ℂ) + ((∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
            (1 : ℂ))‖ := by
          congr 1
          abel
    _ ≤ ‖(1 : ℂ)‖ + ‖(∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
            (1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by
      norm_num at hnorm_sub ⊢
      linarith

/-- Windowed principal-value convergence for the sinc kernel. This avoids
treating the non-integrable constant kernel mass as a whole-line Bochner
integral: the remaining analytic work is split into a finite-window mass limit,
a finite-window local error limit, and a tail-control limit. -/
theorem sinc_kernel_tendsto_of_windowed_pv
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ}
    (hconst : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
        volume (-R) R)
    (herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R)
    (hmass : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      Filter.atTop (nhds (f x)))
    (herror : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have hsplit : (fun T : ℝ =>
      ∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) =ᶠ[Filter.atTop]
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x)) := by
    filter_upwards [hconst, herrInt] with T hconstT herrT
    exact intervalIntegral_sin_div_kernel_split (E := E) f x T R hconstT herrT
  have hwindowSum : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x))
      Filter.atTop (nhds (f x)) := by
    simpa using hmass.add herror
  have hwindow : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u))
      Filter.atTop (nhds (f x)) := by
    exact hwindowSum.congr' hsplit.symm
  have hwhole : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u))
      Filter.atTop (nhds (f x)) := by
    have hsum : Filter.Tendsto
        (fun T : ℝ =>
          (∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u)) +
            ((∫ u : ℝ,
              (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                f (x - u)) -
              ∫ u in (-R)..R,
                (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                  f (x - u)))
        Filter.atTop (nhds (f x)) := by
      simpa using hwindow.add htail
    refine hsum.congr' ?_
    filter_upwards with T
    abel
  refine hwhole.congr' ?_
  filter_upwards with T
  exact (normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae (E := E) f x T).symm

/-- Windowed principal-value convergence with the finite-window mass discharged
by the scalar sinc limit. -/
theorem sinc_kernel_tendsto_of_windowed_pv_of_pos_radius
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R)
    (herror : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have hmass : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      Filter.atTop (nhds (f x)) :=
    by simpa using (tendsto_intervalIntegral_sin_div_kernel_scalar_mass hR).smul_const (f x)
  have hconst : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
        volume (-R) R := by
    filter_upwards with T
    let g : ℝ → E := fun u ↦ ((T / π * Real.sinc (T * u) : ℝ) : ℂ) • f x
    refine ((show Continuous g by fun_prop).intervalIntegrable (-R) R).congr_ae ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by simp [ae_iff, measure_singleton]] with u hu
    by_cases hT0 : T = 0
    · simp [g, hT0, hu]
    · simp [g, hu, Real.sinc_of_ne_zero (mul_ne_zero hT0 hu)]
      field_simp [Real.pi_ne_zero, hT0, hu]
  exact sinc_kernel_tendsto_of_windowed_pv (E := E) hconst herrInt hmass herror htail

/-- Windowed principal-value convergence from local quotient integrability and
tail control. -/
theorem sinc_kernel_tendsto_of_windowed_pv_of_local_quotient
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R)
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R := by
    exact Filter.Eventually.of_forall
      (intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
        (E := E) hq)
  have herror :
      Filter.Tendsto
        (fun T : ℝ =>
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x))
        Filter.atTop (nhds 0) :=
    tendsto_intervalIntegral_sin_div_kernel_error_of_intervalIntegrable_quotient
      (E := E) hR hq
  exact sinc_kernel_tendsto_of_windowed_pv_of_pos_radius (E := E) hR
    herrInt herror htail

/-- Principal-value convergence for the sinc kernel from source integrability
and local quotient integrability at the target point. -/
theorem sinc_kernel_tendsto_of_integrable_local_quotient
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  exact sinc_kernel_tendsto_of_windowed_pv_of_local_quotient (E := E) hR hq
    (tendsto_sin_div_kernel_tail_of_integrable (E := E) hf hR)

theorem laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  unfold laplaceInvLineTrunc fourierInvTrunc
  simp_rw [laplaceTransformBilateral_eq_fourier]
  simp only [one_div, mul_inv_rev, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_mul, add_im, mul_im, zero_add]
  rw [show (π⁻¹ * 2⁻¹ : ℝ) = (1 / (2 * π) : ℝ) by ring]
  change (1 / (2 * π) : ℝ) •
      ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
        𝓕 g (t / (2 * π)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        ((1 / (2 * π) : ℝ) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * π)))
  have hsplit :
      (∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
          𝓕 g (t / (2 * π))) =
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) • 𝓕 g (t / (2 * π)) := by
    rw [← intervalIntegral.integral_smul]
    congr with t
    rw [← smul_assoc]
    congr 1
    change Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hsplit]
  rw [SMulCommClass.smul_comm (M := ℝ) (N := ℂ) (α := E)]

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
  exact laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc sigma f hx
    (fourierInvTrunc_tendsto_of_sinc_kernel (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y) hg hdir)

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
  exact laplaceIntegralCpowTrunc_tendsto_of_sinc_kernel sigma f hx hg
    (sinc_kernel_tendsto_of_integrable_local_quotient (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
      (x := Real.log x) (R := R) hg hR hq)

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
