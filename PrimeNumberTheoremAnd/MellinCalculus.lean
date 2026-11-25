/-
Real/complex derivative coercion arguments below are based on the former Auxiliary module.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Architect
public import Batteries.Tactic.Lemma
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.MellinTransform.Convolution
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GCongr
public import Mathlib.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.MellinTransform.Decay
import TauCeti.MeasureTheory.Measure.Haar.MultHaar
public import TauCeti.Analysis.MellinTransform.SmoothCutoff


@[expose] public section

open scoped ContDiff


-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

blueprint_comment /--
\label{PartialIntegration}

Let $f, g$ be once differentiable functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ so that $fg'$
  and $f'g$ are both integrable, and $f\cdot g (x)\to 0$ as $x\to 0^+,\infty$.
  Then
  $$
  \int_0^\infty f(x)g'(x) dx = -\int_0^\infty f'(x)g(x)dx.
  $$

Partial integration.
-/

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := (support_deriv_subset (f := f)).trans
    (closure_minimal fSupp isClosed_Icc)
  have fgSupp : (f * g).support ⊆ Icc a b := (Function.support_mul_subset_left _ _).trans fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           (Function.support_mul_subset_left _ _).trans fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           (Function.support_mul_subset_left _ _).trans fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have hzero : f * g =ᶠ[𝓝 0] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h0
    exact (not_le.mpr ha) ((closure_minimal fgSupp isClosed_Icc) h0).1
  have htop : f * g =ᶠ[atTop] 0 :=
    (hasCompactSupport_iff_eventuallyEq.mp
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc fgSupp)).filter_mono
        (atTop_le_cocompact.trans cocompact_le_coclosedCompact)
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.filter_mono nhdsWithin_le_nhds).symm
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' htop.symm
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf

blueprint_comment /--
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler),
prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

Def: (Already in Mathlib)
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of
$f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$

[Note: My preferred way to think about this is that we are integrating over the multiplicative
group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and
integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds
of calculations carried out below. But may be more difficult to formalize as things now stand. So
we might have clunkier calculations, which ``magically'' turn out just right - of course they're
explained by the aforementioned structure...]

-/


local notation (name := mellintransform) "𝓜" => mellin


blueprint_comment /--
Finally, we need Mellin Convolutions and properties thereof.
-/
@[blueprint
  (title := "MellinConvolution")
  (statement := /--
  Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the
  Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$
  to $\mathbb{C}$ defined by
  $$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
  -/)]
noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

blueprint_comment /--
Let us start with a simple property of the Mellin convolution.
-/
@[blueprint
  (title := "MellinConvolutionSymmetric")
  (statement := /--
  Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{R}$ or $\mathbb{C}$, for $x\neq0$,
  $$
    (f\ast g)(x)=(g\ast f)(x)
    .
  $$
  -/)
  (proof := /--
  By Definition \ref{MellinConvolution},
  $$
    (f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}
  $$
  in which we change variables to $z=x/y$:
  $$
    (f\ast g)(x) = \int_0^\infty f(x/z)g(z)\frac{dz}{z}
    =(g\ast f)(x)
    .
  $$
  -/)
  (latexEnv := "lemma")]
lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  have hchart (f g : ℝ → 𝕂) (u : ℝ) :
      MellinConvolution f g (Real.exp (-u)) =
        convolution (fun v : ℝ => f (Real.exp (-v)))
          (fun v : ℝ => g (Real.exp (-v))) (ContinuousLinearMap.mul ℝ 𝕂) volume u := by
    simpa only [MellinConvolution, convolution, ContinuousLinearMap.mul_apply',
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, div_eq_mul_inv, mul_comm] using
      ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution (ContinuousLinearMap.mul ℝ 𝕂) f g u
  have hflip : (ContinuousLinearMap.mul ℝ 𝕂).flip = ContinuousLinearMap.mul ℝ 𝕂 := by
    ext a b
    simp
  calc
    _ = convolution (fun v : ℝ => f (Real.exp (-v)))
        (fun v : ℝ => g (Real.exp (-v))) (ContinuousLinearMap.mul ℝ 𝕂) volume
        (-Real.log x) := by simpa only [neg_neg, Real.exp_log xpos] using hchart f g (-Real.log x)
    _ = convolution (fun v : ℝ => g (Real.exp (-v)))
        (fun v : ℝ => f (Real.exp (-v))) (ContinuousLinearMap.mul ℝ 𝕂) volume
        (-Real.log x) := congrFun (convolution_symm _ hflip) _
    _ = _ := by simpa only [neg_neg, Real.exp_log xpos] using (hchart g f (-Real.log x)).symm

open Pointwise in
lemma support_MellinConvolution_subsets {f g : ℝ → 𝕂} {A B : Set ℝ} (hf : f.support ⊆ A)
    (hg : g.support ⊆ B) : (MellinConvolution f g).support ⊆ A * B := by
  intro x hx
  change (∫ y in Ioi 0, f y * g (x / y) / y) ≠ 0 at hx
  obtain ⟨y, hne, hy⟩ :=
    ((MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero hx).and_eventually
      (ae_restrict_mem measurableSet_Ioi)).exists
  have hfg := mul_ne_zero_iff.mp (div_ne_zero_iff.mp hne).1
  exact Set.mem_mul.mpr ⟨y, hf hfg.1, x / y, hg hfg.2, by field_simp [hy.ne']⟩

blueprint_comment /--
The $\nu$ function has Mellin transform $\mathcal{M}(\nu)(s)$ which is entire and decays (at
least) like $1/|s|$.

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one
power.]
-/

-- filter-free version:
@[blueprint
  (title := "MellinOfPsi")
  (statement := /--
  The Mellin transform of $\nu$ is
  $$\mathcal{M}(\nu)(s) =  O\left(\frac{1}{|s|}\right),$$
  as $|s|\to\infty$ with $\sigma_1 \le \Re(s) \le 2$.
  -/)
  (proof := /--
  Integrate by parts:
  $$
  \left|\int_0^\infty \nu(x)x^s\frac{dx}{x}\right| =
  \left|-\int_0^\infty \nu'(x)\frac{x^{s}}{s}dx\right|
  $$
  $$
  \le \frac{1}{|s|} \int_{1/2}^2|\nu'(x)|x^{\Re(s)}dx.
  $$
  Since $\Re(s)$ is bounded, the right-hand side is bounded by a
  constant times $1/|s|$.
  -/)]
lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  have hts : tsupport (fun x ↦ (ν x : ℂ)) ⊆ Icc (1 / 2) 2 :=
    closure_minimal (by simpa [Function.support_comp_eq] using suppν) isClosed_Icc
  have hc : IsCompact (tsupport (fun x ↦ (ν x : ℂ)) ∩ Ioi 0) := by
    rw [inter_eq_left.mpr (hts.trans fun x hx ↦ (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1)]
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨C, hC, hbound⟩ := TauCeti.exists_one_add_abs_im_pow_mul_norm_mellin_le (N := 1)
    (ofRealCLM.contDiff.comp diffν).contDiffOn hc (isCompact_Icc (a := 0) (b := 2))
  refine ⟨2 * C, by positivity, fun σ₁ hσ₁ s hs₁ hs₂ ↦ ?_⟩
  have hs : 0 < ‖s‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hs₁; linarith
  have hns : ‖s‖ ≤ 2 * (1 + |s.im|) := (norm_le_abs_re_add_abs_im s).trans <| by
    rw [abs_of_pos (by linarith)]; linarith [abs_nonneg s.im]
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  calc ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ * ‖s‖ ≤ ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ * (2 * (1 + |s.im|)) := by
        gcongr
    _ = 2 * ((1 + |s.im|) ^ 1 * ‖mellin (fun x ↦ (ν x : ℂ)) s‖) := by ring
    _ ≤ 2 * C := by gcongr; exact hbound s ⟨by linarith, hs₂⟩



blueprint_comment /--
We can make a delta spike out of this bumpfunction, as follows.
-/

@[blueprint
  (title := "DeltaSpike")
  (statement := /--
  Let $\nu$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the
  delta spike $\nu_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
  $$\nu_\epsilon(x) = \frac{1}{\epsilon}\nu\left(x^{\frac{1}{\epsilon}}\right).$$
  -/)]
noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

/-- On `(0, ∞)` the delta spike agrees with Tau Ceti's `TauCeti.deltaSpike`. -/
lemma DeltaSpike_eq_deltaSpike {ν : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x) :
    DeltaSpike ν ε x = TauCeti.deltaSpike ν ε x := by
  rw [TauCeti.deltaSpike_of_pos hx, DeltaSpike, one_div, div_eq_inv_mul]

blueprint_comment /--
This spike still has mass one:
-/

@[blueprint
  (title := "DeltaSpikeMass")
  (statement := /--
  For any $\epsilon>0$, we have
  $$\int_0^\infty \nu_\epsilon(x)\frac{dx}{x} = 1.$$
  -/)
  (proof := /--
  Substitute $y=x^{1/\epsilon}$, and use the fact that $\nu$ has mass one, and that $dx/x$ is Haar
  measure.
  -/)
  (latexEnv := "lemma")]
lemma DeltaSpikeMass {ν : ℝ → ℝ} (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike ν ε) x) / x = 1 := by
  rw [← mass_one, ← TauCeti.integral_deltaSpike_div ν εpos]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
    simp only [DeltaSpike_eq_deltaSpike (mem_Ioi.mp hx)]



blueprint_comment /--
The Mellin transform of the delta spike is easy to compute.
-/
@[blueprint
  (title := "MellinOfDeltaSpike")
  (statement := /--
  For any $\epsilon>0$, the Mellin transform of $\nu_\epsilon$ is
  $$\mathcal{M}(\nu_\epsilon)(s) = \mathcal{M}(\nu)\left(\epsilon s\right).$$
  -/)
  (proof := /-- Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation. -/)]
theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  rw [← TauCeti.mellin_deltaSpike ν εpos s]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
    simp only [DeltaSpike_eq_deltaSpike (mem_Ioi.mp hx)]



blueprint_comment /--
In particular, for $s=1$, we have that the Mellin transform of $\nu_\epsilon$ is $1+O(\epsilon)$.
-/

@[blueprint
  (title := "MellinOfDeltaSpikeAt1")
  (statement := /--
  For any $\epsilon>0$, we have
  $$\mathcal{M}(\nu_\epsilon)(1) =
  \mathcal{M}(\nu)(\epsilon).$$
  -/)
  (proof := /-- This is immediate from the above theorem. -/)
  (latexEnv := "corollary")]
lemma MellinOfDeltaSpikeAt1 (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) 1 = 𝓜 (fun x ↦ (ν x : ℂ)) ε := by
  convert MellinOfDeltaSpike ν εpos 1; simp [mul_one]



@[blueprint
  (title := "MellinOfDeltaSpikeAt1-asymp")
  (statement := /--
  As $\epsilon\to 0$, we have
  $$\mathcal{M}(\nu_\epsilon)(1) = 1+O(\epsilon).$$
  -/)
  (proof := /--
  By Lemma \ref{MellinOfDeltaSpikeAt1},
  $$
    \mathcal M(\nu_\epsilon)(1)=\mathcal M(\nu)(\epsilon)
  $$
  which by Definition \ref{MellinTransform} is
  $$
    \mathcal M(\nu)(\epsilon)=\int_0^\infty\nu(x)x^{\epsilon-1}dx
    .
  $$
  Since $\nu(x) x^{\epsilon-1}$ is integrable (because $\nu$ is continuous and compactly
  supported),
  $$
    \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x
    =\int_0^\infty\nu(x)(x^{\epsilon-1}-x^{-1})dx
    .
  $$
  By Taylor's theorem,
  $$
    x^{\epsilon-1}-x^{-1}=O(\epsilon)
  $$
  so, since $\nu$ is absolutely integrable,
  $$
    \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x=O(\epsilon)
    .
  $$
  We conclude the proof using Theorem \ref{SmoothExistence}.
  -/)
  (latexEnv := "lemma")]
lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have hsupport : (fun x ↦ (ν x : ℂ)).support ⊆ Icc (1 / 2 : ℝ) 2 := by
    rwa [show (fun x ↦ (ν x : ℂ)).support = ν.support from
      Function.support_comp_eq Complex.ofReal (by simp) ν]
  have hzero : (fun x ↦ (ν x : ℂ)) =ᶠ[𝓝 0] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h0
    have := ((closure_minimal hsupport isClosed_Icc) h0).1
    norm_num at this
  have htop : (fun x ↦ (ν x : ℂ)) =ᶠ[atTop] 0 :=
    (hasCompactSupport_iff_eventuallyEq.mp
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport)).filter_mono
        (atTop_le_cocompact.trans cocompact_le_coclosedCompact)
  have diff : DifferentiableWithinAt ℝ
      (fun (ε : ℝ) ↦ 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine (DifferentiableAt.hasDerivAt ?_).comp_ofReal.differentiableAt
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      exact Asymptotics.isBigO_zero_right_iff.mpr htop
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      exact Asymptotics.isBigO_zero_right_iff.mpr (hzero.filter_mono nhdsWithin_le_nhds)
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert! this using 1
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  funext ε
  congr 1
  symm
  calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
      = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast; ring)
    _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [mass_one, ofReal_one]



blueprint_comment /--
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform:
[Note: this already exists in mathlib]
-/
blueprint_comment /--
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$.
-/
@[blueprint
  (title := "Smooth1")
  (statement := /--
  Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from
  $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
  $$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\nu_\epsilon.$$
  -/)
  (proof := /--
  Let $c:=2^\epsilon > 1$, in terms of which we wish to prove
  $$
    -1 < c \log c - c .
  $$
  Letting $f(x):=x\log x - x$, we can rewrite this as $f(1) < f(c)$.
  Since
  $$
    \frac {d}{dx}f(x) = \log x > 0 ,
  $$
  $f$ is monotone increasing on [1, \infty), and we are done.
  -/)
  (latexEnv := "definition")]
noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

/-- On `(0, ∞)` the smoothed cutoff agrees with Tau Ceti's `TauCeti.smoothCutoff`. -/
lemma Smooth1_eq_smoothCutoff {ν : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x) :
    Smooth1 ν ε x = TauCeti.smoothCutoff ν ε x := by
  have h := TauCeti.smoothCutoff_eq_mellinConv ν ε hx
  rw [TauCeti.mellinConv_def] at h
  apply ofReal_injective
  rw [h, Smooth1, MellinConvolution, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
  simp [DeltaSpike_eq_deltaSpike (div_pos hx hy), Set.indicator, Set.mem_Ioc, apply_ite]

/-% ** Wrong delimiters on purpose, no need to include this in blueprint
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  rw [div_lt_iff₀ εpos, rpow_def_of_pos two_pos]
  linarith [add_one_lt_exp (x := Real.log 2 * -ε) (by have := log_pos one_lt_two; nlinarith)]

blueprint_comment /--
In particular, we have the following two properties.
-/

@[blueprint
  (title := "Smooth1Properties-below")
  (statement := /--
  Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
  If $0 < x \leq (1-c\epsilon)$, then
  $$\widetilde{1_{\epsilon}}(x) = 1.$$
  -/)
  (proof := /--
  Opening the definition, we have that the Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$ is
  $$
  \int_0^\infty 1_{(0,1]}(y)\nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}.
  $$
  The support of $\nu_\epsilon$ is contained in $[1/2^\epsilon,2^\epsilon]$, so it suffices to
  consider $y \in [1/2^\epsilon x,2^\epsilon x]$ for nonzero contributions. If $x < 2^{-\epsilon}$,
  then the integral is the same as that over $(0,\infty)$:
  $$
  \int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y},
  $$
  in which we change variables to $z=x/y$ (using $x>0$):
  $$
  \int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^\infty \nu_\epsilon(z)\frac{dz}{z},
  $$
  which is equal to one by Lemma \ref{DeltaSpikeMass}.
  We then choose
  $$
    c:=\log 2,
  $$
  which satisfies
  $$
    c > \frac{1-2^{-\epsilon}}\epsilon
  $$
  by Lemma \ref{Smooth1Properties_estimate}, so
  $$
    1-c\epsilon < 2^{-\epsilon}.
  $$
  -/)
  (latexEnv := "lemma")]
lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  refine ⟨_, log_pos one_lt_two, rfl, fun ε x εpos xpos hx ↦ ?_⟩
  rw [Smooth1_eq_smoothCutoff xpos]
  refine TauCeti.smoothCutoff_eq_one (inter_subset_left.trans suppν) mass_one εpos xpos ?_
  linarith [(div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos]



@[blueprint
  (title := "Smooth1Properties-above")
  (statement := /--
  Fix $0<\epsilon<1$. There is an absolute constant $c>0$ so that:
  if $x\geq (1+c\epsilon)$, then
  $$\widetilde{1_{\epsilon}}(x) = 0.$$
  -/)
  (proof := /--
  Again the Mellin convolution is
  $$\int_0^1 \nu_\epsilon(x/y)\frac{dy}{y},$$
  but now if $x > 2^\epsilon$, then the support of $\nu_\epsilon$ is disjoint
  from the region of integration, and hence the integral is zero.
  We choose
  $$
    c:=2\log 2
    .
  $$
  By Lemma \ref{Smooth1Properties_estimate},
  $$
    c > 2\frac{1-2^{-\epsilon}}\epsilon > 2^\epsilon\frac{1-2^{-\epsilon}}\epsilon
    =
    \frac{2^\epsilon-1}\epsilon,
  $$
  so
  $$
    1+c\epsilon > 2^\epsilon.
  $$
  -/)
  (latexEnv := "lemma")]
lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  refine ⟨_, by positivity [log_pos one_lt_two], rfl, fun ε x hε hx ↦ ?_⟩
  have hx2 : 2 ^ ε < x := by
    have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hε.1.le hε.2.le
    have h2 := add_one_lt_exp (neg_ne_zero.mpr (log_pos one_lt_two).ne')
    rw [Real.exp_neg, Real.exp_log two_pos] at h2
    norm_num at h
    nlinarith [hε.1]
  rw [Smooth1_eq_smoothCutoff ((rpow_pos_of_pos two_pos ε).trans hx2)]
  exact TauCeti.smoothCutoff_eq_zero (inter_subset_left.trans suppν) hε.1 hx2.le


@[blueprint
  (title := "Smooth1Nonneg")
  (statement := /--
  If $\nu$ is nonnegative, then $\widetilde{1_{\epsilon}}(x)$ is nonnegative.
  -/)
  (proof := /--
  By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
  $$
    \widetilde{1_\epsilon}(x)
    =\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  and all the factors in the integrand are nonnegative.
  -/)
  (latexEnv := "lemma")]
lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  exact Smooth1_eq_smoothCutoff xpos ▸ TauCeti.smoothCutoff_nonneg νnonneg εpos.le x


@[blueprint
  (title := "Smooth1LeOne")
  (statement := /--
  If $\nu$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$, $\forall x>0$.
  -/)
  (proof := /--
  By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
  $$
    \widetilde{1_\epsilon}(x)
    =\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  and since $1_{(0,1]}(y)\le 1$, and all the factors in the integrand are nonnegative,
  $$
    \widetilde{1_\epsilon}(x)\le\int_0^\infty \frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  (because in mathlib the integral of a non-integrable function is $0$, for the inequality above
  to be true, we must prove that $\nu((x/y)^{\frac1\epsilon})/y$ is integrable; this follows from
  the computation below).
  We then change variables to $z=(x/y)^{\frac1\epsilon}$:
  $$
    \widetilde{1_\epsilon}(x)\le\int_0^\infty \nu(z) \frac{dz}z
  $$
  which by Theorem \ref{SmoothExistence} is 1.
  -/)
  (latexEnv := "lemma")]
lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  exact Smooth1_eq_smoothCutoff xpos ▸ TauCeti.smoothCutoff_le_one νnonneg mass_one εpos x



blueprint_comment /--
Combining the above, we have the following three Main Lemmata of this section on the Mellin
transform of $\widetilde{1_{\epsilon}}$.
-/
@[blueprint
  (title := "MellinOfSmooth1a")
  (statement := /--
  Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(s) =
  \frac{1}{s}\left(\mathcal{M}(\nu)\left(\epsilon s\right)\right).$$
  -/)
  (proof := /--
  By Definition \ref{Smooth1},
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(1_{(0,1]}\ast\nu_\epsilon)(s)
    .
  $$
  We wish to apply the Mellin convolution product theorem from Tau Ceti.
  To do so, we must prove that
  $$
    (x,y)\mapsto 1_{(0,1]}(y)\nu_\epsilon(x/y)/y
  $$
  is integrable on $[0,\infty)^2$.
  It is actually easier to do this for the convolution: $\nu_\epsilon\ast 1_{(0,1]}$, so we use
  Lemma \ref{MellinConvolutionSymmetric}: for $x\neq0$,
  $$
    1_{(0,1]}\ast\nu_\epsilon(x)=\nu_\epsilon\ast 1_{(0,1]}(x)
    .
  $$
  Now, for $x=0$, both sides of the equation are 0, so the equation also holds for $x=0$.
  Therefore,
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(\nu_\epsilon\ast 1_{(0,1]})(s)
    .
  $$
  Now,
  $$
    (x,y)\mapsto \nu_\epsilon(y)1_{(0,1]}(x/y)\frac{x^{s-1}}y
  $$
  has compact support that is bounded away from $y=0$ (specifically
  $y\in[2^{-\epsilon},2^\epsilon]$ and $x\in(0,y]$), so it is integrable.
  We can thus apply the Mellin convolution product theorem from Tau Ceti and find
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(\nu_\epsilon)(s)\mathcal M(1_{(0,1]})(s)
    .
  $$
  By Mathlib's Mellin transform of $1_{(0,1]}$ and Lemma \ref{MellinOfDeltaSpike},
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\frac1s\mathcal M(\nu)(\epsilon s)
    .
  $$
  -/)
  (latexEnv := "lemma")]
lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have hi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0) :=
    (integrableOn_iff_integrable_of_support_subset ((Function.support_div _ _).trans_subset
      (inter_subset_left.trans suppν))).mp <|
      (diffν.continuous.continuousOn.div continuousOn_id fun x hx ↦
        (by linarith [hx.1] : (0:ℝ) < x).ne').integrableOn_compact isCompact_Icc
  rw [inv_mul_eq_div, ← TauCeti.mellin_smoothCutoff (inter_subset_left.trans suppν) hi εpos hs]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
    simp only [Smooth1_eq_smoothCutoff (mem_Ioi.mp hx)]



@[blueprint
  (title := "MellinOfSmooth1b")
  (statement := /--
  Given $0<\sigma_1\le\sigma_2$, for any $s$ such that $\sigma_1\le\mathcal Re(s)\le\sigma_2$,
  we have
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$
  -/)
  (proof := /-- Use Lemma \ref{MellinOfSmooth1a} and the bound in Lemma \ref{MellinOfPsi}. -/)
  (latexEnv := "lemma")]
lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring




@[blueprint
  (title := "MellinOfSmooth1c")
  (statement := /--
  At $s=1$, we have
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = 1+O(\epsilon)).$$
  -/)
  (proof := /--
  Follows from Lemmas \ref{MellinOfSmooth1a}, \ref{MellinOfDeltaSpikeAt1} and
  \ref{MellinOfDeltaSpikeAt1_asymp}.
  -/)
  (latexEnv := "lemma")]
lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε



@[blueprint
  (title := "Smooth1ContinuousAt")
  (statement := /--
  Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$. Then for any $\epsilon>0$, the function
  $x \mapsto \int_{(0,\infty)} x^{1+it} \widetilde{1_{\epsilon}}(x) dx$ is continuous at any $y>0$.
  -/)
  (proof := /--
  Use Lemma \ref{MellinconvolutionSymmetric} to write $\widetilde{1_{\epsilon}}(x)$ as an integral
  over an integral near $1$, in particular avoiding the singularity at $0$. The integrand may be
  bounded by $2^{\epsilon}\nu_\epsilon(t)$ which is independent of $x$ and we can use dominated
  convergence to prove continuity.
  -/)
  (latexEnv := "lemma")]
lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (_SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  have hi : IntegrableOn (fun x ↦ SmoothingF x / x) (Ioi 0) :=
    (integrableOn_iff_integrable_of_support_subset ((Function.support_div _ _).trans_subset
      (inter_subset_left.trans suppSmoothingF))).mp <|
      (diffSmoothingF.continuous.continuousOn.div continuousOn_id fun x hx ↦
        (by linarith [hx.1] : (0:ℝ) < x).ne').integrableOn_compact isCompact_Icc
  refine ((TauCeti.continuousOn_smoothCutoff hi εpos).continuousAt (Ioi_mem_nhds ypos)).congr ?_
  filter_upwards [Ioi_mem_nhds ypos] with x hx using (Smooth1_eq_smoothCutoff hx).symm




lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
