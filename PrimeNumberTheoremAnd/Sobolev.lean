module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import TauCeti.Analysis.Sobolev.SmoothCutoff


@[expose] public section

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  (Complex.ofRealCLM.contDiff : ContDiff ℝ n ofReal) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    have hd : iteratedDeriv k ((f : ℝ → E) - (g : ℝ → E)) =
        iteratedDeriv k f - iteratedDeriv k g :=
      funext fun x ↦ _root_.iteratedDeriv_sub hf.contDiffAt hg.contDiffAt
    simpa only [hd] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by
  let a (R x : ℝ) : ℂ := g (R⁻¹ • x) • f x
  have hnorm (k : ℕ) (u v : ℝ → ℂ) (x : ℝ) :
      ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ =
        ‖iteratedDeriv k u x - iteratedDeriv k v x‖ := by
    rw [iteratedDeriv_eq_equiv_comp, iteratedDeriv_eq_equiv_comp]
    simp only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]
  have hmem {i : ℕ} (hi : i ≤ 2) :
      MemLp (iteratedFDeriv ℝ i f) 1 (volume : Measure ℝ) := by
    refine (memLp_one_iff_integrable.2 (f.integrable hi)).congr_norm ?_ ?_
    · exact (f.smooth.continuous_iteratedFDeriv (by exact_mod_cast hi)).aestronglyMeasurable
    · exact Eventually.of_forall fun x ↦ norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm
  have hb (i : ℕ) (hi : i ≤ 2) : ∃ C, ∀ x : ℝ, ‖iteratedFDeriv ℝ i g x‖ ≤ C :=
    (g.h1.continuous_iteratedFDeriv (by exact_mod_cast hi)).bounded_above_of_compact_support
      (g.h2.iteratedFDeriv i)
  let B (i : ℕ) : ℝ := if hi : i ≤ 2 then (hb i hi).choose else 0
  have hB : ∀ i ≤ 2, ∀ x : ℝ, ‖iteratedFDeriv ℝ i g x‖ ≤ B i := by
    intro i hi
    simpa only [B, dite_eq_left hi] using (hb i hi).choose_spec
  have hlim (k : ℕ) (hk : k ≤ 2) : Tendsto (fun R : ℝ ↦ ∫ x : ℝ,
      ‖iteratedDeriv k (a R) x - iteratedDeriv k f x‖) atTop (𝓝 0) := by
    have hχ : ContDiff ℝ k g := g.h1.of_le (by exact_mod_cast hk)
    have hf : ContDiff ℝ k f := f.smooth.of_le (by exact_mod_cast hk)
    have hs (R : ℝ) : ContDiff ℝ k (a R) :=
      (hχ.comp (contDiff_const_smul _)).smul hf
    have hcut := TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub
      (μ := (volume : Measure ℝ)) (p := 1) ENNReal.one_ne_top
      (r := id) (l := atTop) (show Tendsto (id : ℝ → ℝ) atTop atTop from tendsto_id)
      hχ g.zero (fun i hi ↦ hB i (hi.trans hk)) hf (fun i hi ↦ hmem (hi.trans hk))
    change Tendsto (fun R : ℝ ↦ eLpNorm
      (iteratedFDeriv ℝ k (a R) - iteratedFDeriv ℝ k f) 1 volume) atTop (𝓝 0) at hcut
    have hto : Tendsto (fun R : ℝ ↦ (eLpNorm
        (iteratedFDeriv ℝ k (a R) - iteratedFDeriv ℝ k f) 1 volume).toReal)
        atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_zero, Function.comp_def] using!
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcut
    have hval (R : ℝ) :
        (∫ x : ℝ, ‖iteratedDeriv k (a R) x - iteratedDeriv k f x‖) =
          (eLpNorm (iteratedFDeriv ℝ k (a R) - iteratedFDeriv ℝ k f) 1 volume).toReal := by
      have hmeas : AEStronglyMeasurable
          (iteratedFDeriv ℝ k (a R) - iteratedFDeriv ℝ k f) volume :=
        ((hs R).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable.sub
          (hf.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_eNorm hmeas, ← integral_norm_eq_lintegral_eNorm hmeas]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ (hnorm k (a R) f x).symm)
    exact hto.congr (fun R ↦ (hval R).symm)
  have heq (R : ℝ) (hR : R ≠ 0) :
      ‖f - (g.scale R * f : W21)‖ =
        (∫ x : ℝ, ‖iteratedDeriv 0 (a R) x - iteratedDeriv 0 f x‖) +
        (4 * Real.pi ^ 2)⁻¹ * ∫ x : ℝ, ‖iteratedDeriv 2 (a R) x - iteratedDeriv 2 f x‖ := by
    have hfun : (fun x ↦ (f - (g.scale R * f : W21)) x) = (fun x ↦ f x - a R x) := by
      funext x
      change f x - ((g.scale R x : ℝ) : ℂ) * f x = f x - a R x
      simp [a, CS.scale, hR, funscale, RCLike.real_smul_eq_coe_mul]
    change W21.norm (fun x ↦ (f - (g.scale R * f : W21)) x) = _
    rw [hfun]
    unfold W21.norm
    congr 1
    · apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        simpa only [iteratedDeriv_zero] using norm_sub_rev (f x) (a R x)
    · congr 1
      have hs : ContDiff ℝ 2 (a R) := (g.h1.comp (contDiff_const_smul _)).smul f.smooth
      have hd : iteratedDeriv 2 ((f : ℝ → ℂ) - a R) =
          iteratedDeriv 2 f - iteratedDeriv 2 (a R) :=
        funext fun x ↦ _root_.iteratedDeriv_sub f.smooth.contDiffAt hs.contDiffAt
      have hd' : deriv (deriv (fun x ↦ f x - a R x)) =
          deriv (deriv f) - deriv (deriv (a R)) := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using! hd
      rw [hd']
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_apply]
        exact norm_sub_rev _ _
  have hsum := (hlim 0 (by decide)).add ((hlim 2 (by decide)).const_mul ((4 * Real.pi ^ 2)⁻¹))
  have hsum' : Tendsto (fun R : ℝ ↦
      (∫ x : ℝ, ‖iteratedDeriv 0 (a R) x - iteratedDeriv 0 f x‖) +
      (4 * Real.pi ^ 2)⁻¹ * ∫ x : ℝ, ‖iteratedDeriv 2 (a R) x - iteratedDeriv 2 f x‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hsum
  -- The bundled scale is zero at R = 0; the native cutoff uses g 0 there.
  apply hsum'.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
  exact (heq R hR).symm
