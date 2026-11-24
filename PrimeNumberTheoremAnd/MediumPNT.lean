module

public import Architect
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import PrimeNumberTheoremAnd.MellinCalculus
public import PrimeNumberTheoremAnd.SmoothExistence
public import PrimeNumberTheoremAnd.ZetaBounds
public import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.LSeries.SmoothedSum


@[expose] public section


open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

blueprint_comment /--
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in [Kontorovich 2015].
-/

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

blueprint_comment /--
\label{ChebyshevPsi}
The (second) Chebyshev Psi function is defined as
$$\psi(x) := \sum_{n \le x} \Lambda(n),$$
where $\Lambda(n)$ is the von Mangoldt function. This is Mathlib's `Chebyshev.psi`.
-/

blueprint_comment /--
It has already been established that zeta doesn't vanish on the 1 line, and has a pole at $s=1$
of order 1.
We also have the following.
-/

@[blueprint "LogDerivativeDirichlet"
  (title := "LogDerivativeDirichlet")
  (statement := /--
  We have that, for $\Re(s)>1$,
  $$-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}. $$-/)
  (proof := /-- Already in Mathlib. -/)]
theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! this; rename ℕ => n
    by_cases h : n = 0 <;> simp [LSeries.term, h]

blueprint_comment /--

The main object of study is the following inverse Mellin-type transform, which will turn out to
be a smoothed Chebyshev function.
-/

noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

@[blueprint
  (title := "SmoothedChebyshev")
  (statement := /--
  Fix $\epsilon>0$, and a bumpfunction supported in $[1/2,2]$. Then we define the smoothed
  Chebyshev function $\psi_{\epsilon}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
  $$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(\sigma)}\frac{-\zeta'(s)}{\zeta(s)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  X^{s}ds,$$
  where we'll take $\sigma = 1 + 1 / \log X$.
  -/)]
noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

blueprint_comment /--
Now in Mathlib:
-/
blueprint_comment /--
\begin{theorem}\label{deriv-conj-conj}
    Let $f : \mathbb{C} \to \mathbb{C}$ be a function at $p \in \mathbb{C}$ with derivative $a$.
    Then the derivative of the function $g(z) = \overline{f(\overline{z})}$ at $\overline{p}$ is
    $\overline{a}$.
  \end{theorem}
\begin{proof}
    We proceed by case analysis on whether $f$ is differentiable at $p$. If $f$ is differentiable
    at $p$, then we can apply the previous theorem. If $f$ is not differentiable at $p$, then
    neither is $g$, and both derivatives have the default value of zero.
  \end{proof}
-/

blueprint_comment /--
\begin{theorem}[deriv-riemannZeta-conj]\label{deriv_riemannZeta_conj}
    Conjugation symmetry of the derivative of the Riemann zeta function. Let $s \in \mathbb{C}$.
    Then $$\zeta'(\overline{s}) = \overline{\zeta'(s)}.$$
\end{theorem}
\begin{proof}
    We apply the canonical affine derivative reflection theorem to the conjugation symmetry of
    the Riemann zeta function. The theorem also covers its totalized derivative at the pole.
\end{proof}
-/

blueprint_comment /--
\begin{theorem}\label{intervalIntegral-conj}
    The conjugation symmetry of the interval integral. Let $f : \mathbb{R} \to \mathbb{C}$ be a
    measurable function, and let $a, b \in \mathbb{R}$. Then
    $$\int_{a}^{b} \overline{f(x)} \, dx = \overline{\int_{a}^{b} f(x) \, dx}.$$
  \end{theorem}
\begin{proof}
    We unfold the interval integral into an integral over a uIoc and use the conjugation property
    of integrals.
  \end{proof}
-/


set_option backward.isDefEq.respectTransparency false in
lemma smoothedChebyshevIntegrand_conj
    {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) =
      conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · simpa using TauCeti.deriv_conj_eq_mul_conj_deriv
      (c := 0) (u := 1) isOpen_univ (fun z _ => by simp) (mem_univ s)
  · exact riemannZeta_conj s
  · unfold mellin
    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open MeasureTheory

@[blueprint
  (title := "SmoothedChebyshevDirichlet-aux-integrable")
  (statement := /--
  Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$,
  and $\sigma\in (1, 2]$, the function
  $$
  x \mapsto\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma + ix)
  $$
  is integrable on $\mathbb{R}$.
  -/)
  (proof := /--
  By Lemma \ref{MellinOfSmooth1b} the integrand is $O(1/t^2)$ as $t\rightarrow \infty$ and hence
  the function is integrable.
  -/)
  (latexEnv := "lemma")]
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

set_option backward.isDefEq.respectTransparency false in
@[blueprint
  (title := "SmoothedChebyshevDirichlet-aux-tsum-integral")
  (statement := /--
  Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$ and
  $\sigma\in(1,2]$, the function
  $x \mapsto \sum_{n=1}^\infty \frac{\Lambda(n)}{n^{\sigma+it}}
  \mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$ is equal to
  $\sum_{n=1}^\infty \int_{(0,\infty)} \frac{\Lambda(n)}{n^{\sigma+it}}
  \mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$.
  -/)
  (proof := /-- Interchange of summation and integration. -/)
  (latexEnv := "lemma")]
lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [eNorm_mul, eNorm_eq_nnNorm, nnNorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnNorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    · simp_rw [← eNorm_eq_nnNorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_eNorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
@[blueprint
  (title := "SmoothedChebyshevDirichlet")
  (proofUses := ["Smooth1ContinuousAt", "SmoothedChebyshevDirichlet_aux_integrable",
    "LogDerivativeDirichlet", "SmoothedChebyshevDirichlet_aux_tsum_integral", -"VerticalIntegral"])
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) = \sum_{n=1}^\infty \Lambda(n)\widetilde{1_{\epsilon}}(n/X).$$
  -/)
  (proof := /--
  We have that
  $$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  X^{s}ds.$$
  We have enough decay (thanks to quadratic decay of $\mathcal{M}(\widetilde{1_{\epsilon}})$) to
  justify the interchange of summation and integration. We then get
  $$\psi_{\epsilon}(X) =
  \sum_{n=1}^\infty \Lambda(n)\frac{1}{2\pi i}\int_{(2)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)
  (n/X)^{-s}
  ds
  $$
  and apply the Mellin inversion formula.
  -/)]
theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (_SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (_mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  unfold SmoothedChebyshev
  have X_pos : 0 < X := by linarith
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have σ_gt : 1 < σ := lt_add_of_pos_right 1 (inv_pos.mpr (by linarith [logt_gt_one X_gt.le]))
  have h := TauCeti.LSeries.hasSum_mul_smoothCutoff (f := fun n ↦ (Λ n : ℂ)) (σ := σ) (X := X)
    diffSmoothingF.contDiffOn (inter_subset_left.trans suppSmoothingF) εpos (by linarith)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [ofReal_re]; exact σ_gt)) X_pos
  have hterm (n : ℕ) : (Λ n : ℂ) * (Smooth1 SmoothingF ε (n / X) : ℂ) =
      (Λ n : ℂ) * (TauCeti.smoothCutoff SmoothingF ε (n / X) : ℂ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Smooth1_eq_smoothCutoff (div_pos (Nat.cast_pos.mpr hn) X_pos)]
  have hint (t : ℝ) : SmoothedChebyshevIntegrand SmoothingF ε X (σ + t * I) =
      ((X⁻¹ : ℝ) : ℂ) ^ (-(σ + t * I)) * (LSeries (fun n ↦ (Λ n : ℂ)) (σ + t * I) *
        mellin (fun x ↦ (TauCeti.smoothCutoff SmoothingF ε x : ℂ)) (σ + t * I)) := by
    have hM : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + t * I) =
        mellin (fun x ↦ (TauCeti.smoothCutoff SmoothingF ε x : ℂ)) (σ + t * I) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
        simp only [Smooth1_eq_smoothCutoff (mem_Ioi.mp hx)]
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; linarith),
      ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg X_pos.le]; exact Real.pi_ne_zero.symm),
      cpow_neg, inv_inv, SmoothedChebyshevIntegrand, hM]
    ring
  beta_reduce at h
  rw [ofReal_tsum]
  simp only [ofReal_mul]
  rw [tsum_congr hterm, h.tsum_eq]
  simp only [VerticalIntegral', VerticalIntegral, mellinInv, smul_eq_mul, real_smul, hint]
  rw [← mul_assoc]
  congr 1
  push_cast
  field_simp

blueprint_comment /--
The smoothed Chebyshev function is close to the actual Chebyshev function.
-/

@[blueprint
  (title := "SmoothedChebyshevClose")
  (proofUses := ["Smooth1Nonneg", "Smooth1Properties_above", "Smooth1Properties_below",
    "Smooth1LeOne", -"DeltaSpike", -"MellinConvolution"])
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X \log X).$$
  -/)
  (proof := /--
  Take the difference. By Lemma \ref{Smooth1Properties_above} and \ref{Smooth1Properties_below},
  the sums agree except when $1-c \epsilon \leq n/X \leq 1+c \epsilon$. This is an interval of
  length $\ll \epsilon X$, and the summands are bounded by $\Lambda(n) \ll \log X$.

  %[No longer relevant, as we will do better than any power of log savings...: This is not enough,
  %as it loses a log! (Which is fine if our target is the strong PNT, with
  %exp-root-log savings, but not here with the ``softer'' approach.) So we will need something like
  %the Selberg sieve (already in Mathlib? Or close?) to conclude that the number of primes in this
  %interval is $\ll \epsilon X / \log X + 1$.
  %(The number of prime powers is $\ll X^{1/2}$.)
  %And multiplying that by $\Lambda (n) \ll \log X$ gives the desired bound.]
  -/)]
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
  refine ⟨8, by norm_num, fun X X_gt ε εpos ε_lt_one hXε ↦ ?_⟩
  have X_pos : 0 < X := by linarith
  have hterm (n : ℕ) : (Λ n : ℂ) * (Smooth1 SmoothingF ε (n / X) : ℂ) =
      (Λ n : ℂ) * (TauCeti.smoothCutoff SmoothingF ε (n / X) : ℂ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Smooth1_eq_smoothCutoff (div_pos (Nat.cast_pos.mpr hn) X_pos)]
  have h := TauCeti.norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le SmoothingFnonneg
    (inter_subset_left.trans suppSmoothingF) mass_one εpos ε_lt_one.le (X := X) (by linarith)
  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF mass_one X_gt
    εpos ε_lt_one, ofReal_tsum]
  simp only [ofReal_mul]
  rw [tsum_congr hterm, norm_sub_rev]
  exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith) (Real.log_nonneg (by linarith)))

@[blueprint "LogDerivZetaHasBound"
  (title := "LogDerivZetaHasBound")
  (statement := /--
  For constants $A$, $C$, $n_1$, and $n_2$ this is true if for all $3<|t|$ one has
  $$1-\frac{A}{\log|t|^{n_1}}\leq\sigma\implies|(\zeta'/\zeta)(\sigma+it)|\leq C\,\log|t|^{n_2}.$$
  -/)]
def LogDerivZetaHasBound (n₁ n₂ : ℝ) (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ n₂

blueprint_comment /--
Suppose we have an estimate of the form in Definition \ref{LogDerivZetaHasBound}. Returning to the
definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and set
$\sigma_0 = 1 + 1 / log X$,
$\sigma_1 = 1- A/ \log T^{n_1}$ (where $n_1$ comes from our estimate from Definition
\ref{LogDerivZetaHasBound}), and
$\sigma_2<\sigma_1$ a constant.
Pull
contours (via rectangles!) to go
from $\sigma_0-i\infty$ up to $\sigma_0-iT$, then over to $\sigma_1-iT$, up to $\sigma_1-3i$,
over to $\sigma_2-3i$, up to $\sigma_2+3i$, back over to $\sigma_1+3i$, up to $\sigma_1+iT$,
over to $\sigma_0+iT$, and finally up to $\sigma_0+i\infty$.

In the process, we will pick up the residue at $s=1$.
We will do this in several stages. Here the interval integrals are defined as follows:
-/

@[blueprint
  "I1"
  (title := "I₁")
  (statement := /--
  $$
  I_1(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{-\infty}^{-T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
   \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i}
  \ i \ dt
  $$
  -/)]
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

@[blueprint
  "I2"
  (title := "I₂")
  (statement := /--
  $$
  I_2(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
  \left(
  \frac{-\zeta'}\zeta(\sigma - i T)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma - i T)
  X^{\sigma - i T} \ d\sigma
  $$
  -/)]
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

@[blueprint
  "I37"
  (title := "I₃₇")
  (statement := /--
  $$
  I_{37}(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I8"
  (title := "I₈")
  (statement := /--
  $$
  I_8(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
  \left(
  \frac{-\zeta'}\zeta(\sigma + T i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma + T i)
  X^{\sigma + T i} \ d\sigma
  $$
  -/)]
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

@[blueprint
  "I9"
  (title := "I₉")
  (statement := /--
  $$
  I_9(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{T}^{\infty}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

@[blueprint
  "I3"
  (title := "I₃")
  (statement := /--
  $$
  I_3(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{-3}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I7"
  (title := "I₇")
  (statement := /--
  $$
  I_7(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{3}^{T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_1 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

@[blueprint
  "I4"
  (title := "I₄")
  (statement := /--
  $$
  I_4(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
  \left(
  \frac{-\zeta'}\zeta(\sigma - 3 i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma - 3 i)
  X^{\sigma - 3 i} \ d\sigma
  $$
  -/)]
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

@[blueprint
  "I6"
  (title := "I₆")
  (statement := /--
  $$
  I_6(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
  \left(
  \frac{-\zeta'}\zeta(\sigma + 3 i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma + 3 i)
  X^{\sigma + 3 i} \ d\sigma
  $$
  -/)]
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

@[blueprint
  "I5"
  (title := "I₅")
  (statement := /--
  $$
  I_5(\nu, \epsilon, X, \sigma_2) := \frac{1}{2\pi i} \int_{-3}^{3}
  \left(
  \frac{-\zeta'}\zeta(\sigma_2 + t i)
  \right)
    \mathcal M(\widetilde 1_\epsilon)(\sigma_2 + t i)
  X^{\sigma_2 + t i} \ i \ dt
  $$
  -/)]
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    DifferentiableOn ℂ (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
@[blueprint
  (title := "dlog-riemannZeta-bdd-on-vertical-lines")
  (statement := /--
  For $\sigma_0 > 1$, there exists a constant $C > 0$ such that
  $$
  \forall t \in \R, \quad
  \left\| \frac{\zeta'(\sigma_0 + t i)}{\zeta(\sigma_0 + t i)} \right\| \leq C.
  $$
  -/)
  (proof := /--
  Write as Dirichlet series and estimate trivially using Theorem \ref{LogDerivativeDirichlet}.
  -/)
  (latexEnv := "lemma")]
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by
  refine ⟨1 + ‖(ζ' σ₀ / ζ σ₀)‖, (by positivity), fun t ↦ ?_⟩
  have := dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t σ₀_gt le_rfl
  rw [neg_div, norm_neg] at this
  exact le_trans this (lt_one_add _).le

@[blueprint
  (title := "SmoothedChebyshevPull1-aux-integrable")
  (statement := /--
  The integrand $$\zeta'(s)/\zeta(s)\mathcal{M}(\widetilde{1_{\epsilon}})(s)X^{s}$$
  is integrable on the contour $\sigma_0 + t i$ for $t \in \R$ and $\sigma_0 > 1$.
  -/)
  (proof := /--
  The $\zeta'(s)/\zeta(s)$ term is bounded, as is $X^s$, and the smoothing function
  $\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
  decays like $1/|s|^2$ by Theorem \ref{MellinOfSmooth1b}.
  Actually, we already know that
  $\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
  is integrable from Theorem \ref{SmoothedChebyshevDirichlet_aux_integrable},
  so we should just need to bound the rest.
  -/)
  (latexEnv := "lemma")]
theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · convert! hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, ne_eq]
        linarith
  convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul
      (c := c) ?_ (ae_of_all _ this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := fun h ↦ by simpa [s, σ₀_gt.ne'] using congr_arg re h
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          (analyticOn_riemannZeta _ s_ne_one).deriv.differentiableAt
        simpa only [Function.comp_def, s] using
          this.continuousAt.comp (f := fun x : ℝ ↦ (σ₀ : ℂ) + x * I) (by fun_prop)
      · simpa only [Function.comp_def, s] using
          diffζ.continuousAt.comp (f := fun x : ℝ ↦ (σ₀ : ℂ) + x * I) (by fun_prop)
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith

blueprint_comment /--
\label{BddAboveOnRect}
Let $g : \C \to \C$ be a holomorphic function on a rectangle, then $g$ is bounded above on the rectangle.

Use the compactness of the rectangle and the fact that holomorphic functions are continuous.
-/

@[blueprint
  (title := "SmoothedChebyshevPull1")
  (statement := /--
  We have that
  $$\psi_{\epsilon}(X) =
  \mathcal{M}(\widetilde{1_{\epsilon}})(1)
  X^{1} +
  I_1 - I_2 +I_{37} + I_8 + I_9
  .
  $$
  -/)
  (proof := /-- Pull rectangle contours and evaluate the pole at $s=1$. -/)]
theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : DifferentiableOn ℂ (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    bound
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
    unfold I₁
    simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    unfold I₉
    nth_rewrite 6 [add_comm]
    simp only [← add_assoc]
    rw [add_right_cancel_iff,
        ← add_right_inj (1 / (2 * ↑π * I) *
          -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
        ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
        unfold fTempRR
        simp only [temp]
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
        unfold fTempRR
        simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
    rw[this]
    have : ∫ (t : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
    rw[this]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
        -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
        I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
        unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
        simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
          ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
          neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
          ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
          zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
        ring_nf
        simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
          mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
        ring_nf
    rw[this]
    field_simp
    rw[mul_comm, eq_comm, neg_add_eq_zero]

    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine (show Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds (1 : ℂ) ↔
            (1 : ℂ) ∈ (uIoo (σ₁ - ↑T * I).re (1 + (Real.log X)⁻¹ + T * I).re) ×ℂ
              (uIoo (σ₁ - ↑T * I).im (1 + (Real.log X)⁻¹ + T * I).im) from by
          simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
            interior_Icc]).mpr ?_
      refine mem_reProdIm.mpr ?_
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
        sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
      constructor
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

    apply ResidueTheoremOnRectangleWithSimplePole'
    · simp; linarith
    · simp; linarith
    · simp only [one_div]
      exact pInRectangleInterior
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · simp only [re_add_im]
          have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
          rw [this]
          apply DifferentiableOn.neg
          apply holoOn.mono
          apply Set.sdiff_subset_sdiff_left
          apply reProdIm_subset_iff'.mpr
          left
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
            neg_zero, zero_div, zero_add]
          constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          have := mem_reProdIm.mp hs.1 |>.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        simp only [re_add_im]
        apply DifferentiableAt.const_cpow (by fun_prop)
        left
        norm_cast
        linarith
    · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
      let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      unfold fTempC fTempRR SmoothedChebyshevIntegrand
      simp only [re_add_im]
      have g_holc : DifferentiableOn ℂ g U := by
        intro u uInU
        apply DifferentiableAt.differentiableWithinAt
        simp only [g]
        apply DifferentiableAt.mul
        · apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          simp only [ofReal_inv, U] at uInU
          unfold Rectangle at uInU
          rw[Complex.mem_reProdIm] at uInU
          have := uInU.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
        · unfold HPow.hPow instHPow
          apply DifferentiableAt.const_cpow differentiableAt_fun_id
          left
          norm_cast
          linarith
      have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        simp only [one_mul, f]
        change (fun s : ℂ ↦ -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹)
          =O[nhdsWithin 1 {1}ᶜ] (fun _ ↦ (1 : ℂ))
        simpa only [neg_add, sub_eq_add_neg, neg_div]
          using log_deriv_riemannZeta_add_inv_sub_bounded.neg_left
      convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
      ext
      simp [f, g]
      ring

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a),
    ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals
    apply IntervalIntegrable.mono_set hf
    apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : DifferentiableOn ℂ (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) =
      -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp only [Set.mem_sdiff, mem_singleton_iff]
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

blueprint_comment /--
Next pull contours to another box.
-/

@[blueprint
  (title := "SmoothedChebyshevPull2")
  (statement := /--
  We have that
  $$
  I_{37} =
  I_3 - I_4 + I_5 + I_6 + I_7
  .
  $$
  -/)
  (proof := /-- Mimic the proof of Lemma \ref{SmoothedChebyshevPull1}. -/)
  (latexEnv := "lemma")]
theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : DifferentiableOn ℂ (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : DifferentiableOn ℂ (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith
  -- Step (1)
  -- Show that the Rectangle is in a given subset of holomorphicity
  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    have h : Icc σ₂ 2 ×ℂ Icc (-3) 3 = Rectangle z (2 + 3 * I) := by
      rw [Rectangle, uIcc_of_le (by simp [z]; linarith), uIcc_of_le (by simp [z])]
      simp [z]
    rw [h]
    refine rectangle_subset_punctured_rect ?_ (.inr (.inr (.inl ⟨?_, ?_⟩)))
    · simp only [z, w, sub_re, add_re, sub_im, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
        I_re, I_im, re_ofNat, im_ofNat]
      norm_num
      constructor <;> linarith
    · simp [z]; linarith
    · simpa [w] using σ₁_lt_one

  have zero_over_box : RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w (holoOn2.mono sub)
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    rw [← mul_add, ← mul_add]
    apply congrArg (fun z : ℂ ↦ (1 : ℂ) / (2 * π * I) * z)
    apply verticalIntegral_split_three_finite
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa only [Function.comp_def] using
            this.continuousAt.comp (f := fun x : ℝ ↦ (σ₁ : ℂ) + x * I) (by fun_prop)
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' fun h ↦ ?_
          simpa [σ₁_pos.ne'] using congr_arg re h
        · fun_prop
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ =
        I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ -
        ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - (1 / (2 * π * I)) *
            VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    --- starting from now, we split the integral `I₃₇` into `I₃ σ₂ + I₅ σ₁ + I₇ σ₁` using `verticalIntegral_split_three_finite`
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

blueprint_comment /--
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box
$[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
-/
@[blueprint
  (title := "ZetaBoxEval")
  (statement := /--
  For all $\epsilon > 0$ sufficiently close to $0$, the rectangle integral over $[1-\delta,2] \times_{ℂ} [-T,T]$ of the integrand in
  $\psi_{\epsilon}$ is
  $$
  \frac{X^{1}}{1}\mathcal{M}(\widetilde{1_{\epsilon}})(1)
  = X(1+O(\epsilon))
  ,$$
  where the implicit constant is independent of $X$.
  -/)
  (proof := /-- Unfold the definitions and apply Lemma \ref{MellinOfSmooth1c}. -/)]
theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X - X‖ ≤ C * ε * X := by
  have := MellinOfSmooth1c ContDiffSmoothingF suppSmoothingF mass_one
  clear suppSmoothingF mass_one ContDiffSmoothingF
  rw[Asymptotics.isBigO_iff] at this
  obtain ⟨C, hC⟩ := this
  use C
  have εpos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), ε > 0 :=
    self_mem_nhdsWithin
  filter_upwards [hC, εpos] with ε hC εpos
  rw[id_eq, norm_of_nonneg (le_of_lt εpos)] at hC
  intro X Xnne
  nth_rw 2 [← one_mul (X : ℂ)]
  rw[← sub_mul, norm_mul, norm_real, norm_of_nonneg Xnne]
  exact mul_le_mul_of_nonneg_right hC Xnne

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
  -- First, simplify the complex norm
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [← normSq_eq_norm_sq, normSq_add_mul_I]
  -- Rewrite the integrand using this simplification
  simp_rw [h1]
  apply integrable_comp_mul_left_iff _ hx |>.mp
  have : (fun t ↦ (x ^ 2 + (x * t) ^ 2) ⁻¹) = (fun t ↦ (1 / x ^ 2) * (1 + t ^ 2) ⁻¹) := by
    ext
    field_simp
  rw [this]
  apply integrable_inv_one_add_sq.const_mul

theorem integral_evaluation (x : ℝ) (T : ℝ) (T_large : 3 < T) :
    ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have hT : 0 < T := by linarith
  rw [← integral_comp_neg_Ioi]
  calc
    _ ≤ ∫ t : ℝ in Ioi T, t ^ (-2 : ℝ) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards with t
        positivity
      · exact integrableOn_Ioi_rpow_of_lt (by norm_num) hT
      · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        intro t ht
        dsimp only
        calc
          _ ≤ (t ^ 2)⁻¹ := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, neg_sq]
            apply inv_anti₀ (sq_pos_of_pos (hT.trans ht))
            nlinarith [sq_nonneg x]
          _ = t ^ (-2 : ℝ) := by simp [Real.rpow_neg_ofNat]
    _ = T⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hT]
      norm_num [Real.rpow_neg_one]

blueprint_comment /--
It remains to estimate all of the integrals.
-/

blueprint_comment /--
This auxiliary lemma is useful for what follows.
-/
@[blueprint
  (title := "IBound-aux1")
  (statement := /--
  Given a natural number $k$ and a real number $X_0 > 0$, there exists $C \geq 1$ so that for all $X \geq X_0$,
  $$
  \log^k X \le C \cdot X.
  $$
  -/)
  (proof := /--
  We use the fact that $\log^k X / X$ goes to $0$ as $X \to \infty$.
  Then we use the extreme value theorem to find a constant $C$ that works for all $X \geq X_0$.
  -/)
  (latexEnv := "lemma")]
lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) {k : ℝ} (k_pos : 0 < k) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  -- When X is large, the ratio goes to 0.
  have hO : (fun X : ℝ ↦ Real.log X ^ k) =O[atTop] (fun X : ℝ ↦ X) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop k zero_lt_one).isBigO
  have hf : ContinuousOn (fun X : ℝ ↦ Real.log X ^ k) (Ici X₀) := by
    apply ContinuousOn.rpow (continuousOn_log.mono ?_) continuousOn_const
      (fun _ _ ↦ Or.inr k_pos)
    intro X hX
    exact ne_of_gt (X₀pos.trans_le hX)
  -- When X is small, use the extreme value theorem.
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_principal.mp
    (hO.isBigO_principal_Ici_of_continuousOn hf continuousOn_id
      (fun X hX ↦ norm_ne_zero_iff.2 (X₀pos.trans_le hX).ne'))
  refine ⟨max C 1, le_max_right _ _, fun X hX ↦ ?_⟩
  have hX0 : 0 < X := X₀pos.trans_le hX
  have hb := hC X hX
  rw [Real.norm_of_nonneg hX0.le] at hb
  exact (le_norm_self _).trans
    (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le))

def I1BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

@[blueprint
  (title := "I1Bound")
  (statement := /--
  We have that
  $$
  \left|I_{1}(\nu, \epsilon, X, T)\
  \right| \ll \frac{X\log X}{\epsilon T}
  .
  $$
  -/)
  (proof := /--
    Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_{1}(\nu, \epsilon, X, T)\right| =
  \left|
  \frac{1}{2\pi i} \int_{-\infty}^{-T}
  \left(
  \frac{-\zeta'}\zeta(\sigma_0 + t i)
  \right)
   \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
  X^{\sigma_0 + t i}
  \ i \ dt
  \right|
  $$
  By Theorem \ref{dlog_riemannZeta_bdd_on_vertical_lines},
  $\zeta'/\zeta (\sigma_0 + t i)$ is bounded by $\zeta'/\zeta(\sigma_0)$, and
  Theorem \ref{riemannZetaLogDerivResidue} gives $\ll 1/(\sigma_0-1)$ for the latter. This gives:
  $$
  \leq
  \frac{1}{2\pi}
  \left|
   \int_{-\infty}^{-T}
  C \log X\cdot
   \frac{C'}{\epsilon|\sigma_0 + t i|^2}
  X^{\sigma_0}
  \ dt
  \right|
  ,
  $$
  where we used Theorem \ref{MellinOfSmooth1b}.
  Continuing the calculation, we have
  $$
  \leq
  \log X \cdot
  C'' \frac{X^{\sigma_0}}{\epsilon}
  \int_{-\infty}^{-T}
  \frac{1}{t^2}
  \ dt
  \ \leq \
  C''' \frac{X\log X}{\epsilon T}
  ,
  $$
  where we used that $\sigma_0=1+1/\log X$, and $X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
  -/)
  (latexEnv := "lemma")]
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I1BoundGenProp SmoothingF := by

  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    obtain ⟨K', K'_pos, K'_bounds_zeta⟩ := triv_bound_zeta
    refine ⟨2 * (K' + 1), by positivity, fun t σ cond cond2 ↦ ?_⟩
    have T1 : 1 ≤ (σ - 1)⁻¹ := (one_le_inv₀ (sub_pos.mpr cond)).mpr (by linarith)
    have U := K'_bounds_zeta σ t cond
    rw [neg_div, norm_neg] at U
    nlinarith

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := fun t ↦ by simp [pts]

  have X_pos_triv : 0 < X := by linarith

  have pts_re_ge_one : 1 < pts_re := by
    simpa [pts_re] using Real.log_pos (by linarith : (1 : ℝ) < X)

  have pts_re_le_one : pts_re < 2 := by
    simp only [pts_re]
    linarith [inv_lt_one_of_one_lt₀ (logt_gt_one X_large.le)]

  have K_bounds_zeta_at_any_t :
      ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    have inve : (pts_re - 1)⁻¹ = Real.log X := by simp [pts_re]
    simpa only [inve] using K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by linarith

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := fun t ↦ (pts_re_triv t).ge

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 :=
    fun t ↦ (pts_re_triv t).le.trans pts_re_le_one.le

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
    intro t
    have hX : ‖(X : ℂ) ^ (pts t)‖ = X ^ pts_re := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos X_pos_triv, pts_re_triv]
    have hζ : ‖-ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
      simpa only [neg_div, norm_neg] using K_bounds_zeta_at_any_t t
    have hM := M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t)
      (triv_pts_up_bound t) eps eps_pos eps_less_one
    calc ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖ ^ 2)⁻¹) * X ^ pts_re := by
          simp only [f, SmoothedChebyshevIntegrand, norm_mul, hX]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hζ hM (norm_nonneg _) ((norm_nonneg _).trans hζ)) (by positivity)
      _ = _ := by ring

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large
    pts_re_ge_one pts_re_le_one.le suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    rw [rpow_one_add' X_pos_triv.le pts_re_pos.ne',
      rpow_inv_log X_pos_triv (by linarith), mul_comm]

  have pts_re_neq_zero : pts_re ≠ 0 := pts_re_pos.ne'

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono f_integrable.norm.restrict ?_ G
            exact ((poisson_kernel_integrable pts_re pts_re_neq_zero).const_mul
              ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)).restrict.congr
              (ae_of_all _ fun t ↦ by simp only [pts]; ring)
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ *
              ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              rw [← integral_const_mul]
              congr 1
              funext t
              ring
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ :=
              mul_le_mul_of_nonneg_left (integral_evaluation pts_re T T_large)
                (mul_nonneg (mul_nonneg (mul_nonneg (mul_pos K_is_pos M_is_pos).le
                  (Real.log_nonneg (by linarith))) (Real.rpow_nonneg X_pos_triv.le _))
                  (inv_nonneg.mpr eps_pos.le))
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 := mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

set_option backward.isDefEq.respectTransparency false in
lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I9BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

@[blueprint "I9Bound"
  (title := "I9Bound")
  (statement := /--
  We have that
  $$
  \left|I_{1}(\nu, \epsilon, X, T)\
  \right| \ll \frac{X}{\epsilon T}
  .
  $$
  -/)
  (proof := /--
  We deduce this from the corresponding bound for $I_1$, using the symmetry between $I_1$ and $I_9$.
  -/)
  (latexEnv := "lemma")]
theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I9BoundGenProp SmoothingF := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

def I2BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

@[blueprint "I2GenBound"
  (title := "I2GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound} we have that
  $$
  \left|I_2(\nu,\epsilon,X,T)\right|\ll\frac{X}{\epsilon T}.
  $$
  -/)
  (proof := /--
  Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_2(\nu, \epsilon, X, T, \sigma_1)\right|=
  \left|\frac{1}{2\pi i}\int_{\sigma_1}^{\sigma_0}
  \left(\frac{-\zeta'}\zeta(\sigma - T i) \right) \cdot
  \mathcal M(\widetilde 1_\epsilon)(\sigma - T i) \cdot
  X^{\sigma - T i}
   \ d\sigma
  \right|
  $$
  $$\leq
  \frac{1}{2\pi}
  \int_{\sigma_1}^{\sigma_0}
  C \cdot \log T ^{n_2}
  \frac{C'}{\epsilon|\sigma - T i|^2}
  X^{\sigma_0}
   \ d\sigma
   \leq
  C'' \cdot \frac{X\log T^{n_2}}{\epsilon T^2}
  ,
  $$
  where we used Theorems \ref{MellinOfSmooth1b}, the hypothesised bound on zeta and the fact that
  $X^\sigma \le X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
  Since $T>3$, we have $\log T^{n_2} \leq C''' T$.
  -/)
  (latexEnv := "lemma")]
lemma I2GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I2BoundGenProp n₁ SmoothingF A := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) n₂_pos)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdiv : 0 < A / Real.log T ^ n₁ ∧ A / Real.log T ^ n₁ ≤ A := by
    have h := Real.one_le_rpow (logt_gt_one T_gt.le).le n₁_pos.le
    exact ⟨div_pos A_in.1 (by linarith), div_le_self A_in.1.le h⟩
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have := inv_nonneg.mpr (Real.log_nonneg (by linarith : (1 : ℝ) ≤ X))
    simp only [σ₁]
    linarith [hdiv.1]
  have σ₁pos : 0 < σ₁ := by
    simp only [σ₁]
    linarith [hdiv.2, A_in.2]
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro σ hσ
        rw [Set.uIoc_of_le interval_length_nonneg] at hσ
        exact this σ hσ
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := by linarith [inv_lt_one_of_one_lt₀ (logt_gt_one X_gt.le)]
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ n₂ := has_bound σ (-T)
          (by simp only [abs_neg]; rw [abs_of_pos Tpos]; exact T_gt)
          (by unfold σ₁ at hσ; simp only [mem_Ioc, abs_neg, log_abs, mem_Ici,
            tsub_le_iff_right] at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ n₂ := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith [inv_lt_one_of_one_lt₀ (logt_gt_one X_gt.le)]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
        _ = C' * X / (ε * T) := by
          field_simp

@[blueprint
  (title := "I8I2")
  (statement := /--
  Symmetry between $I_2$ and $I_8$:
  $$
  I_8(\nu, \epsilon, X, T) = -\overline{I_2(\nu, \epsilon, X, T)}
  .
  $$
  -/)
  (proof := /-- This is a direct consequence of the definitions of $I_2$ and $I_8$. -/)
  (latexEnv := "lemma")]
lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    · simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    · exact lt_trans (by norm_num) T_gt

def I8BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

@[blueprint "I8GenBound"
  (title := "I8GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
  $$
  \left|I_8(\nu,\epsilon,X,T)\right|\ll\frac{X}{\epsilon T}.
  $$
  -/)
  (proof := /--
  We deduce this from the corresponding bound for $I_2$, using the symmetry between $I_2$ and $I_8$.
  -/)
  (latexEnv := "lemma")]
lemma I8GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I8BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, hC, i2Bound⟩ := I2GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  exact i2Bound

blueprint_comment /--
\label{Real.log_le_const_mul_rpow}
For all $0<c$ and $0<x$ we have that
  $$\log x\leq cx^{1/c}.$$

By \texttt{Real.log\_le\_sub\_one\_of\_pos} we know that $\log y\leq y-1$. If we set $y=x^{1/c}$ this becomes
  $$\frac{\log x}{c}\leq x^{1/c}-1.$$
  Multiplying through by $c$ we have
  $$\log x\leq cx^{1/c}-c\leq cx^{1/c}$$
  as desired.
-/

@[blueprint
  (title := "log-pow-over-xsq-integral-bounded")
  (statement := /--
  For every $0<n$ there exists a constant $C>0$ (depending on $n$) such that
  $$
  \int_3^T\frac{(\log x)^n}{x^2}dx < C
  $$
  -/)
  (proof := /--
  Using the previous lemma, we know for all $0<c$ and $0<x$ that
  $$(\log x)^n\leq (cx^{1/c})^n=c^nx^{n/c}.$$
  Now if we choose $c=2n$ then
  $$\frac{(\log x)^n}{x^2}\leq (2n)^nx^{-3/2}.$$
  This function is dominates the integrand and is integrable in $x$ by the $p$-test.
  -/)
  (latexEnv := "lemma")]
lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℝ, (n_pos : 0 < n) →
    ∃ C : ℝ, 0 < C ∧ ∀ T > 3, ∫ x in Ioo 3 T, (Real.log x) ^ n / x ^ 2 < C := by
  intro n n_pos
  set c : ℝ := 2 * n with cDef
  have cpos : 0 < c := by linarith
  set g : ℝ → ℝ := fun x => c ^ n * x ^ (-(3 / 2) : ℝ) with gDef
  have g_nonneg : ∀ x ∈ Ioi (3 : ℝ), 0 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have gInt_nonneg : 0 ≤ ∫ x in Ioi (3 : ℝ), g x := setIntegral_nonneg measurableSet_Ioi g_nonneg
  have g_integrable : IntegrableOn g (Ioi 3) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) _
  have g_mono : ∀ x ∈ Ioi (3 : ℝ), Real.log x ^ n / x ^ 2 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    have xpos : 0 < x := by linarith
    have logxPos : 0 < Real.log x := by
      rw [Real.log_pos_iff xpos.le]
      linarith
    have hlog : Real.log x ≤ c * x ^ (1 / c) := by
      simpa only [one_div, div_inv_eq_mul, mul_comm] using
        (Real.log_le_rpow_div xpos.le (inv_pos.mpr cpos))
    have logBnd := Real.rpow_le_rpow logxPos.le hlog n_pos.le
    rw [Real.mul_rpow cpos.le (Real.rpow_nonneg xpos.le _), ← Real.rpow_mul xpos.le, cDef] at logBnd
    field_simp at logBnd
    have : - ((3 : ℝ) / 2) = (1 / 2) - 2 := by norm_num
    simp only [cDef, gDef, this, Real.rpow_sub xpos, ← mul_div_assoc, rpow_ofNat]
    exact (div_le_div_iff_of_pos_right (sq_pos_iff.mpr (ne_of_gt xpos))).mpr logBnd
  refine ⟨1 + (∫ x in Ioi (3 : ℝ), g x), by linarith, fun T _ => ?_⟩
  calc
    _ ≤ ∫ (x : ℝ) in Ioo 3 T, g x := by
      refine setIntegral_mono_on (IntegrableOn.mono_set (ContinuousOn.integrableOn_Icc
        (ContinuousOn.div (ContinuousOn.rpow_const (ContinuousOn.log (continuousOn_id' _)
        (fun x hx ↦ ?_)) ?_) (ContinuousOn.fun_pow (continuousOn_id' _) _)
        (fun x hx ↦ pow_ne_zero _ ?_))) Ioo_subset_Icc_self)
        (IntegrableOn.mono_set g_integrable Ioo_subset_Ioi_self) measurableSet_Ioo
        (fun x hx ↦ g_mono x hx.1)
      · linarith [hx.1]
      · simp only [mem_Icc, ne_eq, log_eq_zero, not_or, n_pos.le, or_true, implies_true]
      · linarith [hx.1]
    _ ≤ ∫ (x : ℝ) in Ioi 3, g x := by
      refine setIntegral_mono_set g_integrable ?_ (Filter.Eventually.of_forall (fun _ ht ↦ ht.1))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx ↦ g_nonneg x hx)
  linarith

def I3BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

-- Slow

@[blueprint "I3GenBound"
  (title := "I3GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
  $$
  \left|I_3(\nu,\epsilon,X,T)\right|\ll\frac{X}{\epsilon}\, X^{-\frac{A}{(\log T)^{n_1}}}.
  $$
  -/)
  (proof := /--
  Unfold the definitions and apply the triangle inequality.
  $$
  \left|I_{3}(\nu, \epsilon, X, T, \sigma_1)\right| =
  \left|\frac{1}{2\pi i} \int_{-T}^3
  \left(\frac{-\zeta'}\zeta(\sigma_1 + t i) \right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
  X^{\sigma_1 + t i}
  \ i \ dt
  \right|
  $$
  $$\leq
  \frac{1}{2\pi}
  \int_{-T}^3
  C \cdot\log t^{n_2}
  \frac{C'}{\epsilon|\sigma_1 + t i|^2}
  X^{\sigma_1}
   \ dt
  ,
  $$
  where we used Theorems \ref{MellinOfSmooth1b} and the hypothesised bound on zeta.
  Now we estimate $X^{\sigma_1} = X \cdot X^{-A/ \log T^{n_1}}$, and the integral is absolutely bounded.
  -/)
  (latexEnv := "lemma")]
theorem I3GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I3BoundGenProp n₁ SmoothingF A := by
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded n₂ n₂_pos
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have Xpos := zero_lt_three.trans Xgt3
  have Tgt3' : -T < -3 := neg_lt_neg_iff.mpr Tgt3

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      exact ht.2.trans (by norm_num)
    rw [← Set.neg_mem_Ioo_iff, mem_Ioo] at ht
    rwa [this]

  have logt2gt1_bounds :
      ∀ t, t ∈ Set.Icc (-T) (-3) → Real.log |t| ^ n₂ > 1 := by
    intro t ht
    refine Real.one_lt_rpow ?_ n₂_pos
    have : |t| = -t := by
        refine abs_of_neg ?_
        exact ht.2.trans_lt (by norm_num)
    rw [this, Real.lt_log_iff_exp_lt (by linarith [ht.2])]
    linarith [ht.2, Real.exp_one_lt_d9]

  have Aoverlogt2gtAoverlogT2_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ n₁ > A / Real.log T ^ n₁ := by
    intro t ht
    refine div_lt_div_of_pos_left hA.1 ?_ ?_
    · exact zero_lt_one.trans <| Real.one_lt_rpow (logt_gt_one ht.1.le) n₁_pos
    · have h1 := log_lt_log (zero_lt_three.trans ht.1) ht.2
      have h2 := logt_gt_one ht.1.le
      have h3 : 0 ≤ Real.log |t| := zero_le_one.trans h2.le
      apply Real.rpow_lt_rpow h3 h1 n₁_pos

  have AoverlogT1in0half: A / Real.log T ^ n₁ ∈ Ioo 0 (1/2) := by
    have h := Real.one_lt_rpow (logt_gt_one Tgt3.le) n₁_pos
    exact ⟨div_pos hA.1 (by linarith), (div_lt_self hA.1 h).trans_le hA.2⟩

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT1in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT1in0half.2]

  have quotient_bound :
      ∀ t ∈ Ioo (-T) (-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ n₂ / t ^ 2 := by
    intro t ht
    have loght := logt2gt1_bounds t (Ioo_subset_Icc_self ht)
    have logpos : Real.log |t| ^ n₂ > 0 := zero_lt_one.trans loght
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := (le_add_iff_nonneg_left _).mpr <| sq_nonneg σ₁
    have denom_pos : 0 < t ^ 2 := by
      apply sq_pos_of_ne_zero
      rintro rfl
      norm_num [mem_Ioo] at ht
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) denom_pos
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have MellinBound : ∀ (t : ℝ),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤
        CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    refine CMhyp σ₁ σ₁pos _ ?_ ?_ _ εgt0 εlt1 <;> simp [σ₁lt1.le.trans one_le_two]

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ n₂ := by
    intro t tbounds
    apply hCζ
    · exact tbounds.1
    · unfold σ₁
      rw [mem_Ici, sub_le_sub_iff_left]
      exact (Aoverlogt2gtAoverlogT2_bounds t tbounds).le

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have bound_integral : ∀ t ∈ Ioo (-T) (-3), ‖f t‖ ≤ g t := by
    intro t ht
    unfold f

    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ n₂) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
        simp [norm_cpow_eq_rpow_re_of_pos Xpos]
      obtain ⟨ht_gt3, ht_ltT⟩ := t_bounds _ ht
      have logtgt1 : 1 < Real.log |t| := logt_gt_one ht_gt3.le
      have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
      have h𝓜 := MellinBound t
      rw[Xσ_bound]
      gcongr

    have : (Cζ * Real.log |t| ^ n₂) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f :
      ∫ (t : ℝ) in (-T)..(-3),
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑X ^ (↑σ₁ + ↑t * I) =
      ∫ (t : ℝ) in (-T)..(-3), f t := by
    simp only [f]
  rw[int_with_f]

  apply (norm_mul_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_I, one_mul]

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ ≤ ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · simp only [one_div, norm_inv]
      apply inv_le_one_of_one_le₀
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, pi_nonneg,
        abs_of_nonneg, norm_I, mul_one]
      apply one_le_mul_of_one_le_of_one_le one_le_two
      exact le_trans (by norm_num) pi_gt_three.le
  apply le_trans this

  apply le_trans (intervalIntegral.norm_integral_le_integral_norm Tgt3'.le)

  have ne_zero_of_mem_uIcc (x) (hx : x ∈ uIcc (-T) (-3)) : x ≠ 0 := by
    rintro rfl
    norm_num [mem_uIcc] at hx
    linarith

  have cont1 : ContinuousOn (fun t ↦ Real.log |t| ^ n₂) (uIcc (-T) (-3)) := by
    exact ContinuousOn.rpow (ContinuousOn.log continuous_abs.continuousOn (fun x hx ↦ abs_ne_zero.mpr (ne_zero_of_mem_uIcc x hx))) continuousOn_const (fun _ _ ↦ Or.inr n₂_pos)

  have g_cont : ContinuousOn g (uIcc (-T) (-3)) := by
    unfold g
    refine .mul ?_ continuousOn_const
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul cont1
    · fun_prop
    · intro x hx
      apply mul_ne_zero εgt0.ne'
      have : 0 < σ₁ ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos σ₁pos) (sq_nonneg x)
      simp only [Complex.sq_norm, normSq_add_mul_I, ne_eq, this.ne', not_false_eq_true]

  have int_normf_le_int_g: ∫ (t : ℝ) in (-T)..(-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in (-T)..(-3), g ↑t := by
    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · exact intervalIntegral.integral_mono_on_of_le_Ioo
        Tgt3'.le h_int g_cont.intervalIntegrable bound_integral
    · rw [intervalIntegral.integral_undef h_int]
      apply intervalIntegral.integral_nonneg Tgt3'.le
      intro t ht
      unfold g
      have := logt2gt1_bounds t ht
      positivity

  apply le_trans int_normf_le_int_g
  unfold g

  simp only [σ₁]

  have : X ^ (1 - A / Real.log T ^ n₁) = X * X ^ (- A / Real.log T ^ n₁) := by
    rw [sub_eq_add_neg, Real.rpow_add Xpos, Real.rpow_one, neg_div]

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]

    have bound : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      simp_rw [Complex.sq_norm, normSq_add_mul_I]

      have : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in (-T)..(-3), Real.log |t| ^ n₂ /  t ^ 2 := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo Tgt3'.le ?_ ?_ ?_
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' _
            · intro t ht
              have h1 : 0 < t ^ 2 := pow_two_pos_of_ne_zero (ne_zero_of_mem_uIcc t ht)
              have h2 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              exact (add_pos_of_pos_of_nonneg h2 h1.le).ne'
          apply cont.intervalIntegrable
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / t ^ 2) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' _
            · intro t ht
              exact pow_ne_zero 2 (ne_zero_of_mem_uIcc t ht)
          apply cont.intervalIntegrable
        · intro x hx
          exact quotient_bound x hx
      apply le_trans this
      rw [← intervalIntegral.integral_comp_neg]
      simp only [abs_neg, log_abs, even_two, Even.neg_pow]
      rw [intervalIntegral.integral_of_le Tgt3.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact (Cinthyp T Tgt3).le
    rw [mul_comm,
      ← mul_div_assoc, mul_one]

    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in (-T)..(-3), Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ n₁))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     simp only [log_abs]
     rw [← intervalIntegral.integral_const_mul]
     apply intervalIntegral.integral_congr
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ n₁)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · positivity

  apply le_trans this
  ring_nf
  field_simp
  rfl

lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I7BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

@[blueprint "I7GenBound"
  (title := "I7GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
  $$
  \left|I_7(\nu,\epsilon,X,T)\right|\ll\frac{X}{\epsilon}\, X^{-\frac{A}{(\log T)^{n_1}}}.
  $$
  -/)
  (proof := /--
  We deduce this from the corresponding bound for $I_3$, using the symmetry between $I_3$ and $I_7$.
  -/)
  (latexEnv := "lemma")]
theorem I7GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I7BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, Cpos, bound⟩ := I3GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

def I4BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

@[blueprint
  (title := "I4GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
  $$
  \left|I_4(\nu,\epsilon,X,\sigma_1,\sigma_2)\right|
    \ll\frac{X}{\epsilon}\,X^{-\frac{A}{(\log T)^{n_1}}}.
  $$
  -/)
  (proof := /--
    The analysis of $I_4$ is similar to that of $I_2$, (in Lemma \ref{I2Bound}) but even easier.
    Let $C$ be the sup of $-\zeta'/\zeta$ on the curve $\sigma_2 + 3 i$ to $1+ 3i$
    (this curve is compact, and away from the pole at $s=1$). Apply Theorem \ref{MellinOfSmooth1b}
    to get the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$. And $X^s$ is bounded
    by $X^{\sigma_1}=X \cdot X^{-A/ \log T^{n_1}}$. Putting these together gives the result.
  -/)
  (latexEnv := "lemma")]
lemma I4GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : n > 0) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I4BoundGenProp n SmoothingF A σ₂ := by
  have reOne : re 1 = 1 := rfl
  have imOne : im 1 = 0 := rfl
  have reThree : re 3 = 3 := rfl
  have imThree : im 3 = 0 := rfl

  unfold I4BoundGenProp I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnNorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[(by ring : σ₂ - σ₂ * x + x - I * 3 = σ₂ - σ₂ * x + (x - I * 3))] at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp (A ^ (n : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹)))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb ^ n := by
      have : rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ≤ Tlb := by
        unfold Tlb
        nth_rewrite 2 [max_comm]
        rw[max_left_comm]
        apply le_max_of_le_left (by rfl)
      rw[← Real.le_log_iff_exp_le] at this
      · have h1 : 0 ≤ (A / (1 - σ₂)) ^ (n : ℝ)⁻¹ := by apply Real.rpow_nonneg (by exact expr_nonneg)
        rw[← Real.rpow_le_rpow_iff h1 logTlb_nonneg n_pos] at this
        have h: ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ^ (n : ℝ) = A / (1 - σ₂) := by
          apply rpow_inv_rpow (by exact expr_nonneg)
          exact Ne.symm (Std.ne_of_lt n_pos)
        rw[h, div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact rpow_pos_of_pos (by exact logTlb_pos) _
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ^ n ≤ 1 - A / Real.log T ^ n := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · apply Real.rpow_pos_of_pos
        apply Real.log_pos
        linarith
      · exact Real.rpow_le_rpow logTlb_nonneg (log_le_log (by linarith) T_gt_Tlb.le) n_pos.le
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    apply Real.rpow_pos_of_pos
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T ^ n) / ε = 1 * (C * X * X ^ (-A / Real.log T ^ n) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_nonneg, Complex.norm_I, mul_one]
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T ^ n) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T ^ n) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T ^ n)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T ^ n) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]
                · rw[zero_mul, neg_zero, Real.exp_zero]
                  simp only [inv_one, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    ring_nf at xInIoc
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  · simp only [norm_nonneg]
  norm_num

lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]

def I6BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

@[blueprint "I6GenBound"
  (title := "I6GenBound")
  (statement := /--
  Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
  $$
  \left|I_6(\nu,\epsilon,X,\sigma_1,\sigma_2)\right|
    \ll\frac{X}{\epsilon}\,X^{-\frac{A}{(\log T)^{n_1}}}.
  $$
  -/)
  (proof := /--
  We deduce this from the corresponding bound for $I_4$, using the symmetry between $I_4$ and $I_6$.
  -/)
  (latexEnv := "lemma")]
lemma I6GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : 0 < n) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I6BoundGenProp n SmoothingF A σ₂ := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4GenBound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ n_pos hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

def I5BoundGenProp (SmoothingF : ℝ → ℝ) (σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε

@[blueprint
  (title := "I5Bound")
  (statement := /--
  We have that
  $$
  \left|I_5(\nu,\epsilon,X,\sigma_2)\right|\ll\frac{X^{\sigma_2}}{\epsilon}.
  $$
  -/)
  (proof := /--
  Here $\zeta'/\zeta$ is absolutely bounded on the compact interval $\sigma_2 + i [-3,3]$, and
  $X^s$ is bounded by $X^{\sigma_2}$. Using Theorem \ref{MellinOfSmooth1b} gives the bound
  $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$. Putting these together gives the result.
  -/)
  (latexEnv := "lemma")]
lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    I5BoundGenProp SmoothingF σ₂ := by
  unfold LogDerivZetaIsHoloSmall at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I5BoundGenProp I₅ SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  clear C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact zpow_two_nonneg t
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  -- Now want to apply the triangle inequality
  -- and bound everything trivially
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
    unfold C
    ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

def LogDerivZetaBoundedAndHoloGenProp (n₁ n₂ : ℝ) : Prop := ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound n₁ n₂ A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    DifferentiableOn ℂ (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ n₁) 2)  ×ℂ (Icc (-T) T) ) \ {1})

lemma LogDerivZetaBoundedAndHoloGen {n₁ n₂ : ℝ}
  (LogDerivZetaBndUnif : LogDerivZetaBndUnifGenProp n₁ n₂)
  (LogDerivZetaHolcLargeT : LogDerivZetaHolcLargeTGenProp n₁) :
  LogDerivZetaBoundedAndHoloGenProp n₁ n₂ := by
  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd⟩ := LogDerivZetaBndUnif
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · intro σ T hT hσ
    apply zeta_bnd _ _ hT
    apply mem_Ici.mpr (le_trans _ hσ)
    gcongr
    · bound
    · apply min_le_left
  · intro T hT
    apply (holo _ hT).mono
    intro s hs
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    refine ⟨?_, hs.1.1.2⟩
    apply le_trans _ hs.1.1.1
    gcongr
    · bound
    · apply min_le_right

lemma LogDerivZetaBoundedAndHolo99 : LogDerivZetaBoundedAndHoloGenProp 9 9 := by
  exact LogDerivZetaBoundedAndHoloGen LogDerivZetaBndUnif99 LogDerivZetaHolcLargeT9

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity
lemma x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
  have h : Tendsto (fun u : ℝ ↦ u * (1 - c * u ^ (B - 1))) atTop atTop := by
    refine tendsto_id.atTop_mul_pos one_pos ?_
    simpa using tendsto_const_nhds (x := (1 : ℝ)).sub
      ((tendsto_rpow_neg_atTop (y := 1 - B) (by linarith)).const_mul c)
  refine (tendsto_exp_atTop.comp (h.comp tendsto_log_atTop)).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlog := Real.log_pos hx
  have : Real.log x * (1 - c * (Real.log x ^ B / Real.log x)) =
      Real.log x + -c * Real.log x ^ B := by
    field_simp
    ring
  rw [comp_apply, comp_apply, Real.rpow_sub_one hlog.ne', this, Real.exp_add,
    Real.exp_log (by linarith)]

blueprint_comment /--
\section{MediumPNT}
-/

@[blueprint "GenStrengthPNT"
  (title := "GenStrengthPNT")
  (statement := /--
    Assuming a bound of the form of Definition \ref{LogDerivZetaHasBound}, we have that
    $$\sum_{n \leq x}\Lambda(n)=x+O(x\exp(-c(\log x)^{1/(1+n_1)})).$$
  -/)
  (proof := /--
    By Theorems \ref{SmoothedChebyshevPull1}, \ref{SmoothedChebyshevPull2},
    and \ref{SmoothedChebyshevClose} we have that
    $$\mathcal{M}(\tilde{1}_\varepsilon)(1)\,x^1+I_1-I_2+I_3-I_4+I_5+I_6+I_7+I_8+I_9
      =\psi(x)+O(\varepsilon x\log x).$$
    Applying Theorems \ref{I1Bound}, \ref{I2GenBound}, \ref{I3GenBound}, \ref{I4GenBound},
    \ref{I5Bound}, \ref{I6GenBound}, \ref{I7GenBound}, \ref{I8GenBound}, \ref{I9Bound},
    and \ref{MellinOfSmooth1c} we have
    $$\psi(x)=x+O(\varepsilon x)+O(\varepsilon x\log x)+O\left(\frac{X}{\varepsilon T}\right)+
      O\left(\frac{X\log X}{\varepsilon T}\right)+
      O\left(\frac{X}{\varepsilon}\,X^{-A/(\log T)^{n_1}}\right)+
      O\left(\frac{X^{\sigma_2}}{\varepsilon}\right).$$
    Balancing the error terms in $\varepsilon$ and $T$ completes the proof.
  -/)]
lemma GenStrengthPNT {n₁ n₂ : ℝ}
  (LogDerivZetaBoundedAndHolo : LogDerivZetaBoundedAndHoloGenProp n₁ n₂)
  (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) : ∃ c > 0,
  (ψ - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂, σ₂InIoo, holo2⟩ := LogDerivZetaHolcSmallT'
  obtain ⟨c_close, c_close_pos, h_close⟩ := SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨C_main, C_main_pos, h_main⟩ := (MellinOfSmooth1c ContDiff1ν ν_supp ν_massOne).exists_pos

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  σ₂InIoo
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc
  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 4
  have Apow_pos : 0 < A ^ ((1 : ℝ) / (1 + n₁)) := Real.rpow_pos_of_pos A_in_Ioc.1 _
  have cpos : 0 < c := by positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 2
  have c_εx_pos : 0 < c_εx := by positivity
  let c_Tx : ℝ := A ^ ((1 : ℝ) / (1 + n₁))
  have c_Tx_pos : 0 < c_Tx := Apow_pos

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))

  have one_div_succ_n₁_pos : 0 < (1 : ℝ) / (1 + n₁) := by
    simp only [one_div, inv_pos]
    linarith

  have one_div_succ_n₁_lt_one : (1 : ℝ) / (1 + n₁) < 1 := by
    rw [one_div, inv_lt_one₀ (one_div_pos.mp one_div_succ_n₁_pos)]
    norm_num [n₁_pos]

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁)) = -(c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx one_div_succ_n₁_lt_one
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) ^ n₁ := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂InIoo.2
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop n₁_pos).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp only [comp_apply, div_eq_mul_inv]
    · simp

  have eventually_main : ∀ᶠ (x : ℝ) in atTop,
      ‖𝓜 (fun t ↦ (Smooth1 ν (εx x) t : ℂ)) 1 - 1‖ ≤ C_main * εx x := by
    have : Tendsto εx atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨ex_to_zero, .of_forall fun x ↦ Real.exp_pos _⟩
    filter_upwards [this.eventually h_main.bound] with x hx
    rwa [id_eq, Real.norm_of_nonneg (by positivity)] at hx

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 10] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          exact Real.log_nonneg (logt_gt_one (by linarith)).le
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this,
        mul_assoc]

      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx
    have const1bnd : (A ^ ((1 : ℝ) / (1 + n₁)) / 4) < (A ^ ((1 : ℝ) / (1 + n₁)) / 2) := by
        linarith
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd one_div_succ_n₁_pos, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / (1 + n₁)
    have const2bnd : 0 < const2 := one_div_succ_n₁_pos
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / (1 + n₁))
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul, Real.log_exp, Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (n₁ : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le,
          div_eq_mul_inv]

        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos, const2_eq]
        field_simp
        ring_nf
      rw [div_mul_eq_div_div, neg_div, this (A_in_Ioc.1), mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div, this (y := Real.log x) logxpos, ← Real.exp_add]
      apply Real.exp_monotone
      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]
      gcongr
      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      positivity
    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ^ n₁) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / (1 + n₁) with const2eq
    set const1 := (A ^ const2 / 2) with const1eq
    set const1' := (A ^ const2 / 4) with const1'eq
    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]
    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt
    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ n₁)
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    grw [x_bnd]

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    have h := ((tendsto_rpow_neg_atTop (y := 1 - pow1) (by linarith)).comp
      tendsto_log_atTop).const_mul (const2 + const3)
    rw [mul_zero] at h
    filter_upwards [h.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < 1 - const1)),
      eventually_gt_atTop 3] with x hx x_gt
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    rw [comp_apply, neg_sub, Real.rpow_sub_one hlog.ne'] at hx
    have e : Real.log x * ((const2 + const3) * (Real.log x ^ pow1 / Real.log x)) =
        (const2 + const3) * Real.log x ^ pow1 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hx hlog.le]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / (1 + n₁)) / 4) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂InIoo.2 (A ^ ((1 : ℝ) / (1 + n₁)) / 2)
      (A ^ ((1 : ℝ) / (1 + n₁)) / 4) one_div_succ_n₁_lt_one] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf
    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ h_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_main event_logX_ge

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ n₁
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) ^ n₁ >= 1 - (1/2) / 1 ^ n₁ := by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo2a : DifferentiableOn ℂ (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith [mem_reProdIm.mp hs.1 |>.1.1, σ₂InIoo.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂InIoo.1 σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂ = (I₁ ν ε X T - I₂ ν ε T X σ₁) + (I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  have main : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ n₁) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

/-- *** Prime Number Theorem (Medium Strength) *** The `Chebyshev.psi` function is asymptotic to `x`. -/
@[blueprint
  (title := "MediumPNT")
  (statement := /--
    We have
    $$\sum_{n \leq x}\Lambda(n)=x+O(x \exp(-c(\log x)^{1/10})).$$
  -/)
  (proof := /--
    This follows as a corollary of Theorems \ref{GenStrengthPNT} and \ref{LogDerivZetaBnd}. -/)]
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have := GenStrengthPNT LogDerivZetaBoundedAndHolo99 (by linarith) (by linarith); ring_nf at this
  simpa only [gt_iff_lt, one_div, neg_mul] using this

/-- info: 'MediumPNT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MediumPNT
