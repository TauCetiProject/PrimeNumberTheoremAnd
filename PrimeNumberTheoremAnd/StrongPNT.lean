module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient

public import Architect
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Data.Rat.Cast.OfScientific
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.SimpleRing.Principal
public import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.LocalLogDeriv
public import TauCeti.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.JensenFormula
public import TauCeti.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Convex.SimplyConnected
public import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Local
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
public import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
public import TauCeti.NumberTheory.LSeries.ThreeFourOne
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import PrimeNumberTheoremAnd.MediumPNT
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity


@[expose] public section

open Nat Filter Topology Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "ψ" => Chebyshev.psi

--open scoped ArithmeticFunction



@[blueprint "SetOfZeros"
  (title := "SetOfZeros")
  (statement := /--
    Let $R>0$ and $f:\mathbb{C}\to\mathbb{C}$. Define the set of zeros
    $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
  -/)]
def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}



lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite :=
  finiteZeros.subset fun _ hz => ⟨hz.1.trans r_lt_one.le, hz.2⟩



open Classical

@[blueprint "ZerosBound"
  (title := "ZerosBound")
  (statement := /--
    Let $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
  -/)
   (proof := /--
    This is Jensen's formula, in the form of Mathlib's \texttt{AnalyticOnNhd.sum\_divisor\_le}:
    each zero $\rho$ with $|\rho|\leq r$ contributes $m_f(\rho)\log(R/|\rho|)\geq
    m_f(\rho)\log(R/r)$ to
    $$\frac{1}{2\pi}\int_0^{2\pi}\log|f(Re^{i\theta})|\,d\theta-\log|f(0)|\leq\log B.$$
    The divisor of $f$ on $\overline{\mathbb{D}_r}$ is exactly $m_f$ on $\mathcal{K}_f(r)$.
  -/)
  (latexEnv := "theorem")]
theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := r_pos.trans r_lt_R
  have hfr : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) r) :=
    hfAnalytic.mono (Metric.closedBall_subset_closedBall r_lt_one.le)
  let D := MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)
  let Z := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset
  have hsum : (∑ᶠ ρ, D ρ : ℤ) = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℤ) := by
    rw [finsum_eq_sum_of_support_subset (fun ρ => D ρ) (s := Z) (by
      intro ρ hρ
      have hball := D.supportWithinDomain hρ
      apply (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mpr
      refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hball, ?_⟩
      by_contra hzero
      exact hρ ((hfr ρ hball).divisor_apply_eq_zero hzero))]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hball : ρ ∈ Metric.closedBall (0 : ℂ) r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        ((finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ).1
    exact hfr.meromorphicOn.divisor_eq_analyticOrderNatAt (hfr ρ hball) hball
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := r) (R := R) (M := B)
    (by simpa only [abs_of_pos r_pos] using r_pos)
    (by simpa only [abs_of_pos r_pos, abs_of_pos R_pos] using r_lt_R)
    (by simpa only [hf0_eq_one, norm_one] using fz_bound 0 (by simpa only [norm_zero] using R_pos.le))
    (by simpa only [abs_of_pos R_pos] using
      hfAnalytic.mono (Metric.closedBall_subset_closedBall R_lt_one.le))
    (by simp only [hf0_eq_one, ne_eq, one_ne_zero, not_false_eq_true])
    (fun z hz => fz_bound z (by simpa only [abs_of_pos R_pos, Metric.mem_closedBall,
      dist_zero_right] using (Metric.sphere_subset_closedBall hz)))
  rw [abs_of_pos r_pos] at hJ
  simp only [hf0_eq_one, norm_one, div_one] at hJ
  dsimp only [D] at hsum
  rw [hsum] at hJ
  simpa only [Int.cast_sum, Int.cast_natCast, Nat.cast_sum, one_div, inv_mul_eq_div] using hJ


attribute [blueprint "FinalBound"
  (title := "FinalBound")
  (statement := /--
    Let $0<r<R$ and let $f$ be analytic on $\overline{\mathbb{D}_R(z_0)}$ with
    $|f(w)|\leq M\,|f(z_0)|$ for all $|w-z_0|=R$. Then for every $z$ with
    $d=|z-z_0|<r$ and $f(z)\neq 0$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{|\rho-z_0|\leq r}\frac{m_f(\rho)}{z-\rho}\right|
      \leq\left(\frac{4(r+d)}{(r-d)^2}+\frac{r}{(R^2-rd)\,\log(R/r)}\right)\log M,$$
    where the sum runs over the zeros $\rho$ of $f$, counted with multiplicity $m_f(\rho)$.
  -/)
  (proof := /--
    Divide $f$ by $\prod_\rho (z-\rho)^{m_f(\rho)}$ and multiply by the reflected factors
    $\prod_\rho (R^2-\overline{(\rho-z_0)}(z-z_0))^{m_f(\rho)}$ (a Blaschke product). The
    resulting function $B$ has no zeros in $\overline{\mathbb{D}_r(z_0)}$ and satisfies
    $|B|\leq M|B(z_0)|$, so the Borel--Carath\'eodory inequality applied to $\log B$ bounds
    $|B'/B|$ on $\overline{\mathbb{D}_d(z_0)}$ by the first term. The logarithmic derivatives of the
    reflected factors contribute at most $r/(R^2-rd)$ per zero, and Jensen's formula
    (Theorem \ref{ZerosBound}) bounds the number of zeros by $\log M/\log(R/r)$.
  -/)
  (proofUses := ["ZerosBound"])
  (latexEnv := "theorem")]
  AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le


blueprint_comment /--
\label{ZetaFixedLowerBound}
For all $t\in\mathbb{R}$ one has
    $$|\zeta(3/2+it)|\geq\frac{\zeta(3)}{\zeta(3/2)}.$$

From the Euler product expansion of $\zeta$, we have that for $\Re s>1$
    $$\zeta(s)=\prod_p\frac{1}{1-p^{-s}}.$$
    Thus, we have that
    $$\frac{\zeta(2s)}{\zeta(s)}=\prod_p\frac{1-p^{-s}}{1-p^{-2s}}=\prod_p\frac{1}{1+p^{-s}}.$$
    Now note that $|1-p^{-(3/2+it)}|\leq 1+|p^{-(3/2+it)}|=1+p^{-3/2}$. Thus,
    $$|\zeta(3/2+it)|=\prod_p\frac{1}{|1-p^{-(3/2+it)}|}
      \geq\prod_p\frac{1}{1+p^{-3/2}}=\frac{\zeta(3)}{\zeta(3/2)}$$
    for all $t\in\mathbb{R}$ as desired.
-/

@[blueprint "GlobalBound"
  (title := "GlobalBound")
  (statement := /--
    For all $s\in\mathbb{C}$ with $|s|\leq 1$ and $t\in\mathbb{R}$ with $|t|\geq 2$, we have that
    $$|\zeta(s+3/2+it)|\leq 7+2\,|t|.$$
  -/)
  (proof := /--
    Let $z=s+3/2+it$. Since $|s|\leq 1$ we know that $1/2\leq\Re z$, and since
    $|t|\geq 2$, we know $|z-1|\geq|\Im z|\geq 1$. Tau Ceti's
    \texttt{TauCeti.norm\_riemannZeta\_le\_linear} gives $|\zeta(z)|\leq 4+|t|$ on this disc.
    It comes from the first-order Euler--Maclaurin bound
    $$|\zeta(z)|\leq\frac12+\frac{1}{|z-1|}+\frac{|z|}{2\Re z}\leq\frac32+|z|
      \leq\frac32+1+\frac32+|t|.$$
    In particular $|\zeta(s+3/2+it)|\leq 4+|t|\leq 7+2\,|t|$.
  -/)]
theorem GlobalBound
    {s : ℂ} (hs : ‖s‖ ≤ 1) {t : ℝ} (ht : |t| ≥ 2) :
    ‖ζ (s + 3 / 2 + I * t)‖ ≤ 7 + 2 * |t| := by
  have hz : s + 3 / 2 + I * t ∈ Metric.closedBall (3 / 2 + t * I : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    convert hs using 2
    ring
  linarith [TauCeti.norm_riemannZeta_le_linear ht hz, abs_nonneg t]



@[blueprint "norm_zeta_strict_mono_ofReal"
  (title := "norm-zeta-strict-mono-ofReal")
  (statement := /--
    If $a,b\in\mathbb{R}$ with $1<b<a$, then
    $$|\zeta(a)|<|\zeta(b)|.$$
  -/)
  (proof := /--
    Expand out $\zeta$ as a summation (we can do this as we are in the region of convergence) and
    ignore the norm as every term is positive and real. Comparing term by term proves the result.
  -/)]
lemma norm_zeta_strict_mono_ofReal {a b : ℝ} (hb : 1 < b) (hab : b < a) :
    ‖ζ a‖ < ‖ζ b‖ := by
  open scoped ComplexOrder in
  rw [← Complex.re_eq_norm.2 (riemannZeta_pos_of_one_lt (hb.trans hab)).le,
    ← Complex.re_eq_norm.2 (riemannZeta_pos_of_one_lt hb).le]
  exact TauCeti.strictAntiOn_riemannZeta_re hb (hb.trans hab) hab



attribute [blueprint "LogDerivZetaFinalBound"
  (title := "LogDerivZetaFinalBound")
  (statement := /--
    Let $\sigma_0>1$ and $0<r<r'$. There is a constant $C$ such that for all $s_0$ with
    $\Re s_0=\sigma_0$ and all $s\neq 1$ with $|s-s_0|\leq r$ and $\zeta(s)\neq 0$,
    $$\left|\frac{\zeta'}{\zeta}(s)+\frac{1}{s-1}
      -\sum_{|\rho-s_0|\leq r'}\frac{m_\zeta(\rho)}{s-\rho}\right|
      \leq C\log(|\Im s_0|+2),$$
    where the sum runs over the zeros $\rho$ of $\zeta$, counted with multiplicity
    $m_\zeta(\rho)$.
  -/)
  (proof := /--
    Apply Theorem \ref{FinalBound} to the entire function $(s-1)\zeta(s)$ on discs centred at
    $s_0$ of radii $r'$ and $r'+1$. Its size on the larger disc is at most a power of
    $|\Im s_0|+2$, and at the centre $|(s_0-1)\zeta(s_0)|\geq(\sigma_0-1)
    \exp(-\zeta(\sigma_0))$ by the Euler product, so $\log M\ll\log(|\Im s_0|+2)$. The
    logarithmic derivative of $(s-1)\zeta(s)$ is $\frac{\zeta'}{\zeta}(s)+\frac{1}{s-1}$
    (compare Theorem \ref{riemannZetaLogDerivResidue}).
  -/)
  (proofUses := ["FinalBound", "riemannZetaLogDerivResidue"])]
  TauCeti.riemannZeta_local_logDeriv


@[blueprint "ZetaShiftFiniteZeros"
  (title := "ZetaShiftFiniteZeros")
  (statement := /--
    For all $|t|\geq 2$, if $f(z)=\zeta(z+3/2+it)$, then $f(z)$ has a finite number of zeros in
    $\overline{\mathbb{D}_1}$.
  -/)
  (proof := /--
    If we suppose the opposite, i.e. that there are an infinite number of zeros in this region, then
    $f\equiv 0$ by the identity theorem. This is a contradiction, so the statement must be true.
  -/)]
lemma ZetaShiftFiniteZeros {t : ℝ} (_ht : |t| ≥ 2)
    {f : ℂ → ℂ} (hf : f = fun z ↦ ζ (z + 3 / 2 + I * t)) : (SetOfZeros 1 f).Finite := by
  refine (((isCompact_closedBall (3 / 2 + I * t) 1).inter_riemannZetaZeros_finite).preimage
    (add_left_injective (3 / 2 + I * t)).injOn).subset fun z hz => ?_
  subst hf
  exact ⟨by simpa [dist_eq_norm] using hz.1, mem_riemannZetaZeros.2 (by simpa [add_assoc] using hz.2)⟩



@[blueprint "ZeroWindow"
  (title := "ZeroWindow")
  (statement := /--
    Let $\mathcal{Z}_t=\{\rho\in\mathbb{C}:\zeta(\rho)=0,\,|\rho-(3/2+it)|\leq 3/4\}$.
  -/)]
def ZeroWindow (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ ‖ρ - (3 / 2 + I * t)‖ ≤ 3 / 4}



/-- Tau Ceti's local expansion `TauCeti.riemannZeta_local_logDeriv` of `ζ'/ζ` about `3/2 + it`,
with the zeros of the window `ZeroWindow t`. -/
private lemma zeroWindow_logDeriv_bound :
    ∃ C > 0, ∀ (t : ℝ), |t| ≥ 2 → ∀ (z : ℂ), z.im = t → ‖z - (3 / 2 + I * t)‖ ≤ 5 / 8 →
      ζ z ≠ 0 → ∀ (finiteZeros : (ZeroWindow t).Finite),
        ‖ζ' z / ζ z - ∑ ρ ∈ finiteZeros.toFinset, analyticOrderNatAt ζ ρ / (z - ρ)‖ ≤
          C * Real.log |t| := by
  obtain ⟨C, hC⟩ := TauCeti.riemannZeta_local_logDeriv (σ₀ := 3 / 2) (r := 5 / 8) (r' := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨2 * |C| + 2, by positivity, fun t ht z hzt hz hζ hfin ↦ ?_⟩
  have hz1 : z ≠ 1 := by rintro rfl; simp only [one_im] at hzt; rw [← hzt] at ht; norm_num at ht
  have h := hC (3 / 2 + I * t) z (by simp) hz hz1 hζ
  rw [finsum_subtype_eq_finsum_cond (fun w : ℂ ↦ ‖w - (3 / 2 + I * t)‖ ≤ 3 / 4 ∧ ζ w = 0)
    (f := fun ρ ↦ ((analyticOrderAt ζ ρ).toNat : ℂ) / (z - ρ))] at h
  have hsum : ∑ᶠ (ρ : ℂ) (_ : ‖ρ - (3 / 2 + I * t)‖ ≤ 3 / 4 ∧ ζ ρ = 0),
      ((analyticOrderAt ζ ρ).toNat : ℂ) / (z - ρ) =
      ∑ᶠ ρ ∈ ZeroWindow t, (analyticOrderNatAt ζ ρ : ℂ) / (z - ρ) :=
    finsum_congr fun ρ ↦ by rw [ZeroWindow, mem_ofPred_eq, and_comm]; rfl
  have hinv : ‖1 / (z - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    refine le_trans ?_ (abs_im_le_norm _)
    simp only [sub_im, hzt, one_im, sub_zero]; linarith
  have hlog : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
    have h := Real.log_le_log (by positivity) (by nlinarith : |t| + 2 ≤ |t| ^ 2)
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hlog2 : 1 / 2 ≤ Real.log |t| :=
    (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) ht)
  rw [hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, show (3 / 2 + I * t : ℂ).im = t by simp] at h
  calc _ = ‖(ζ' z / ζ z + 1 / (z - 1) - ∑ ρ ∈ hfin.toFinset,
        (analyticOrderNatAt ζ ρ : ℂ) / (z - ρ)) - 1 / (z - 1)‖ := by ring_nf
    _ ≤ C * Real.log (|t| + 2) + 1 := (norm_sub_le _ _).trans (add_le_add h hinv)
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
      have h2 := mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.log_nonneg (by linarith [abs_nonneg t] : (1 : ℝ) ≤ |t| + 2))
      nlinarith

/- API for analyticOrderNatAt -/

attribute [blueprint "ShiftTwoBound"
  (title := "ShiftTwoBound")
  (statement := /--
    There is a constant $A>0$ such that for all $s$ with $\Re s\geq 1$ and $|\Im s|\geq 1$,
    $$-\Re \left(\frac{\zeta'}{\zeta}(s)\right)\leq A\log(|\Im s|+3).$$
  -/)
  (proof := /--
    For $1\leq\Re s\leq 9/8$, apply Landau's local lemma (the one-sided form of
    Theorem \ref{FinalBound}) to $\zeta$ on the disc of radius $1/2$ about $9/8+i\Im s$, on
    which $|\zeta|\ll|\Im s|$ and at whose centre $\zeta$ is bounded below by the Euler product.
    Each zero $\rho$ near $s$ has $\Re\rho\leq 1\leq\Re s$, so
    $\Re\frac{1}{s-\rho}\geq 0$, and dropping these terms only increases
    $-\Re\frac{\zeta'}{\zeta}(s)$. For $\Re s\geq 9/8$, compare the Dirichlet series
    $-\frac{\zeta'}{\zeta}(s)=\sum_n\Lambda(n)n^{-s}$ termwise with its value at $9/8$.
  -/)
  (proofUses := ["FinalBound", "LogDerivativeDirichlet"])]
  TauCeti.exists_neg_re_logDeriv_riemannZeta_le

attribute [blueprint "ShiftOneBound"
  (title := "ShiftOneBound")
  (statement := /--
    There is a constant $A>0$ such that for all $\sigma\geq 1$ and every zero
    $\rho$ of $\zeta$ with $|\Im\rho|\geq 1$,
    $$-\Re \left(\frac{\zeta'}{\zeta}(\sigma+i\Im\rho)\right)
      \leq -\frac{1}{\sigma-\Re\rho}+A\log(|\Im\rho|+3).$$
  -/)
  (proof := /--
    As in Lemma \ref{ShiftTwoBound}, apply Landau's local lemma about $9/8+i\Im\rho$, now
    keeping the term of the zero $\rho$, whose real part is
    $\frac{m_\zeta(\rho)}{\sigma-\Re\rho}\geq\frac{1}{\sigma-\Re\rho}$; the remaining
    terms have nonnegative real part and are dropped. When $\sigma>9/8$ or $\Re\rho<7/8$, the
    term $\frac{1}{\sigma-\Re\rho}$ is bounded and Lemma \ref{ShiftTwoBound} suffices.
  -/)
  (proofUses := ["FinalBound", "ShiftTwoBound"])]
  TauCeti.exists_neg_re_logDeriv_riemannZeta_add_sub_inv_le

attribute [blueprint "ShiftZeroBound"
  (title := "ShiftZeroBound")
  (statement := /--
    There is a constant $C\geq 0$ such that for all $\delta\in(0,1]$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\frac{1}{\delta}+C.$$
  -/)
  (proof := /--
    From Theorem \ref{riemannZetaLogDerivResidue} we know that
    $$-\frac{\zeta'}{\zeta}(s)=\frac{1}{s-1}+O(1).$$
    Changing variables $s\mapsto 1+\delta$ and taking real parts gives the claim.
  -/)
  (proofUses := ["riemannZetaLogDerivResidue"])]
  TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le


attribute [blueprint "vonMangoldtLSeriesSummable"
  (title := "vonMangoldtLSeriesSummable")
  (statement := /--
    The series
    $$\sum_{n=1}^\infty\frac{\Lambda(n)}{n^s}$$
    converges when $1<\mathfrak{R}(s)$.
  -/)
  (proof := /--
    We know that $\Lambda(n)$ is $O(n^\varepsilon)$ since it is bounded above by $\log(n)$. Thus,
    $$\left|\sum_{n=1}^\infty\frac{\Lambda(n)}{n^s}\right|\leq
      \sum_{n=1}^\infty\left|\frac{\Lambda(n)}{n^s}\right|\ll
      \sum_{n=1}^\infty\frac{1}{n^{\mathfrak{R}(s)-\varepsilon}}.$$
    Since $\varepsilon$ can be arbitrarily small, we know the left hand side converges by the
    $p$-test.
  -/)]
  ArithmeticFunction.LSeriesSummable_vonMangoldt


@[blueprint "ZeroWindowFinite"
  (title := "ZeroWindowFinite")
  (statement := /--
    For all $|t|\geq 2$, $\mathcal{Z}(t)$ contains a finite number of points.
  -/)
  (proof := /--
    If we suppose the opposite, i.e. that there are an infinite number of zeta zeros in this region,
    then $\zeta\equiv 0$ by the identity theorem. This is a contradiction, so the statement must be
    true.
  -/)]
lemma ZeroWindowFinite {t : ℝ} (_ht : |t| ≥ 2) : (ZeroWindow t).Finite :=
  ((isCompact_closedBall (3 / 2 + I * t) (3 / 4)).inter_riemannZetaZeros_finite).subset
    fun _ h => ⟨by simpa [dist_eq_norm] using h.2, h.1⟩



@[blueprint "ZeroInequality"
  (title := "ZeroInequality")
  (proofUses := ["LogDerivativeDirichlet", "ShiftZeroBound", "ShiftOneBound", "ShiftTwoBound"])
  (statement := /--
    There exists a constant $0 < E<1/14$ such that for all $\rho=\sigma+it$ with $\zeta(\rho)=0$
    and $|t|\geq 2$, one has
    $$\sigma\leq 1-\frac{E}{\log|t|}.$$
  -/)
  (proof := /--
    This is immediate from the de la Vallée Poussin zero-free region
    \texttt{TauCeti.LFunctions.riemannZeta\_zeroFreeRegion}: there is $c>0$ such that
    $\zeta(s)\neq 0$ whenever $s\neq 1$ and $\Re s\geq 1-c/\log(|\Im s|+3)$. Since
    $\log(|t|+3)\leq 3\log|t|$ for $|t|\geq 2$, we may take $E=\min(1/15,c/3)$.

    The zero-free region is proved by the classical 3-4-1 argument. From
    Theorem \ref{LogDerivativeDirichlet}, when $\Re s>1$ we have
    $-\frac{\zeta'}{\zeta}(s)=\sum_{1\leq n}\Lambda(n)n^{-s}$. Thus,
    \begin{align*}
        -3\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)&
            -4\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
            -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right) \\
        &\qquad\qquad\qquad=\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}
            \left(3+4\cos(t\log n)+\cos(2t\log n)\right)\geq 0,
    \end{align*}
    since $3+4\cos\theta+\cos 2\theta=2\,(1+\cos\theta)^2\geq 0$. If $\rho=\beta+it$ is a
    zero with $|t|\geq 1$, Lemmas \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and
    \ref{ShiftTwoBound} bound the left hand side, so
    $$0\leq\frac{3}{\delta}+3A-\frac{4}{1+\delta-\beta}+D\log(|t|+3)$$
    for constants $A$ and $D$. Choosing $\delta$ a small multiple of $1/\log(|t|+3)$ gives
    $\beta\leq 1-c/\log(|t|+3)$. Zeros with $|t|<1$ are excluded by compactness and the
    nonvanishing of $\zeta$ on $\Re s\geq 1$.
  -/)]
theorem ZeroInequality : ∃ (E : ℝ), E ∈ Ioo (0 : ℝ) (1 / 14 : ℝ) ∧
    ∀ (ρ : ℂ), ζ ρ = 0 →
      ∀ (σ : ℝ), σ = ρ.re →
        ∀ (t : ℝ), t = ρ.im → |t| ≥ 2 →
          σ ≤ 1 - E / log |t| := by
  obtain ⟨c, hc, h⟩ := TauCeti.LFunctions.riemannZeta_zeroFreeRegion
  refine ⟨min (1 / 15) (c / 3), ⟨by positivity, by linarith [min_le_left (1 / 15 : ℝ) (c / 3)]⟩,
    fun ρ hρ σ hσ t ht ht2 ↦ ?_⟩
  subst hσ ht
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at ht2; linarith
  have hlt := lt_of_not_ge fun hle ↦ h ρ hρ1 hle hρ
  have hL : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
  have h2 : Real.log (|ρ.im| + 3) ≤ 3 * Real.log |ρ.im| := by
    rw [← Real.log_rpow (by linarith)]; exact Real.log_le_log (by linarith) (by norm_cast; nlinarith [mul_nonneg (mul_nonneg (abs_nonneg ρ.im) (sub_nonneg.2 ht2)) (by linarith : (0:ℝ) ≤ |ρ.im| + 2)])
  have h3 : min (1 / 15) (c / 3) / Real.log |ρ.im| ≤ c / Real.log (|ρ.im| + 3) := calc
    _ ≤ c / (3 * Real.log |ρ.im|) := by rw [← div_div]; gcongr; exact min_le_right _ _
    _ ≤ _ := div_le_div_of_nonneg_left hc.le (Real.log_pos (by linarith)) h2
  linarith



noncomputable def E : ℝ := ZeroInequality.choose
lemma EinIoo : E ∈ Ioo (0 : ℝ) (1 / 14 : ℝ) := ZeroInequality.choose_spec.1
theorem ZeroInequalitySpec : ∀ (ρ : ℂ), ζ ρ = 0 →
    ∀ (σ : ℝ), σ = ρ.re →
      ∀ (t : ℝ), t = ρ.im → |t| ≥ 2 →
        σ ≤ 1 - E / log |t| := ZeroInequality.choose_spec.2



@[blueprint "DeltaT"
  (title := "DeltaT")
  (statement := /--
    Let $\delta_t=E/\log|t|$ where $E$ is the constant coming from Theorem \ref{ZeroInequality}.
  -/)]
noncomputable def DeltaT (t : ℝ) : ℝ := E / log |t|



@[blueprint "DeltaRange"
  (title := "DeltaRange")
  (statement := /--
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ we have that $$\delta_t<1/9.$$
  -/)
  (proof := /--
    Note that $\delta_t=E/\log|t|$ where $E<1/14$ is the constant from
    Theorem \ref{ZeroInequality}. Thus,
    $$\delta_t=\frac{E}{\log|t|}\leq\frac{1}{14\,\log2}<\frac{1}{9}.$$
  -/)]
lemma DeltaRange : ∀ (t : ℝ),
    |t| ≥ 2 →
      DeltaT t < (1 : ℝ) / 9 := by
  intro t ht
  rw [DeltaT, div_lt_div_iff₀ (Real.log_pos (by linarith)) (ofNat_pos'), one_mul]
  exact lt_of_lt_of_le (by linarith [EinIoo.2, Real.log_two_gt_d9]) (Real.log_le_log zero_lt_two ht)



@[blueprint "SumBoundII"
  (title := "SumBoundII")
  (proofUses := ["LogDerivZetaFinalBound", "ZeroInequality"])
  (statement := /--
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ and $z=\sigma+it$
    where $1-\delta_t/3\leq\sigma\leq 3/2$, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
  -/)
  (proof := /--
    By Lemma \ref{DeltaRange} we have that
    $$-29/54<-1/2-\delta_t/3\leq\sigma-3/2\leq0,$$
    so $|z-(3/2+it)|\leq 5/8$. Additionally, $\zeta(z)\neq 0$, since $z$ lies in the zero-free
    region given by Lemma \ref{ZeroInequality} ($\sigma\geq 1-\delta_t/3> 1-\delta_t$).
    We apply Theorem \ref{LogDerivZetaFinalBound} with $s_0=3/2+it$, $r=5/8$ and $r'=3/4$.
    The zeros $\rho$ with $|\rho-s_0|\leq 3/4$ are exactly those of $\mathcal{Z}_t$, so
    $$\left|\frac{\zeta'}{\zeta}(z)+\frac{1}{z-1}
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log(|t|+2).$$
    Finally $|1/(z-1)|\leq 1/|t|\leq 1$ and $\log(|t|+2)\leq 2\log|t|$.
  -/)]
lemma SumBoundII :
    ∃ (C : ℝ), C > 0 ∧
      ∀ (t : ℝ), |t| ≥ 2 →
        ∀ (z : ℂ), (hzIm : t = z.im) → (hzRe : z.re ∈ Icc (1 - DeltaT t / 3) (3 / 2)) →
          ∀ (finiteZeros : (ZeroWindow t).Finite),
    ‖ζ' (z) / ζ (z) - ∑ ρ ∈ finiteZeros.toFinset,
      analyticOrderNatAt ζ ρ / (z - ρ)‖ ≤ C * Real.log |t| := by
  obtain ⟨C, hC, h⟩ := zeroWindow_logDeriv_bound
  refine ⟨C, hC, fun t ht z hzIm hzRe finiteZeros ↦
    h t ht z hzIm.symm ?_ (fun hζ ↦ ?_) finiteZeros⟩
  · rw [show z - (3 / 2 + I * t) = ((z.re - 3 / 2 : ℝ) : ℂ) by
      apply Complex.ext <;> simp [hzIm], norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hzRe.1, hzRe.2, DeltaRange t ht]
  · have hΔ : DeltaT t / 3 < E / Real.log |t| :=
      div_lt_self (div_pos EinIoo.1 (Real.log_pos (by linarith))) (by norm_num)
    linarith [hzRe.1, ZeroInequalitySpec z hζ z.re rfl t hzIm ht]



@[blueprint "GapSize"
  (title := "GapSize")
  (statement := /--
    Let $t\in\mathbb{R}$ with $|t|\geq 3$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$.
   Additionally, let $\rho\in\mathcal{Z}_t$. Then we have that
   $$|z-\rho|\geq\delta_t/6.$$
  -/)
  (proof := /--
    Let $\rho=\sigma'+it'$ and note that since $\rho\in\mathcal{Z}_t$, we have $t'\in(t-3/4,t+3/4)$.
    Thus, if $t>1$ we have
    $$\log|t'|\leq\log|t+3/4|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    And otherwise if $t<-1$ we have
    $$\log|t'|\leq\log|t-3/4|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    So by taking reciprocals and multiplying through by a constant we have
    that $\delta_t\leq2\delta_{t'}$. Now note that since $\rho\in\mathcal{Z}_t$
    we know that $\sigma'\leq 1-\delta_{t'}$ by Theorem \ref{ZeroInequality}
    (here we use the fact that $|t|\geq 3$ to give us that $|t'|\geq 2$). Thus,
    $$\delta_t/6\leq\delta_{t'}-\delta_t/3
      =1-\delta_t/3-(1-\delta_{t'})\leq\sigma-\sigma'\leq|z-\rho|.$$
  -/)]
lemma GapSize (t : ℝ) (ht : |t| ≥ 3)
    (z : ℂ) (hzRe : z.re ∈ Icc (1 - DeltaT t / 3) (3 / 2))
    (ρ : ℂ) (hρ : ρ ∈ ZeroWindow t) :
    ‖z - ρ‖ ≥ DeltaT t / 6 := by
  simp only [ZeroWindow, mem_ofPred_eq] at hρ
  have := abs_sub_abs_le_abs_sub t ρ.im; rw [abs_sub_comm] at this
  have ρImDiffBound : |ρ.im - t| ≤ 3 / 4 := by
    have h := Complex.abs_im_le_norm (ρ - (3 / 2 + I * t))
    simp only [sub_im, add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, I_re, ofReal_im, mul_zero,
      I_im, ofReal_re, one_mul, zero_add] at h
    exact h.trans hρ.2
  have ρImAbsUpperBound : Real.log |ρ.im| ≤ 2 * Real.log |t| := by
    have moveTwo : Real.log (2 * |t|) ≤ 2 * Real.log |t| := by
      rw [← Real.log_rpow (by linarith)]
      have := mul_le_mul_of_nonneg_right ht (abs_nonneg t); rw [← sq, ← Real.rpow_two] at this
      exact Real.log_le_log (by linarith) (by linarith)
    refine le_trans (Real.log_le_log (by linarith) ?_) moveTwo
    linarith [abs_sub_abs_le_abs_sub ρ.im t]
  have deltaRelation : DeltaT t ≤ 2 * (DeltaT ρ.im) := by
    simp only [DeltaT, mul_div, mul_comm]
    rw [div_le_div_iff₀ (Real.log_pos (by linarith)) (Real.log_pos (by linarith)), mul_assoc]
    nlinarith [EinIoo.1, EinIoo.2]
  have hρRe := ZeroInequalitySpec ρ hρ.1 ρ.re rfl ρ.im rfl (by linarith); rw [← DeltaT] at hρRe
  calc DeltaT t / 6 ≤ (1 - DeltaT t / 3) - (1 - DeltaT ρ.im) := by linarith
    _ ≤ z.re - ρ.re := by linarith [hzRe.1, hρRe]
    _ = (z - ρ).re := by rw [Complex.sub_re]
    _ ≤ ‖z - ρ‖ := Complex.re_le_norm _



@[blueprint "LogDerivZetaUniformLogSquaredBoundStrip"
  (title := "LogDerivZetaUniformLogSquaredBoundStrip")
  (statement := /--
    There exists a constant $F\in(0,1/42)$ such that
    for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\leq 3/2
      \implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
  -/)
  (proof := /--
    Take $F=E/3$ where $E$ comes from Theorem \ref{ZeroInequality}.
    Then we have that $\sigma\geq 1-\delta_t/3$. So, we apply Lemma \ref{SumBoundII},
    which gives us that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
    Using the reverse triangle inequality and rearranging, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{|z-\rho|}+C\,\log|t|$$
    where $C$ is the implied constant in Lemma \ref{SumBoundII}.
    Now applying Lemma \ref{GapSize} we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)+C\,\log|t|.$$
    Now let $f(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$ with $\rho=\rho'+3/2+it$.
    Then if $\rho\in\mathcal{Z}_t$ we have that
    $$0=\zeta(\rho)=\zeta(\rho'+3/2+it)=f(\rho')$$
    with the same multiplicity of zero, that is $m_\zeta(\rho)=m_f(\rho')$.
    And also if $\rho\in\mathcal{Z}_t$ then
    $$3/4\geq|\rho-(3/2+it)|=|\rho'|.$$
    Thus we change variables to have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho'\in\mathcal{K}_f(3/4)}m_f(\rho')+C\,\log|t|.$$
    Now note that $f(0)=1$ and for $|z|\leq 5/6$ we have
    $$|f(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}.
    Thus by Theorem \ref{ZerosBound} we have that
    $$\sum_{\rho'\in\mathcal{K}_f(3/4)}m_f(\rho')
      \leq\frac{\log|t|+\log(13\,\zeta(3/2)/(3\,\zeta(3)))}{\log((5/6)/(3/4))}\leq D\log|t|$$
    where $D$ is taken to be sufficiently large.
    Recall, by definition that, $\delta_t=E/\log|t|$ with $E$ coming from
    Theorem \ref{ZeroInequality}. By using this fact and the above, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\ll\log^2|t|+\log|t|$$
    where the implied constant is taken to be bigger than $6D/E+C$.
    We know that the RHS is bounded above by $\ll\log^2|t|$; so the result follows.
  -/)]
lemma LogDerivZetaUniformLogSquaredBoundStrip : ∃ (F : ℝ) (_ : F = E / 3)
    (C : ℝ) (_ : 0 < C),
      ∀ (t : ℝ), 3 ≤ |t| →
        ∀ (σ : ℝ), σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
          ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 := by
  obtain ⟨C, Cpos, SumBoundII⟩ := SumBoundII
  set d : ℝ := ‖13 * ζ (3 / 2) / (3 * ζ 3)‖ with hd
  have d_gt_one : 1 < d := by
    simp only [hd, Complex.norm_div, Complex.norm_mul, Complex.norm_ofNat]
    rw [one_lt_div]
    · refine mul_lt_mul (by linarith) ?_ ?_ (ofNat_nonneg' _)
      · have ζNormLe := norm_zeta_strict_mono_ofReal (a := 3) (b := (3 / 2))
        simp only [half_lt_self_iff, ofNat_pos, ofReal_ofNat, ofReal_div, forall_const] at ζNormLe
        refine le_of_lt (ζNormLe (by linarith))
      · simp only [norm_pos_iff, ne_eq]
        exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    · simp only [ofNat_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq]
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  set D : ℝ := (1 + Real.log d / Real.log 3) / Real.log (10 / 9) with hD
  have Dpos : D > 0 := by
    rw [hD, add_div]
    refine add_pos ?_ (_root_.div_pos (_root_.div_pos (Real.log_pos d_gt_one) (Real.log_pos one_lt_ofNat))
        (Real.log_pos ?_))
    · rw [one_div_pos]
      exact Real.log_pos (by norm_num)
    · rw [one_lt_div ofNat_pos']
      linarith
  refine ⟨E / 3, rfl, ⟨6 * D / E + C,
    add_pos (mul_pos (mul_pos ofNat_pos' Dpos) (inv_pos.mpr EinIoo.1)) Cpos, ?_⟩⟩
  intro t ht σ hσ
  set r : ℝ := 3 / 4 with rwr
  set R : ℝ := 5 / 6 with rwR
  have R_over_r : R / r = 10 / 9 := by norm_num
  have r_pos : 0 < r := by norm_num
  have r_lt_one : r < 1 := by norm_num
  have r_lt_R : r < R := by norm_num
  have R_lt_one : R < 1 := by norm_num
  set B : ℝ := d * |t| with hB
  set g : ℂ → ℂ := fun z ↦ ζ (z + 3 / 2 + I * t) with hg
  set f : ℂ → ℂ := fun z ↦ g z / ζ (3 / 2 + I * t) with hf
  have fAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz; simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [hf, hg]
    refine AnalyticAt.div_const (AnalyticAt.comp (analyticOn_riemannZeta _ ?_)
      (AnalyticAt.add (AnalyticAt.add analyticAt_id analyticAt_const) analyticAt_const))
    by_contra h
    simp only [mem_compl_iff, mem_singleton_iff, not_not, Pi.add_apply, id_eq] at h
    rw [Complex.ext_iff] at h
    obtain ⟨_, hIm⟩ := h; simp only [add_im, div_ofNat_im, im_ofNat, zero_div, add_zero, mul_im,
      I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, one_im] at hIm
    rw [add_eq_zero_iff_eq_neg] at hIm
    have h := Complex.abs_im_le_norm z; rw [hIm, abs_neg] at h
    linarith
  have zetaThreeHalfNonzero : ¬ζ (3 / 2 + I * ↑t) = 0 := by
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have f0_1 : f 0 = 1 := by
    simp only [hg, hf, zero_add, div_self_eq_one₀, ne_eq, zetaThreeHalfNonzero, not_false_eq_true]
  have finiteSetOf0s : (SetOfZeros 1 f).Finite := by
    have gFiniteSetOf0s := ZetaShiftFiniteZeros (t := t) (by linarith) hg
    simp only [SetOfZeros, hf, div_eq_zero_iff, zetaThreeHalfNonzero, or_false] at gFiniteSetOf0s ⊢
    exact gFiniteSetOf0s
  have rFinite0s:= finiteSetOfZeros_mono r_lt_one finiteSetOf0s
  have finite0s := ZeroWindowFinite (t := t) (by linarith)
  have fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro z hz
    simp only [hf, hg, Complex.norm_div, hB, hd, Complex.norm_mul, Complex.norm_ofNat]
    rw [mul_comm 3 _, div_mul_eq_div_mul_one_div, mul_comm _ |t|, mul_comm _ (1 / 3), ← mul_div,
      ← mul_assoc, ← mul_assoc]
    refine mul_le_mul (le_trans (GlobalBound (s := z) (t := t) (by linarith) (by linarith)) (by linarith)) ?_ (inv_nonneg.mpr (Complex.norm_nonneg _)) (by linarith)
    rw [← inv_le_inv₀ (_root_.div_pos (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
      (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))) (inv_pos.mpr (norm_pos_iff.mpr zetaThreeHalfNonzero)), inv_div, inv_inv]
    have zetaLowerBound := norm_riemannZeta_ratio_le_on_vertical_line t
    simp only [verticalLine, norm_div, mul_comm, Complex.ofReal_div, Complex.ofReal_ofNat] at zetaLowerBound
    exact_mod_cast zetaLowerBound
  have ZerosBound := ZerosBound r_pos r_lt_one r_lt_R R_lt_one fAnalytic f0_1 finiteSetOf0s fz_bound
  rw [hB, one_div_mul_eq_div, cast_sum, R_over_r,
    Real.log_mul (by linarith) (by linarith), add_div] at ZerosBound
  have ZerosBound : ∑ ρ ∈ finite0s.toFinset, ↑(analyticOrderNatAt ζ ρ) ≤ Real.log |t| * D := by
    rw [mul_comm, Finset.sum_nbij' (t := rFinite0s.toFinset) (g := fun ρ ↦ ↑(analyticOrderNatAt f ρ))
      (fun ρ => ρ - (3 / 2 + I * t)) (fun ρ => ρ + (3 / 2 + I * t))]
    · apply le_trans ZerosBound
      rw [hd, div_mul_eq_mul_div, add_mul, one_mul, add_div, add_comm, add_le_add_iff_left]
      gcongr
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos one_lt_ofNat)]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log three_pos ht) (Real.log_nonneg d_gt_one.le)
    · simp only [ZeroWindow, Finite.mem_toFinset, mem_ofPred_eq, SetOfZeros, and_imp, rwr, hf, hg]
      ring_nf
      intro z hzZero hzBound
      simp only [_root_.mul_eq_zero, inv_eq_zero, zetaThreeHalfNonzero, or_false]
      exact ⟨hzBound, hzZero⟩
    · simp only [SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq, ZeroWindow, add_sub_cancel_right,
        and_imp, rwr, hf, hg]
      ring_nf
      intro z hzBound hzZero
      simp only [_root_.mul_eq_zero, inv_eq_zero, zetaThreeHalfNonzero, or_false] at hzZero
      exact ⟨hzZero, hzBound⟩
    · simp only [Finite.mem_toFinset, implies_true, sub_add_cancel]
    · simp only [Finite.mem_toFinset, implies_true, add_sub_cancel_right]
    · simp only [ZeroWindow, Finite.mem_toFinset, mem_ofPred_eq, hf, hg, Nat.cast_inj, and_imp]
      intro z hzZero hzBound
      have hAnal : AnalyticAt ℂ (fun w : ℂ ↦ ζ (w + 3 / 2 + I * t))
          (z - (3 / 2 + I * t)) := by
        apply AnalyticAt.comp (analyticOn_riemannZeta _ ?_)
          (AnalyticAt.add (AnalyticAt.add analyticAt_id analyticAt_const) analyticAt_const)
        simp only [mem_compl_iff, mem_singleton_iff, Pi.add_apply, id_eq]; ring_nf
        by_contra z1
        simp [z1] at hzBound; ring_nf at hzBound
        have h := Complex.abs_im_le_norm (-1 / 2 - I * t); simp only [sub_im, div_ofNat_im, neg_im,
          one_im, neg_zero, zero_div, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul,
          zero_add, zero_sub, abs_neg] at h
        linarith
      have horder := analyticOrderNatAt_fun_mul_const hAnal (inv_ne_zero zetaThreeHalfNonzero)
      have htranslate :
          analyticOrderNatAt (fun w : ℂ ↦ ζ (w + (3 / 2 + I * t)))
              (z - (3 / 2 + I * t)) =
            analyticOrderNatAt ζ (z - (3 / 2 + I * t) + (3 / 2 + I * t)) := by
        simpa only [analyticOrderNatAt, Function.comp_def] using congrArg ENat.toNat
          (analyticOrderAt_comp_of_deriv_ne_zero (f := ζ)
            (g := fun w : ℂ ↦ w + (3 / 2 + I * t)) (z₀ := z - (3 / 2 + I * t))
            (analyticAt_id.add analyticAt_const) (by simp))
      simp only [div_eq_mul_inv] at htranslate
      simpa only [div_eq_mul_inv, add_assoc, htranslate, sub_add_cancel] using horder.symm
  set z : ℂ := σ + t * I with hz
  have zIm : t = z.im := by
    simp only [hz, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
  have zRe : z.re ∈ Icc (1 - DeltaT t / 3) (3 / 2) := by
    simp only [hz, DeltaT, div_right_comm, add_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
      ofReal_im, mul_zero, sub_self, add_zero, hσ]
  have one_le_logt : 1 ≤ Real.log |t| := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos _)
    linarith [Real.exp_one_lt_three]
  calc ‖ζ' z / ζ z‖ ≤ _ := norm_le_norm_sub_add _ (∑ ρ ∈ finite0s.toFinset, analyticOrderNatAt ζ ρ / (z - ρ))
    _ ≤ ‖∑ ρ ∈ finite0s.toFinset, ↑(analyticOrderNatAt ζ ρ) / (z - ρ)‖ + C * Real.log |t| := by
      linarith [SumBoundII t (by linarith) z zIm zRe finite0s]
    _ ≤ ∑ ρ ∈ finite0s.toFinset, ↑(analyticOrderNatAt ζ ρ) / ‖z - ρ‖ + C * Real.log |t| := by
      rw [add_le_add_iff_right]
      apply norm_sum_le_of_le
      intro ρ hρ
      simp only [Complex.norm_div, RCLike.norm_natCast, Std.le_refl]
    _ ≤ (6 / DeltaT t) * ∑ ρ ∈ finite0s.toFinset, ↑(analyticOrderNatAt ζ ρ) + C * Real.log |t| := by
      rw [add_le_add_iff_right, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ hρ; rw [Finite.mem_toFinset] at hρ
      rw [mul_comm, mul_div, ← div_div_eq_mul_div]
      refine div_le_div_of_nonneg_left (cast_nonneg' _) ?_ (GapSize t ht z zRe ρ hρ)
      simp only [DeltaT, ofNat_pos, div_pos_iff_of_pos_right]
      refine _root_.div_pos EinIoo.1 (Real.log_pos ?_)
      linarith
    _ ≤ 6 * D / E * Real.log |t| ^ 2 + C * Real.log |t| := by
      simp only [DeltaT, add_le_add_iff_right, ← div_mul, mul_comm]
      field_simp
      exact div_le_div_of_nonneg_right ZerosBound EinIoo.1.le
    _ ≤ _ := by
      simp only [add_mul, add_le_add_iff_left]
      refine mul_le_mul_of_nonneg_left ?_ Cpos.le
      nlinarith [one_le_logt]



noncomputable def F : ℝ := LogDerivZetaUniformLogSquaredBoundStrip.choose
lemma Fequ : F = E / 3 := LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.1
lemma FinIoo : F ∈ Ioo (0 : ℝ) (1 / 42 : ℝ) := by
  simp only [one_div, Fequ, mem_Ioo, EinIoo.1, div_pos_iff_of_pos_left, ofNat_pos, true_and]
  linarith [EinIoo.2]



@[blueprint "LogDerivZetaBdd_of_Re_ge_three_halves"
  (title := "LogDerivZetaBdd-of-Re-ge-three-halves")
  (statement := /--
    There exists a uniform constant $C$ such that for $z=\sigma+it$ one has
    $$3/2\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(z)\right|\leq C.$$
  -/)
  (proof := /--
    Note that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|=\left|\sum_{n=1}^\infty\frac{\Lambda(n)}{n^z}\right|\leq
      \sum_{n=1}^\infty\frac{\Lambda(n)}{|n^z|}=\sum_{n=1}^\infty\frac{\Lambda(n)}{n^\sigma}\leq
      \sum_{n=1}^\infty\frac{\Lambda(n)}{n^{3/2}}<\infty$$
    by \ref{vonMangoldtLSeriesSummable}.
  -/)]
lemma LogDerivZetaBdd_of_Re_ge_three_halves :
    ∃ C, ∀ (s : ℂ), 3/2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)).norm
  refine ⟨∑' n, ‖LSeries.term (fun n ↦ (Λ n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖, fun s hs ↦ ?_⟩
  have hle := LSeries.norm_term_le_of_re_le_re (fun n ↦ (Λ n : ℂ))
    (s := ((3 / 2 : ℝ) : ℂ)) (s' := s) (by simpa using hs)
  have hsum' := hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [← norm_neg, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)]
  exact (norm_tsum_le_tsum_norm hsum').trans (hsum'.tsum_le_tsum hle hsum)



@[blueprint "LogDerivZetaUniformLogSquaredBound"
  (title := "LogDerivZetaUniformLogSquaredBound")
  (statement := /--
    There exists a constant $F\in(0,1/42)$ such that for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
  -/)
  (proof := /--
    Put the previous two Lemmas together.
  -/)]
theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Ici (1 - F / Real.log |t|) →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ (2 : ℝ) := by
  obtain ⟨C1, hC1⟩ := LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2
  obtain ⟨C2, hC2⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  have hC2pos := (norm_nonneg _).trans (hC2 2 (by norm_num))
  use max C1 C2, lt_max_of_lt_left hC1.1
  intro σ t ht hσ
  by_cases hσ' : σ ≤ 3 / 2
  · apply (hC1.2 t (by grind) σ ⟨hσ, hσ'⟩).trans
    gcongr
    · exact le_max_left _ _
    · simp only [log_abs, rpow_ofNat, Std.le_refl]
  · refine (hC2 _ ?_).trans ?_
    · norm_num; linarith
    · nth_rewrite 1 [← mul_one C2, ← mul_one 1, ← sq]
      refine mul_le_mul (le_max_right _ _) ?_ (sq_nonneg _) ?_
      · rw [one_pow, rpow_ofNat, one_le_sq_iff_one_le_abs, abs_of_pos (Real.log_pos (by linarith)), Real.le_log_iff_exp_le (by linarith)]
        linarith [Real.exp_one_lt_d9]
      · linarith [le_max_right C1 C2]



/-- A wrapper for the above theorem -/
lemma LogDerivZetaBndUnif12 : LogDerivZetaBndUnifGenProp 1 2 := by
  refine ⟨F, ⟨FinIoo.1, by linarith [FinIoo.2]⟩, ?_⟩
  simp only [rpow_one]
  apply LogDerivZetaUniformLogSquaredBound



-- analouge from ZetaBounds
lemma ZetaZeroFree1 :
    ZetaZeroFreeGenProp 1 := by
  refine ⟨F, ⟨FinIoo.1, by linarith [FinIoo.2]⟩, ?_⟩
  intro σ t ht hσ
  by_contra h
  have ZeroInequalityThing := ZeroInequalitySpec (σ + t * I) h
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, ge_iff_le, forall_eq] at ZeroInequalityThing
  have contra := hσ.1; rw [Fequ] at contra
  have contra := le_trans contra (ZeroInequalityThing (by linarith))
  have log_pos : 0 < Real.log |t| := by exact Real.log_pos (by linarith)
  rw [rpow_one, sub_le_sub_iff_left, div_div, div_le_div_iff_of_pos_left EinIoo.1 log_pos (mul_pos three_pos (Real.log_pos (lt_trans one_lt_ofNat ht)))] at contra
  linarith



@[blueprint "StrongPNT"
  (title := "StrongPNT")
  (statement := /--
    We have
    $$\sum_{n \leq x}\Lambda(n)=x+O(x \exp(-c(\log x)^{1/2})).$$
  -/)
  (proof := /-- This follows as a corollary of
    Theorems \ref{GenStrengthPNT} and \ref{LogDerivZetaUniformLogSquaredBound}. -/)
  (latexEnv := "theorem")]
theorem StrongPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  have := GenStrengthPNT (LogDerivZetaBoundedAndHoloGen LogDerivZetaBndUnif12
    (LogDerivZetaHolcLargeTGen ZetaZeroFree1 zero_lt_one)) (by linarith) (by linarith)
  ring_nf at this
  simpa only [gt_iff_lt, one_div, neg_mul] using this

/-- info: 'StrongPNT' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms StrongPNT
