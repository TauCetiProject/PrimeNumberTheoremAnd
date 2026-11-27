module

public import Architect
public import TauCeti.Analysis.Contour.Residue.SimplePole
public import TauCeti.Analysis.Contour.Residue.LogDeriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogUpperBound
import TauCeti.NumberTheory.LSeries.RiemannZeta.ZeroFreeStrip


@[expose] public section


open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta

blueprint_comment /--
We record here some prelimiaries about the zeta function and general
holomorphic functions.
-/
attribute [blueprint "ResidueOfTendsTo"
  (title := "ResidueOfTendsTo")
  (statement := /--
  If a function $f$ is meromorphic at $p$ with a pole of order at most one there, and $A$ is its
  residue at $p$, then
  $f(s) = \frac{A}{s-p} + O(1)$ near $p$. In particular, this holds if $f$ is holomorphic in a
  punctured neighborhood of $p$ and $\lim_{s\to p} (s-p)f(s) = A$.
  -/)
  (proof := /--
  Write $f(s) = g(s)/(s-p)$ near $p$ with $g$ holomorphic at $p$; then $A = g(p)$. Because $g$
  is holomorphic, near $s=p$ we have $g(s)=A+O(s-p)$. Then when you divide by $(s-p)$, you get
  $f(s) = A/(s-p) + O(1)$.
  -/)]
  MeromorphicAt.isBigO_sub_inv_smul_residue

attribute [blueprint "riemannZetaResidue"
  (proofUses := ["ResidueOfTendsTo"])
  (title := "riemannZetaResidue")
  (statement := /--
  The Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with residue $1$. In particular,
  the function $\zeta(s) - \frac{1}{s-1}$ is bounded in a neighborhood of $s=1$.
  -/)
  (proof := /--
  From \texttt{riemannZeta\_residue\_one} (in Mathlib), we know that
  $(s-1)\zeta(s)$ goes to $1$ as $s\to1$. Now apply Theorem \ref{ResidueOfTendsTo}.
  (This can also be done using $\zeta_0$ below, which is expressed as
  $1/(s-1)$ plus things that are holomorphic for $\Re(s)>0$...)
  -/)]
  isBigO_riemannZeta_sub_one_div

attribute [blueprint "logDerivResidue"
  (title := "logDerivResidue")
  (statement := /--
  If $f$ is meromorphic at $p$ of order $n\in\mathbb{Z}$, then $f'/f$ has a simple pole at $p$
  with residue $n$:
  $$ \frac{f'(s)}{f(s)} = \frac{n}{s - p} + O(1).$$
  In particular, if $f$ has a simple pole at $p$ with nonzero residue, then
  $\frac{f'(s)}{f(s)} = \frac{-1}{s - p} + O(1)$.
  -/)
  (proof := /--
  Write $f(s) = (s-p)^n h(s)$ near $p$, with $h$ holomorphic and nonvanishing at $p$. Then
  $$
  \frac{f'(s)}{f(s)} = \frac{n}{s-p} + \frac{h'(s)}{h(s)},
  $$
  so the residue of $f'/f$ at $p$ is $n$ and the pole has order at most one. Now apply
  Theorem \ref{ResidueOfTendsTo}.
  -/)
  (proofUses := ["ResidueOfTendsTo"])]
  MeromorphicAt.isBigO_logDeriv_sub_order_div

blueprint_comment /--
\label{BddAbove-to-IsBigO}
If $f$ is bounded above in a punctured neighborhood of $p$, then $f$ is $O(1)$ there.
This is the native bounded-filter characterization of $O(1)$.
-/

blueprint_comment /--
As a corollary, the log derivative of the Riemann zeta function has a simple pole at $s=1$:
-/
attribute [blueprint "riemannZetaLogDerivResidue"
  (uses := ["DifferentiableOn.vanishesOnRectangle"])
  (proofUses := ["logDerivResidue", "riemannZetaResidue"])
  (title := "riemannZetaLogDerivResidue")
  (statement := /--
  The log derivative of the Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with
  residue $-1$: $-\frac{\zeta'(s)}{\zeta(s)} - \frac{1}{s-1} = O(1)$.
  -/)
  (proof := /--
  This follows from Theorem \ref{logDerivResidue} and Theorem \ref{riemannZetaResidue}.
  -/)]
  log_deriv_riemannZeta_add_inv_sub_bounded

attribute [blueprint "riemannZeta0"
  (title := "riemannZeta0")
  (statement := /--
  For any natural $N\ge 0$ and any $s$ with $\Re s>0$, $s\neq 1$, the Euler--Maclaurin formula
  cut at the half-integer $N+1/2$ gives
  $$
  \zeta(s) =
  \sum_{1\le n \le N} \frac1{n^s}
  + \frac{(N+1/2)^{1-s}}{s-1}
  - s \int_{N+1/2}^\infty \frac{B_1(\{x\})}{x^{s+1}} \, dx,
  $$
  where $B_1(\{x\})=\{x\}-1/2$ is the first periodic Bernoulli function.
  -/)
  (proof := /--
  For $\Re s>1$ apply first-order Euler--Maclaurin summation to $n\mapsto n^{-s}$ on
  $(N+1/2,M]$ and let $M\to\infty$. The boundary term at $N+1/2$ vanishes because
  $B_1(1/2)=0$. The right-hand side is holomorphic in $\Re s>0$, $s\neq 1$, since the integral
  converges absolutely there, so the identity extends by analytic continuation.
  -/)
  (latexEnv := "lemma")]
  TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast_add_half

attribute [blueprint "ZetaBnd_aux1"
  (title := "ZetaBnd-aux1")
  (statement := /--
  For any integer $N\ge1$ and any $s$ with $\Re s>0$, $s\neq 1$,
  $$
  \left|\zeta(s)-\left(\sum_{1\le n\le N}\frac1{n^s}+\frac{N^{1-s}}{s-1}-\frac{N^{-s}}{2}\right)
  \right|\le\frac{|s|\,N^{-\Re s}}{2\Re s}.
  $$
  -/)
  (proof := /--
  Cut the Euler--Maclaurin formula at the integer $N$, where $B_1(\{N\})=-1/2$. The remainder is
  $-s\int_N^\infty B_1(\{x\})x^{-s-1}\,dx$, and $|B_1(\{x\})|\le 1/2$ bounds it by
  $\frac{|s|}{2}\int_N^\infty x^{-\Re s-1}\,dx=\frac{|s|\,N^{-\Re s}}{2\Re s}$.
  -/)
  (proofUses := ["riemannZeta0"])
  (latexEnv := "lemma")]
  TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le

attribute [blueprint "ZetaUpperBnd"
  (title := "ZetaUpperBnd")
  (statement := /--
  For every real $A$ there is a constant $C$ such that
  $$
  |\zeta(s)| \le C\log(|\Im s|+2)
  $$
  whenever $|\Im s|\ge 1$ and $1-A/\log(|\Im s|+2)\le\Re s$.
  -/)
  (proof := /--
  Write $s=\sigma+it$ and cut the Euler--Maclaurin formula of Lemma \ref{ZetaBnd_aux1} at
  $N=\lceil |t|\rceil$. This bounds $|\zeta(s)|$ by a harmonic sum weighted by
  $n^{1-\sigma}\le\max(1,(|t|+2)^{1-\sigma})$, plus terms of the same size. On the region
  $1-A/\log(|t|+2)\le\sigma$ that weight is at most $e^A$, so
  $|\zeta(s)|\ll_A\log(|t|+2)$.
  -/)
  (proofUses := ["ZetaBnd_aux1"])
  (latexEnv := "lemma")]
  TauCeti.exists_norm_riemannZeta_le_mul_log

attribute [blueprint "ZetaDerivUpperBnd"
  (title := "ZetaDerivUpperBnd")
  (statement := /--
  For every real $A$ there is a constant $C$ such that the derivative of the entire function
  $\zeta_0(s)=\zeta(s)-\frac{1}{s-1}$ satisfies
  $$
  |\zeta_0'(s)| \le C\log^2(|\Im s|+2)
  $$
  whenever $1-A/\log(|\Im s|+2)\le\Re s$.
  -/)
  (proof := /--
  The argument of Lemma \ref{ZetaUpperBnd}, together with the bound
  $|\zeta_0(s)-1/2|\le|s|/(2\Re s)$ far to the right and compactness at bounded height, gives
  $|\zeta_0(s)|\ll\log(|\Im s|+2)$ on the region $1-(A+1)/\log(|\Im s|+2)\le\Re s$. Apply
  Cauchy's estimate on the circle of radius $1/\log(|\Im s|+2)$ about $s$, which lies in that
  region.
  -/)
  (proofUses := ["ZetaUpperBnd"])
  (latexEnv := "lemma")]
  TauCeti.exists_norm_deriv_riemannZeta₀_le_mul_log_sq

attribute [blueprint "ZetaNear1BndExact"
  (title := "ZetaNear1BndExact")
  (statement := /--
  For every $s$ with $\Re s>1$,
  $$
  |\zeta(s)| < 1+\frac{1}{\Re s-1}.
  $$
  In particular $|\zeta(\sigma)|\le 2/(\sigma-1)$ for $1<\sigma\le 2$.
  -/)
  (proof := /--
  We have $|\zeta(s)|\le\zeta(\Re s)=\sum_n n^{-\Re s}$, and comparing the sum with an integral,
  $\sum_n n^{-\sigma}<1+\int_1^\infty x^{-\sigma}\,dx=1+\frac{1}{\sigma-1}$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one

blueprint_comment /--
\label{ZetaNoZerosOn1Line}
The zeta function does not vanish on the 1-line.
This fact is already proved in Stoll's work.
-/

attribute [blueprint "LogDerivZetaBnd"
  (title := "LogDerivZetaBnd")
  (proofUses := ["ZetaDerivUpperBnd", "SumBoundII", "ZeroInequality", "ShiftZeroBound",
    "LogDerivativeDirichlet"])
  (statement := /--
  There are constants $0<\beta<1$ and $C$ such that every $s\neq 1$ with
  $1-\beta/\log(|\Im s|+2)\le\Re s$ has $\zeta(s)\neq 0$,
  $$
  \left|\zeta'(s)+\frac{1}{(s-1)^2}\right|\le C\log^2(|\Im s|+2)
  \quad\text{and}\quad
  \left|\frac{\zeta'}{\zeta}(s)+\frac{1}{s-1}\right|\le C\log(|\Im s|+2).
  $$
  -/)
  (proof := /--
  The bound for $\zeta'$ is Lemma \ref{ZetaDerivUpperBnd}. For $\zeta'/\zeta$ put
  $L=\log(|\Im s|+2)$, $\eta=1/(2L)$ and $s_1=1+\eta+i\Im s$. On $\Re s\geq 1+\eta$, comparing the
  Dirichlet series $-\frac{\zeta'}{\zeta}=\sum_n\Lambda(n)n^{-s}$ with its value at $1+\eta$
  (Theorem \ref{LogDerivativeDirichlet}) and Lemma \ref{ShiftZeroBound} give $O(L)$. Otherwise
  apply Theorem \ref{SumBoundII} at $s$ and at $s_1$: the two window sums run over the same zeros
  $\rho$, which Theorem \ref{ZeroInequality} keeps at distance at least $\beta/L$ from $s$, so
  $$\left|\frac{1}{s-\rho}-\frac{1}{s_1-\rho}\right|
    \le\left(2+\frac{1}{2\beta}\right)\Re\frac{1}{s_1-\rho},$$
  and the window sum at $s_1$, whose real part is $O(L)$ by the bound at $s_1$, bounds the
  difference.
  -/)
  (latexEnv := "theorem")]
  TauCeti.riemannZeta_deriv_logDeriv_bound

attribute [blueprint "ZetaInvBnd"
  (title := "ZetaInvBnd")
  (proofUses := ["LogDerivZetaBnd", "ZetaUpperBnd", "ZetaNear1BndExact"])
  (statement := /--
  There are constants $0<\beta<1$ and $C>0$ such that, on the region
  $Z=\{s:1-\beta/\log(|\Im s|+2)\le\Re s\}$, $\zeta(s)\neq 0$ for $s\neq 1$, the extension
  $R(s)=(s-1)/((s-1)\zeta(s))$ of $1/\zeta$ (with $R(1)=0$) is analytic on a neighbourhood of
  $Z$, and
  $$
  \left|\zeta(s)-\frac{1}{s-1}\right|\le C\log(|\Im s|+2),\qquad
  |R(s)|\le C\log(|\Im s|+2)
  $$
  on $Z$.
  -/)
  (proof := /--
  The bound for $\zeta(s)-1/(s-1)$ is the argument of Lemma \ref{ZetaUpperBnd}. For $R$ write
  $L=\log(|\Im s|+2)$ and $s_1=1+1/L+i\Im s$. Right of $\Re s=1+1/L$ the Möbius series gives
  $|1/\zeta(s)|\le 1+L$, as in Lemma \ref{ZetaNear1BndExact}. Left of that line and at height
  $|\Im s|\ge 1$, Theorem \ref{LogDerivZetaBnd} gives $\zeta'/\zeta=O(L)$ on the horizontal
  segment from $s$ to $s_1$, whose length is at most $2/L$. Gr\"onwall's inequality along the
  segment bounds $|\zeta(s_1)|/|\zeta(s)|$ by an absolute constant, so
  $|R(s)|\ll|R(s_1)|=O(L)$. Below height $1$ the rest of $Z$ is compact and $R$ is continuous
  on it.
  -/)
  (latexEnv := "theorem")]
  TauCeti.riemannZeta_zeroFreeStrip_bounds

blueprint_comment /--
The 3-4-1 inequality also gives a lower bound for $|\zeta|$ to the right of the line
$\Re s=1$, which degrades only like a power of $\sigma-1$.
-/

@[blueprint
  (title := "ZetaInvBound1")
  (statement := /--
  For all $\sigma>1$,
  $$
  1/|\zeta(\sigma+it)| \le |\zeta(\sigma)|^{3/4}|\zeta(\sigma+2it)|^{1/4}
  $$
  -/)
  (proof := /--
  This is the fourth root of the 3-4-1 inequality
  $$
  1 \le |\zeta(\sigma)|^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)|
  $$
  for $\sigma>1$, which Mathlib proves for every Dirichlet $L$-function
  (\texttt{DirichletCharacter.norm\_LFunction\_product\_ge\_one}); take the trivial character
  of modulus $1$.
  -/)
  (latexEnv := "lemma")]
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖ζ (σ + t * I)‖ ≤ ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (1 : DirichletCharacter ℂ 1)
    (x := σ - 1) (by linarith) t
  simp only [DirichletCharacter.LFunctionTrivChar, one_pow, DirichletCharacter.LFunction_modOne_eq,
    ofReal_sub, ofReal_one, add_sub_cancel, norm_mul, norm_pow, mul_comm I, mul_right_comm _ I] at h
  rw [one_div, inv_le_iff_one_le_mul₀ (norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re
    (by simpa using σ_gt)))]
  refine (one_le_pow_iff_of_nonneg (by positivity) four_ne_zero).1 (h.trans_eq ?_)
  simp only [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
  ring

@[blueprint
  (title := "ZetaInvBound2")
  (proofUses := ["ZetaInvBnd"])
  (statement := /--
  For $\sigma>1$ (and $\sigma \le 2$),
  $$
  1/|\zeta(\sigma+it)| \ll (\sigma-1)^{-3/4}(\log |t|)^{1/4},
  $$
  as $|t|\to\infty$.
  -/)
  (proof := /--
  Put $x=1/|\zeta(\sigma+it)|$. Theorem \ref{ZetaInvBnd} gives $x\ll\log(|t|+2)\le 2\log|t|$,
  and the Möbius series gives $x<1+1/(\sigma-1)\le 2/(\sigma-1)$. Hence
  $x=x^{1/4}x^{3/4}\ll(\log|t|)^{1/4}(\sigma-1)^{-3/4}$. (Alternatively, combine
  Lemma \ref{ZetaInvBound1} with the bounds in Lemmata \ref{ZetaNear1BndExact} and
  \ref{ZetaUpperBnd}.)
  -/)
  (latexEnv := "lemma")]
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨β, C, hβ, -, hC, -, h⟩ := TauCeti.riemannZeta_zeroFreeStrip_bounds
  refine ⟨(2 * C) ^ ((1 : ℝ) / 4) * 2 ^ ((3 : ℝ) / 4), by positivity, fun {σ} hσ t ht ↦ ?_⟩
  have hσ1 : 0 < σ - 1 := sub_pos.2 hσ.1
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hs1 : (σ + t * I : ℂ) ≠ 1 := fun h ↦ by
    have := congrArg im h; simp at this; norm_num [this] at ht
  have hA := (h (σ + t * I) (by simp; linarith [div_pos hβ (Real.log_pos (by linarith :
    1 < |t| + 2))])).2.2
  rw [div_eq_mul_inv, ← inv_riemannZeta_eq_sub_mul_of_ne_one hs1, norm_inv] at hA
  have hl2 : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
    rw [show 2 * Real.log |t| = Real.log (|t| ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hB := TauCeti.inv_norm_riemannZeta_lt_one_add_one_div_sub_one (s := σ + t * I)
    (by simpa using hσ.1)
  have h1 : 1 ≤ 1 / (σ - 1) := by rw [le_div_iff₀ hσ1]; linarith [hσ.2]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hA hB
  have h2 : 2 / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
  calc 1 / ‖ζ (σ + t * I)‖
        = ‖ζ (σ + t * I)‖⁻¹ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖⁻¹ ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add' (by positivity) (by norm_num), one_div]; norm_num
    _ ≤ (2 * C * Real.log |t|) ^ ((1 : ℝ) / 4) * (2 / (σ - 1)) ^ ((3 : ℝ) / 4) := by
        gcongr
        · nlinarith
        · linarith
    _ = _ := by
        rw [Real.mul_rpow (by positivity) hlog.le, Real.div_rpow two_pos.le hσ1.le, neg_div,
          Real.rpow_neg hσ1.le]
        ring

@[blueprint
  (title := "ZetaLowerBound3")
  (proofUses := ["ZetaInvBound2"])
  (statement := /--
  There exists a $c>0$ such that for all $1 < \sigma <= 2$ and $3 < |t|$,
  $$
  c \frac{(\sigma-1)^{3/4}}{(\log |t|)^{1/4}} \le |\zeta(\sigma + tI)|.
  $$
  -/)
  (proof := /--
  Take reciprocals in Lemma \ref{ZetaInvBound2}.
  -/)
  (latexEnv := "lemma")]
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨C, hC, h⟩ := ZetaInvBound2
  refine ⟨C⁻¹, inv_pos.2 hC, fun {σ} hσ t ht ↦ ?_⟩
  have hσ1 : 0 < σ - 1 := sub_pos.2 hσ.1
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hζ := norm_pos_iff.2
    (riemannZeta_ne_zero_of_one_lt_re (s := σ + t * I) (by simpa using hσ.1))
  have h1 := h hσ t ht
  rw [neg_div, Real.rpow_neg hσ1.le, one_div, inv_le_comm₀ hζ (by positivity)] at h1
  convert h1 using 1
  field_simp
