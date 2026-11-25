module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.NumberTheory.Chebyshev.DeLaValleePoussin
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Local
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Window


@[expose] public section

open Filter Real

local notation "ψ" => Chebyshev.psi

blueprint_comment /--
The route to the strong prime number theorem is: Landau's local lemma
(Theorem \ref{FinalBound}), the local expansion of $\zeta'/\zeta$
(Theorem \ref{LogDerivZetaFinalBound}) and its window form (Theorem \ref{SumBoundII}), the
de la Vall\'ee Poussin zero-free region (Theorem \ref{ZeroInequality}), the bound for
$\zeta'/\zeta$ to the right of the zero-free curve (Theorem \ref{LogDerivZetaBnd}), and Ingham's
transfer theorem (Theorem \ref{GenStrengthPNT}).
-/

attribute [blueprint "ZerosBound"
  (title := "ZerosBound")
  (statement := /--
    Let $0<|r|<|R|$ and $M\geq 1$. If $f$ is analytic on a neighbourhood of the closed disc
    $\overline{\mathbb{D}_{|R|}(c)}$ with $f(c)\neq 0$ and $|f(z)|\leq M$ for $|z-c|=|R|$, then
    the number of zeros of $f$ in $\overline{\mathbb{D}_{|r|}(c)}$, counted with multiplicity, is
    at most
    $$\frac{\log(M/|f(c)|)}{\log(R/r)}.$$
  -/)
  (proof := /--
    This is Jensen's formula, in the form of Mathlib's \texttt{AnalyticOnNhd.sum\_divisor\_le}:
    each zero $\rho$ with $|\rho-c|\leq|r|$ contributes $m_f(\rho)\log(|R|/|\rho-c|)\geq
    m_f(\rho)\log(R/r)$ to
    $$\frac{1}{2\pi}\int_0^{2\pi}\log|f(c+Re^{i\theta})|\,d\theta-\log|f(c)|
      \leq\log M-\log|f(c)|.$$
  -/)
  (latexEnv := "theorem")]
  AnalyticOnNhd.sum_divisor_le


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


attribute [blueprint "ZeroInequality"
  (title := "ZeroInequality")
  (proofUses := ["LogDerivativeDirichlet", "ShiftZeroBound", "ShiftOneBound", "ShiftTwoBound"])
  (statement := /--
    There is a constant $c>0$ such that $\zeta(s)\neq 0$ for every $s\neq 1$ with
    $$\Re s\geq 1-\frac{c}{\log(|\Im s|+3)}.$$
  -/)
  (proof := /--
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
  -/)
  (latexEnv := "theorem")]
  TauCeti.LFunctions.riemannZeta_zeroFreeRegion


attribute [blueprint "SumBoundII"
  (title := "SumBoundII")
  (proofUses := ["LogDerivZetaFinalBound", "ZerosBound"])
  (statement := /--
    There is a constant $C$ such that for every $s\neq 1$ with $-1\leq\Re s\leq 2$ and
    $\zeta(s)\neq 0$,
    $$\left|\frac{\zeta'}{\zeta}(s)+\frac{1}{s-1}
      -\sum_{\rho}\frac{m_\zeta(\rho)}{s-\rho}\right|\leq C\log(|\Im s|+2),$$
    where the sum runs over the zeros $\rho$ of $\zeta$ with $0<\Re\rho<1$ and
    $|\Im\rho-\Im s|\leq 1$, counted with multiplicity $m_\zeta(\rho)$.
  -/)
  (proof := /--
    Apply Theorem \ref{LogDerivZetaFinalBound} with centre $s_0=2+i\Im s$ and radii $3<4$.
    Every zero of the window lies in the disc of radius $4$ about $s_0$. Every other zero $\rho$
    of $\zeta$ in that disc is at distance at least $1$ from $s$: the zeros with $\Re\rho\leq 0$
    are the trivial zeros $-2,-4,\dots$, there are none with $\Re\rho\geq 1$, and the rest have
    $|\Im\rho-\Im s|>1$. So those zeros contribute at most their number, which is
    $O(\log(|\Im s|+2))$ by Jensen's formula (Theorem \ref{ZerosBound}) applied to the entire
    function $(s-1)\zeta(s)$ on a disc centred on the line $\Re s=2$.
  -/)
  (latexEnv := "theorem")]
  TauCeti.riemannZeta_logDeriv_window


attribute [blueprint "dlVPPNT"
  (title := "Prime number theorem with de la Vall\'ee Poussin's error term")
  (proofUses := ["GenStrengthPNT", "LogDerivZetaBnd", "ZeroInequality"])
  (statement := /--
    There are $c>0$ and $C$ such that for every $x\geq 3$,
    $$\left|\psi(x)-x\right|\leq C\,x\exp\left(-c\sqrt{\log x}\right).$$
  -/)
  (proof := /--
    Apply Ingham's transfer theorem (Theorem \ref{GenStrengthPNT}) to $a=\Lambda$, $r=1$ and the
    zero-free width $\eta(t)=c/\log t$. Its hypotheses on $\zeta$ come from
    Theorems \ref{ZeroInequality} and \ref{LogDerivZetaBnd}: on the region
    $1-c/\log(|\Im s|+3)\leq\Re s$ the function $\zeta$ has no zeros other than the pole at $1$,
    and $G(s)=-\frac{\zeta'}{\zeta}(s)-\frac{1}{s-1}$ is holomorphic on a neighbourhood of the
    region (it is the negative logarithmic derivative of the entire function $(s-1)\zeta(s)$) and
    is $O(\log(|\Im s|+3))$ there. For this width the Ingham exponent satisfies
    $\omega_\eta(x)\geq\sqrt{c\log x}$ (Definition \ref{InghamExponent}).
  -/)
  (latexEnv := "theorem")]
  Chebyshev.exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log


@[blueprint "StrongPNT"
  (title := "StrongPNT")
  (statement := /--
    We have
    $$\sum_{n \leq x}\Lambda(n)=x+O(x \exp(-c(\log x)^{1/2})).$$
  -/)
  (proof := /-- This is the asymptotic form of Theorem \ref{dlVPPNT}. -/)
  (proofUses := ["dlVPPNT"])
  (latexEnv := "theorem")]
theorem StrongPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  obtain ⟨c, hc, h⟩ := Chebyshev.exists_isBigO_psi_sub_id_mul_exp_neg_mul_sqrt_log
  exact ⟨c, hc, by simpa only [Real.sqrt_eq_rpow] using h.congr_left fun x ↦ by simp⟩

/-- info: 'StrongPNT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StrongPNT
