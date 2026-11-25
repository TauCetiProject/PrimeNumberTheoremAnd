module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
public import PrimeNumberTheoremAnd.StrongPNT
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.MellinTransform.EdgeBounds
import TauCeti.NumberTheory.LSeries.InghamExponent
import TauCeti.NumberTheory.LSeries.SmoothedSum.Basic
import TauCeti.NumberTheory.LSeries.SmoothedSum.Contour
import TauCeti.NumberTheory.LSeries.SmoothedSum.ContourEstimate
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion


@[expose] public section


open Filter Real

local notation "ψ" => Chebyshev.psi

blueprint_comment /--
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in [Kontorovich 2015], in the form of Ingham's
transfer theorem from a zero-free region to an error term in the prime number theorem.
-/

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

attribute [blueprint "LogDerivativeDirichlet"
  (title := "LogDerivativeDirichlet")
  (statement := /--
  We have that, for $\Re(s)>1$,
  $$-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}. $$-/)
  (proof := /-- Already in Mathlib. -/)
  (latexEnv := "theorem")]
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div

blueprint_comment /--
\begin{definition}[SmoothedChebyshev]\label{SmoothedChebyshev}
Fix $\epsilon>0$, and a bumpfunction $\nu$ supported in $[1/2,2]$
(Theorem \ref{SmoothExistence}). The smoothed Chebyshev function $\psi_{\epsilon}$ from
$\mathbb{R}_{>0}$ to $\mathbb{C}$ is
$$\psi_{\epsilon}(X) = \sum_{n=1}^\infty \Lambda(n)\widetilde{1_{\epsilon}}(n/X),$$
where $\widetilde{1_{\epsilon}}$ is the smoothed cutoff of Definition \ref{Smooth1}.
\end{definition}
-/

attribute [blueprint "SmoothedChebyshevDirichlet_aux_integrable"
  (title := "SmoothedChebyshevDirichlet-aux-integrable")
  (statement := /--
  Let $\nu$ be of class $C^1$ on $(0,\infty)$ and vanish there off $[1/2,2]$, and let
  $\epsilon>0$ and $\sigma>0$. Then for any arithmetic function $a$ the function
  $$
  t \mapsto L(a,\sigma + it)\,\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma + it)
  $$
  is integrable on $\mathbb{R}$ (where the $L$-series does not converge it is $0$).
  -/)
  (proof := /--
  Where $L(a,\sigma+it)$ converges absolutely it is bounded by its value at $\sigma$, and by
  Lemma \ref{MellinOfSmooth1b} the Mellin factor is $O(1/t^2)$ as $t\rightarrow \infty$; hence
  the function is integrable.
  -/)
  (proofUses := ["MellinOfSmooth1b"])
  (latexEnv := "lemma")]
  TauCeti.LSeries.integrable_LSeries_mul_mellin_smoothCutoff

attribute [blueprint "SmoothedChebyshevDirichlet"
  (title := "SmoothedChebyshevDirichlet")
  (proofUses := ["Smooth1ContinuousAt", "SmoothedChebyshevDirichlet_aux_integrable",
    "MellinOfSmooth1a"])
  (statement := /--
  Let $\nu$ be of class $C^1$ on $(0,\infty)$ and vanish there off $[1/2,2]$, let $\epsilon>0$,
  and let the $L$-series of $f$ converge absolutely on the line $\Re s=\sigma>0$. For $X>0$,
  $$\sum_{n=1}^\infty f(n)\widetilde{1_{\epsilon}}(n/X) = \frac{1}{2\pi i}\int_{(\sigma)}
  L(f,s)\,\mathcal{M}(\widetilde{1_{\epsilon}})(s)\,X^{s}ds.$$
  With $f=\Lambda$ and $\sigma=1+1/\log X$, by Theorem \ref{LogDerivativeDirichlet} this
  expresses $\psi_\epsilon(X)$ as
  $$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(\sigma)}\frac{-\zeta'(s)}{\zeta(s)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)X^{s}ds.$$
  -/)
  (proof := /--
  The sum has finitely many nonzero terms, since $\widetilde{1_{\epsilon}}$ vanishes on
  $[2^\epsilon,\infty)$. By Mellin inversion,
  $\widetilde{1_{\epsilon}}(n/X)=\frac{1}{2\pi i}\int_{(\sigma)}
  \mathcal{M}(\widetilde{1_{\epsilon}})(s)(n/X)^{-s}ds$, and the quadratic decay of
  $\mathcal{M}(\widetilde{1_{\epsilon}})$ justifies the interchange of summation and
  integration.
  -/)
  (latexEnv := "theorem")]
  TauCeti.LSeries.hasSum_mul_smoothCutoff

blueprint_comment /--
The smoothed Chebyshev function is close to the actual Chebyshev function.
-/

attribute [blueprint "SmoothedChebyshevClose"
  (title := "SmoothedChebyshevClose")
  (proofUses := ["Smooth1Nonneg", "Smooth1Properties_above", "Smooth1Properties_below",
    "Smooth1LeOne"])
  (statement := /--
  For a bumpfunction $\nu$, $0<\epsilon\le 1$ and $X\ge 2$,
  $$|\psi(X)-\psi_{\epsilon}(X)|\le 3(2\epsilon X+1)\log X.$$
  In particular $\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X \log X)$ when $\epsilon X\ge 1$.
  -/)
  (proof := /--
  Take the difference. By Lemma \ref{Smooth1Properties_above} and \ref{Smooth1Properties_below},
  the sums agree except when $2^{-\epsilon} < n/X < 2^{\epsilon}$. This is an interval of
  length $\ll \epsilon X$, and the summands are bounded by $\Lambda(n) \le \log(2X)$.
  -/)
  (latexEnv := "theorem")]
  TauCeti.norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le

blueprint_comment /--
Suppose that $\zeta$ has a zero-free region $\Re s\ge 1-\eta(|\Im s|+3)$ in which
$-\zeta'/\zeta(s)=G(s)+1/(s-1)$ with $G$ holomorphic and of logarithmic size. Returning to the
definition of $\psi_{\epsilon}$, fix a height $T$ to be chosen later, and set
$\sigma_0 = 1 + 1 / \log X$ and $\sigma_1 = 1-\eta(T+3)$. Pull the contour from the line
$\Re s=\sigma_0$ to the boundary of the rectangle $[\sigma_1,\sigma_0]\times[-T,T]$: the two
vertical tails $|t|>T$ on the line $\Re s=\sigma_0$, the left edge $\Re s=\sigma_1$, $|t|\le T$,
and the two horizontal edges at heights $\pm T$. In the process, we pick up the residue at
$s=1$.
-/

attribute [blueprint "SmoothedChebyshevPull1"
  (title := "SmoothedChebyshevPull1")
  (proofUses := ["SmoothedChebyshevDirichlet", "SmoothedChebyshevDirichlet_aux_integrable",
    "ResidueTheoremOnRectangleWithSimplePole", "RectangleIntegral"])
  (statement := /--
  Let $\nu$ be of class $C^1$ on $(0,\infty)$ and vanish there off $[1/2,2]$, $\epsilon>0$,
  $x\ge 0$, $0<\sigma_1<1<\sigma_0$ and $T>0$. Let $G$ be continuous on
  $[\sigma_1,\sigma_0]\times[-T,T]$ and holomorphic on its interior, and let the $L$-series of
  $a$ be summable at $\sigma_0$ with $L(a,s)=G(s)+r/(s-1)$ on the line $\Re s=\sigma_0$. With
  $f(s)=(G(s)+r/(s-1))\,\mathcal{M}(\widetilde{1_{\epsilon}})(s)\,x^s$,
  $$\sum_{n} a(n)\widetilde{1_{\epsilon}}(n/x) =
  r\,\mathcal{M}(\widetilde{1_{\epsilon}})(1)\,x +
  \frac{1}{2\pi}\left(\int_{|t|>T}f(\sigma_0+it)\,dt+\int_{-T}^{T}f(\sigma_1+it)\,dt
  +\frac1i\left(\int_{\sigma_1}^{\sigma_0}f(\sigma+iT)\,d\sigma
  -\int_{\sigma_1}^{\sigma_0}f(\sigma-iT)\,d\sigma\right)\right).$$
  -/)
  (proof := /-- Pull the rectangle contour and evaluate the pole at $s=1$. -/)
  (latexEnv := "theorem")]
  TauCeti.LSeries.tsum_mul_smoothCutoff_eq_residue_add_contour

blueprint_comment /--
It remains to estimate the three kinds of integrals.
-/

attribute [blueprint "I1Bound"
  (title := "I1Bound")
  (statement := /--
  Let $\epsilon>0$ and $T>0$. If
  $|f(\sigma+it)|\le K/(|s|(1+\epsilon|s|))$ at $s=\sigma+it$ for $|t|>T$, then
  $$\left|\int_{|t|>T}f(\sigma+it)\,dt\right|\le\frac{2K}{\epsilon T}.$$
  On the line $\sigma_0=1+1/\log X$ the integrand of Theorem \ref{SmoothedChebyshevPull1} has
  this form with $K\ll X\log^2 X$, by Lemma \ref{MellinOfSmooth1b}.
  -/)
  (proof := /--
  Bound $1/(|s|(1+\epsilon|s|))\le 1/(\epsilon t^2)$ and integrate:
  $\int_{|t|>T}\frac{dt}{\epsilon t^2}=\frac{2}{\epsilon T}$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.norm_integral_vertical_tail_le

attribute [blueprint "I2GenBound"
  (title := "I2GenBound")
  (statement := /--
  Let $\sigma_1\le\sigma_2$, $T\neq 0$, $\epsilon>0$ and $x\ge 1$. If
  $|f(\sigma+iT)|\le Kx^\sigma/(|s|(1+\epsilon|s|))$ at $s=\sigma+iT$ for
  $\sigma_1\le\sigma\le\sigma_2$, then
  $$\left|\int_{\sigma_1}^{\sigma_2}f(\sigma+iT)\,d\sigma\right|
    \le\frac{(\sigma_2-\sigma_1)Kx^{\sigma_2}}{\epsilon T^2}.$$
  -/)
  (proof := /--
  Bound $1/(|s|(1+\epsilon|s|))\le 1/(\epsilon T^2)$ and $x^\sigma\le x^{\sigma_2}$, and
  integrate over an interval of length $\sigma_2-\sigma_1$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.norm_intervalIntegral_horizontal_le

attribute [blueprint "I3GenBound"
  (title := "I3GenBound")
  (statement := /--
  Let $\sigma>0$ and $T\ge 0$. If $|f(\sigma+it)|\le K/|\sigma+it|$ for $|t|\le T$, then
  $$\left|\int_{-T}^{T}f(\sigma+it)\,dt\right|\le 4K\log(1+T/\sigma).$$
  -/)
  (proof := /--
  Bound $1/|\sigma+it|\le 2/(\sigma+|t|)$ and integrate:
  $\int_{-T}^{T}\frac{2\,dt}{\sigma+|t|}=4\log(1+T/\sigma)$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.norm_intervalIntegral_vertical_le

attribute [blueprint "SmoothedSumNearPole"
  (title := "SmoothedSumNearPole")
  (proofUses := ["SmoothedChebyshevPull1", "I1Bound", "I2GenBound", "I3GenBound",
    "MellinOfSmooth1b"])
  (statement := /--
  Let $|a(n)|\le B\log(n+1)$ for $n\ge 1$, let $\nu$ be of class $C^1$ on $(0,\infty)$ and vanish
  there off $[1/2,2]$, $\epsilon>0$, $x\ge 2$, $0<\eta<1$ and $\eta\le T$, and put
  $\sigma_0=1+1/\log x$. Let $G$ be continuous on $[1-\eta,\sigma_0]\times[-T,T]$, holomorphic
  on its interior and bounded by $M$ there, with $L(a,s)=G(s)+r/(s-1)$ on the line
  $\Re s=\sigma_0$. If $|\mathcal{M}(\widetilde{1_{\epsilon}})(s)|\le C/(|s|(1+\epsilon|s|))$
  for $1-\eta\le\Re s\le\sigma_0$, then
  $$\left|\sum_n a(n)\widetilde{1_{\epsilon}}(n/x)-r\,\mathcal{M}(\widetilde{1_{\epsilon}})(1)\,x
    \right|\le\frac{1}{2\pi}\left(\frac{16eBCx\log^2x}{\epsilon T}
    +4Kx^{1-\eta}\log\left(1+\frac{T}{1-\eta}\right)
    +\frac{2e(1/\log x+\eta)Kx}{\epsilon T^2}\right),$$
  where $K=(M+|r|/\eta)C$.
  -/)
  (proof := /--
  Apply Theorem \ref{SmoothedChebyshevPull1} with $\sigma_1=1-\eta$. On the line $\Re
  s=\sigma_0$ the $L$-series is at most $B\sum_n\log(n+1)n^{-\sigma_0}\le 8B\log^2x$ and
  $x^{\sigma_0}=ex$, so Lemma \ref{I1Bound} bounds the tails. On the rest of the contour
  $|G(s)+r/(s-1)|\le M+|r|/\eta$, so Lemmas \ref{I3GenBound} and \ref{I2GenBound} bound the left
  edge and the horizontal edges.
  -/)
  (latexEnv := "theorem")]
  TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log

attribute [blueprint "InghamExponent"
  (title := "InghamExponent")
  (statement := /--
  For a zero-free width $\eta$, the Ingham exponent is
  $$\omega_\eta(x)=\inf_{t\ge 3}\left(\eta(t)\log x+\log t\right).$$
  If $\eta(t)\ge a_0(\log t)^{-A}$ on $[3,\infty)$ with $a_0,A\ge 0$, then
  $\omega_\eta(x)\ge a_0^{1/(1+A)}(\log x)^{1/(1+A)}$ for $x\ge 1$; for $\eta(t)=c/\log t$ this
  gives $\omega_\eta(x)\ge\sqrt{c\log x}$.
  -/)
  (latexEnv := "definition")]
  TauCeti.inghamExponent

attribute [blueprint "InghamHeightChoice"
  (title := "InghamHeightChoice")
  (proofUses := ["InghamExponent"])
  (statement := /--
  Let $\eta$ be continuous and nonincreasing on $[3,\infty)$, and let $x\ge 1$ satisfy
  $\log 3\le\eta(6)\log x$. Then there is a height $T\ge 3$ with $x^{\eta(T+3)}=T$ and
  $\omega_\eta(x)\le 2\log T+\log 2$.
  -/)
  (proof := /--
  The function $T\mapsto x^{\eta(T+3)}-T$ is continuous, nonnegative at $T=3$ and negative for
  large $T$, so it has a zero $T$. At $t=T+3\le 2T$,
  $\omega_\eta(x)\le\eta(T+3)\log x+\log(T+3)=\log T+\log(T+3)\le 2\log T+\log 2$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.exists_rpow_eq_and_inghamExponent_le

blueprint_comment /--
\section{MediumPNT}
-/

attribute [blueprint "GenStrengthPNT"
  (title := "GenStrengthPNT")
  (proofUses := ["SmoothedChebyshevClose", "SmoothedChebyshevDirichlet", "SmoothedSumNearPole",
    "InghamHeightChoice", "InghamExponent", "MellinOfSmooth1b", "MellinOfSmooth1c",
    "SmoothExistence"])
  (statement := /--
    (Ingham's transfer theorem.) Let $\eta$ be continuous and nonincreasing on $[3,\infty)$ with
    $\eta(t)\ge a_0(\log t)^{-A}$ there, $a_0>0$. Let $|a(n)|\le B\log(n+1)$ for $n\ge 1$, let
    $U$ contain $R_\eta=\{s:1-\eta(|\Im s|+3)\le\Re s\}$, and let $G$ be holomorphic on $U$
    with $L(a,s)=G(s)+r/(s-1)$ for $\Re s>1$ and $|G(s)|\le C_0\log(|\Im s|+3)^{B'}$ on
    $R_\eta$. Then there are $c>0$ and $C'$ with
    $$\left|\sum_{n\le x}a(n)-rx\right|\le C'x\exp(-c\,\omega_\eta(x))$$
    for every $x\ge 3$. For $a=\Lambda$ and $\eta(t)=A/\log^{n_1}t$ this gives
    $$\sum_{n \leq x}\Lambda(n)=x+O(x\exp(-c(\log x)^{1/(1+n_1)})).$$
  -/)
  (proof := /--
    Fix a bump $\nu$ (Theorem \ref{SmoothExistence}) and choose the height $T$ of
    Lemma \ref{InghamHeightChoice}. The rectangle $[1-\eta(T+3),1+1/\log x]\times[-T,T]$ lies in
    $R_\eta$, so Theorem \ref{SmoothedSumNearPole} bounds the smoothed sum minus
    $r\,\mathcal{M}(\widetilde{1_{\epsilon}})(1)\,x$, using Lemma \ref{MellinOfSmooth1b} for the
    Mellin factor. With $\epsilon = T^{-1/2}$, the comparison with the sharp sum
    (Theorem \ref{SmoothedChebyshevClose}), the distance from
    $\mathcal{M}(\widetilde{1_{\epsilon}})(1)$ to $1$ (Lemma \ref{MellinOfSmooth1c}) and the
    contour bound are each $O(x(\log x)^kT^{-1/2})$, and $T^{-1/2}\le 2\exp(-\omega_\eta(x)/4)$.
    The powers of $\log x$ are absorbed into the exponential. The case $a=\Lambda$ follows from
    the lower bound for $\omega_\eta$ in Definition \ref{InghamExponent}.
  -/)
  (latexEnv := "theorem")]
  TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion

/-- *** Prime Number Theorem (Medium Strength) *** The `Chebyshev.psi` function is asymptotic to `x`. -/
@[blueprint
  (title := "MediumPNT")
  (statement := /--
    We have
    $$\sum_{n \leq x}\Lambda(n)=x+O(x \exp(-c(\log x)^{1/10})).$$
  -/)
  (proof := /--
    This follows as a corollary of Theorem \ref{StrongPNT}, since
    $(\log x)^{1/10}\le(\log x)^{1/2}$ for $x\ge e$. -/)]
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, h⟩ := StrongPNT
  refine ⟨c, hc, h.trans (Asymptotics.IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 ≤ x := (Real.exp_pos 1).le.trans hx
  have hlog : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0
  have := Real.rpow_le_rpow_of_exponent_le hlog (show (1 : ℝ) / 10 ≤ 1 / 2 by norm_num)
  nlinarith

/-- info: 'MediumPNT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MediumPNT
