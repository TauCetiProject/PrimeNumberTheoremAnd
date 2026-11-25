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
The 3-4-1 inequality also gives a lower bound for $|\zeta|$ to the right of the line
$\Re s=1$, which degrades only like a power of $\sigma-1$.
-/

/-- `ζ(σ + it) ≪ log |t|` for `3 < |t|` on `1 - A / log |t| ≤ σ ≤ 2`, from Tau Ceti's
`TauCeti.exists_norm_riemannZeta_le_mul_log`. -/
private lemma norm_riemannZeta_le_mul_log_abs :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_riemannZeta_le_mul_log 1
  refine ⟨1 / 2, ⟨by norm_num, le_rfl⟩, 2 * max C 1, by positivity, fun σ t ht hσ ↦ ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
  have h2 : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
    rw [show 2 * Real.log |t| = Real.log (|t| ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hre : (σ + t * I : ℂ).re = σ := by simp
  have him : (σ + t * I : ℂ).im = t := by simp
  have hσ' : 1 - 1 / Real.log (|t| + 2) ≤ (σ + t * I : ℂ).re := by
    rw [hre]
    refine le_trans (sub_le_sub_left ?_ 1) hσ.1
    rw [div_le_div_iff₀ hlog hlog2]
    linarith
  have h := hC (σ + t * I) (by rw [him]; linarith) (by rw [him]; exact hσ')
  rw [him] at h
  calc ‖ζ (σ + t * I)‖ ≤ max C 1 * Real.log (|t| + 2) :=
        h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog2.le)
    _ ≤ max C 1 * (2 * Real.log |t|) := by gcongr
    _ = 2 * max C 1 * Real.log |t| := by ring

/-- `‖ζ(σ)‖ ≤ 2 / (σ - 1)` for `1 < σ ≤ 2`, from
`TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one`. -/
private lemma norm_riemannZeta_le_div_sub_one :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1) := by
  refine ⟨2, two_pos, fun σ hσ ↦ ?_⟩
  have h := TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one (s := σ) (by simpa using hσ.1)
  have h1 : 0 < σ - 1 := sub_pos.2 hσ.1
  rw [ofReal_re] at h
  have h2 : 1 ≤ 1 / (σ - 1) := by rw [le_div_iff₀ h1]; linarith [hσ.2]
  rw [show (2 : ℝ) / (σ - 1) = 1 / (σ - 1) + 1 / (σ - 1) by ring]
  linarith

theorem ZetaLowerBound1_aux1 {σ t : ℝ} (this : 1 ≤ ‖ζ σ‖ ^ (3 : ℝ) * ‖ζ (σ + I * t)‖ ^ (4 : ℝ) * ‖ζ (σ + 2 * I * t)‖) :
  ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  use (one_le_pow_iff_of_nonneg (by bound) four_ne_zero).1 (by_contra (this.not_gt ∘ ?_))
  simp_rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num [mul_right_comm, mul_comm (t : ℂ), mul_pow]

lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  -- Start with the fundamental identity
  have := DirichletCharacter.norm_LFunction_product_ge_one (1 : DirichletCharacter ℂ 1)
    (x := σ - 1) (by linarith) t
  simp only [DirichletCharacter.LFunctionTrivChar, one_pow,
    DirichletCharacter.LFunction_modOne_eq] at this
  simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast]
    at this
  apply ZetaLowerBound1_aux1 this

lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖ζ (σ + t * I)‖ := by
  have := ZetaLowerBound1 (t := t) σ_gt
  exact (div_le_iff₀' (pos_of_mul_pos_left (one_pos.trans_le this) (norm_nonneg _) ) ).mpr this

@[blueprint
  (title := "ZetaInvBound1")
  (statement := /--
  For all $\sigma>1$,
  $$
  1/|\zeta(\sigma+it)| \le |\zeta(\sigma)|^{3/4}|\zeta(\sigma+2it)|^{1/4}
  $$
  -/)
  (proof := /--
  The identity
  $$
  1 \le |\zeta(\sigma)|^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)|
  $$
  for $\sigma>1$
  is already proved by Michael Stoll in the EulerProducts PNT file.
  -/)
  (latexEnv := "lemma")]
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖ζ (σ + t * I)‖ ≤ ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  exact (div_le_iff₀ (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re
    (by simp [σ_gt])))).2 (ZetaLowerBound1 σ_gt)

theorem ZetaLowerBound3_aux3 (C : ℝ) (c_near : ℝ) {σ : ℝ} (t : ℝ) (σ_gt : 1 < σ) :
  c_near ^ ((3 : ℝ) / 4) * ((-1 + σ) ^ ((3 : ℝ) / 4))⁻¹ * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) =
    c_near ^ ((3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) * (-1 + σ) ^ (-(3 : ℝ) / 4) := by
  exact (symm) (.trans (by rw [neg_div, Real.rpow_neg (by linarith)]) (by ring))

theorem ZetaLowerBound3_aux4 (C : ℝ) (hC : 0 < C)
  (c_near : ℝ) (hc_near : 0 < c_near) {σ : ℝ} (t : ℝ) (ht : 3 < |t|)
  (σ_gt : 1 < σ)
   :
  0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |2 * t| ^ ((1 : ℝ) / 4) := by
  match sub_pos.mpr σ_gt with | S => match Real.log_pos (by simp; linarith : abs (2 *t) > 1) with | S => positivity

@[blueprint
  (title := "ZetaLowerBound3")
  (proofUses := ["ZetaInvBound1", "ZetaNear1BndExact", "ZetaUpperBnd"])
  (statement := /--
  There exists a $c>0$ such that for all $1 < \sigma <= 2$ and $3 < |t|$,
  $$
  c \frac{(\sigma-1)^{3/4}}{(\log |t|)^{1/4}} \le |\zeta(\sigma + tI)|.
  $$
  -/)
  (proof := /--
  Combine Lemma \ref{ZetaInvBound1} with upper bounds for
  $|\zeta(\sigma)|$ (from Lemma \ref{ZetaNear1BndExact}) and
  $|\zeta(\sigma+2it)|$ (from Lemma \ref{ZetaUpperBnd}).
  -/)
  (latexEnv := "lemma")]
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨A, ha, C, hC, h_upper⟩ := norm_riemannZeta_le_mul_log_abs
  obtain ⟨c_near, hc_near, h_near⟩ := norm_riemannZeta_le_div_sub_one

  use 1 / (c_near ^ ((3 : ℝ) / 4) * (2 * C) ^ ((1 : ℝ) / 4)), by positivity
  intro σ hσ t ht
  obtain ⟨σ_gt, σ_le⟩ := hσ

  -- Use ZetaLowerBound2, the reciprocal form of `ZetaInvBound1`
  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower

  -- Now we need to bound the denominator from above
  -- This will give us a lower bound on the whole expression

  -- Upper bound on ‖ζ σ‖ from ZetaNear1BndExact
  have ζ_σ_bound : ‖ζ σ‖ ≤ c_near / (σ - 1) := by
    exact h_near σ ⟨σ_gt, σ_le⟩

  have ht_2 : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith

  -- Upper bound on ‖ζ (σ + 2*t * I)‖ from ZetaUpperBnd

  have σ_in_range : σ ∈ Icc (1 - A / Real.log |2 * t|) 2 := by
    constructor
    · -- σ ≥ 1 - A / Real.log |2*t|
      have : 0 < A / Real.log |2 * t| := by
        exact div_pos ha.1 <| Real.log_pos (by linarith)
      nlinarith
    · exact σ_le

  have ζ_2t_bound := h_upper σ (2 * t) ht_2 σ_in_range

  -- Combine the bounds
  have denom_bound : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤
      (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul
    · apply Real.rpow_le_rpow (norm_nonneg _) ζ_σ_bound (by norm_num)
    · apply Real.rpow_le_rpow (norm_nonneg _) _ (by norm_num)
      convert ζ_2t_bound
      norm_cast
    · apply Real.rpow_nonneg (norm_nonneg _)
    · apply Real.rpow_nonneg (div_nonneg (by linarith) (by linarith))

  -- Simplify the bound
  have : (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) =
         c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
    exact ZetaLowerBound3_aux3 _ _ _ σ_gt
  rw [this] at denom_bound

  -- Take reciprocal (flipping inequality)
  have pos_left : 0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply ZetaLowerBound3_aux4 C hC c_near hc_near t ht σ_gt

  have pos_right : 0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
    -- This follows from ZetaLowerBound1 - if either factor were zero, we'd get 0 ≥ 1
    exact pos_of_mul_pos_left ((ZetaLowerBound1 σ_gt).trans_lt' zero_lt_one) (norm_nonneg _)


  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound).trans' ?_
  simp_rw [abs_mul, abs_two, neg_div, Real.rpow_neg (sub_pos.2 σ_gt).le] at *
  have hlog : 0 < Real.log |t| := Real.log_pos <| ht.trans' <| by norm_num
  have : 0 < Real.log |t| ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hlog2 : 0 < Real.log (2 * |t|) := Real.log_pos <| ht_2.trans' <| by norm_num
  have : 0 < Real.log (2 * |t|) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog2 (1 / 4)
  field_simp
  rw [Real.mul_rpow two_pos.le hC.le]
  move_mul [C ^ (1 / 4)]
  rw [mul_le_mul_iff_left₀]
  swap
  · positivity
  rw [← Real.mul_rpow two_pos.le hlog.le]
  apply Real.rpow_le_rpow hlog2.le ?_ (by norm_num)
  rw [← Real.log_rpow (ht.trans' (by norm_num))]
  apply Real.log_le_log (ht_2.trans' (by norm_num))
  rw [Real.rpow_two, sq]
  gcongr
  exact ht.trans' (by norm_num) |>.le

@[blueprint
  (title := "ZetaInvBound2")
  (statement := /--
  For $\sigma>1$ (and $\sigma \le 2$),
  $$
  1/|\zeta(\sigma+it)| \ll (\sigma-1)^{-3/4}(\log |t|)^{1/4},
  $$
  as $|t|\to\infty$.
  -/)
  (proof := /--
  Combine Lemma \ref{ZetaInvBound1} with the bounds in Lemmata \ref{ZetaNear1BndExact} and
  \ref{ZetaUpperBnd}.
  -/)
  (latexEnv := "lemma")]
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨c, hc, hbound⟩ := ZetaLowerBound3
  refine ⟨c⁻¹, inv_pos.mpr hc, fun {σ} hσ t ht ↦ ?_⟩
  have hp : 0 < c * (σ - 1) ^ ((3 : ℝ) / 4) / Real.log |t| ^ ((1 : ℝ) / 4) := by
    apply div_pos (mul_pos hc (Real.rpow_pos_of_pos (sub_pos.mpr hσ.1) _))
    exact Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  calc
    1 / ‖ζ (σ + t * I)‖ ≤
        1 / (c * (σ - 1) ^ ((3 : ℝ) / 4) / Real.log |t| ^ ((1 : ℝ) / 4)) :=
      one_div_le_one_div_of_le hp (hbound hσ t ht)
    _ = _ := by
      rw [neg_div, Real.rpow_neg (sub_pos.mpr hσ.1).le]
      field_simp


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
