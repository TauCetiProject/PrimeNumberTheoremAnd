module

public import Architect
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.WeakPNT
public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
public import TauCeti.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.NthPrime
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Liouville
import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.GramTao
import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.PrimeNumberTheorem



@[expose] public section


open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

@[blueprint
  (title := "finsum-range-eq-sum-range")
  (statement := /--
   For any arithmetic function $f$ and real number $x$, one has
  $$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
  and
  $$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
  -/)
  (proof := /-- Straightforward: both follow from Mathlib's `finsum_cond_eq_sum_of_cond_iff`, with
  `Nat.le_floor_iff'` and `Nat.lt_ceil` respectively. The formal statement is the second identity. -/)
  (latexEnv := "lemma")]
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

blueprint_comment /--
\label{WeakPNT}
The Chebyshev function satisfies $\psi(x) \sim x$.
This is Mathlib's `Chebyshev.isEquivalent_psi_id`.
-/

blueprint_comment /--
\label{chebyshev-asymptotic}
One has $\sum_{p \leq x} \log p = x + o(x)$.
This is Mathlib's `Chebyshev.isEquivalent_theta_id`.
-/

-- one could also consider adding a version with p < x instead of p \leq x


@[blueprint
  (title := "primorial-bounds")
  (statement := /--
  We have
    $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
  -/)
  (proof := /-- Exponentiate Theorem \ref{chebyshev-asymptotic}. -/)
  (latexEnv := "corollary")]
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  use (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p - x)
  constructor
  · exact Asymptotics.IsEquivalent.isLittleO Chebyshev.isEquivalent_theta_id
  intro x
  simp only [cast_prod, add_sub_cancel, exp_sum]
  apply Finset.prod_congr rfl
  intros x hx
  rw[Real.exp_log]
  rw[Finset.mem_filter] at hx
  norm_cast
  exact Nat.Prime.pos hx.right

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.le,
    ← TauCeti.Real.logIntegral_def]
  exact (div_pos (sub_pos.mpr hx) (log_pos (one_lt_two.trans hx))).trans_le
    (TauCeti.Real.le_logIntegral hx.le)

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  have hpi := Nat.isEquivalent_primeCounting
  have hli : (fun x : ℝ ↦ ∫ t in Set.Icc 2 x, 1 / log t) ~[atTop]
      (fun x : ℝ ↦ x / log x) := by
    refine TauCeti.Real.logIntegral_isEquivalent_div_log.congr_left ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [TauCeti.Real.logIntegral_def, intervalIntegral.integral_of_le hx,
      integral_Icc_eq_integral_Ioc]
    simp only [one_div]
  have hratio := (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    simpa only [one_div] using (integral_log_inv_pos x hx).ne')).mp (hpi.trans hli.symm)
  exact (isLittleO_one_iff ℝ).mpr (by simpa only [sub_self, Pi.div_apply] using hratio.sub_const (1 : ℝ))

@[blueprint
  (title := "pi-asymp")
  (statement := /--
  There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.
  -/)
  (proof := /--
  We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev-asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
  -/)]
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

@[blueprint
  (title := "pi-alt")
  (statement := /--
    One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.
  -/)
  (proof := /--
  An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
  -/)
  (latexEnv := "corollary")]
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  refine ⟨fun x ↦ (log x / x) * ⌊x⌋₊.primeCounting - 1, ?_, ?_⟩
  · have hratio := (isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact (div_pos (zero_lt_one.trans hx) (log_pos hx)).ne')).mp
        Nat.isEquivalent_primeCounting
    refine (isLittleO_one_iff ℝ).mpr ?_
    convert hratio.sub_const (1 : ℝ) using 1 <;>
      simp only [sub_self, Pi.div_apply, div_div_eq_mul_div, mul_div_assoc, mul_comm]
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

@[blueprint
  (title := "pn-asymptotic")
  (statement := /--
   One has
    $$ p_n = (1+o(1)) n \log n$$
  as $n \to \infty$.
  -/)
  (proof := /--
    Use Corollary \ref{pi_alt} to show that $n=\pi(p_n)\sim p_n/\log p_n$
    Taking logs gives $\log n \sim \log p_n - \log\log p_n \sim \log p_n$.
    Multiplying these gives $p_n\sim n\log n$ from which the result follows.
  -/)
  (latexEnv := "proposition")]
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (Nat.nth Nat.Prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  apply isLittleO_of_tendsto
  · simp
  simp only [div_one]
  unfold c
  have := isEquivalent_iff_tendsto_one ?_|>.mp Nat.isEquivalent_nth_prime
  swap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp
    norm_cast
    grind
  convert! this.add_const (-1 : ℝ) using 2
  norm_num


@[blueprint
  (title := "pn-pn-plus-one")
  (statement := /--
  We have $p_{n+1} - p_n = o(p_n)$
    as $n \to \infty$.
  -/)
  (proof := /-- Easy consequence of preceding proposition. -/)
  (latexEnv := "corollary")]
theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  have hne (n : ℕ) : (Nat.nth Nat.Prime n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.prime_nth_prime n).ne_zero
  have hratio := (isEquivalent_iff_tendsto_one (Eventually.of_forall hne)).mp
    Nat.isEquivalent_nth_prime_succ
  refine ⟨fun n ↦ ((Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n) /
    Nat.nth Nat.Prime n, (isLittleO_one_iff ℝ).mpr ?_, ?_⟩
  · have hzero := hratio.sub_const (1 : ℝ)
    simp only [sub_self] at hzero
    apply hzero.congr
    intro n
    simp only [Pi.div_apply, sub_div, div_self (hne n)]
  · intro n
    exact (div_mul_cancel₀ _ (hne n)).symm

@[blueprint
  (title := "prime-between")
  (statement := /-- For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for
  all sufficiently large $x$. -/)
  (proof := /-- Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity
  as $x \to \infty$. -/)
  (latexEnv := "corollary")]
theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  filter_upwards [Nat.eventually_exists_prime_mem_Ioc (show 0 < ε / 2 by linarith),
    eventually_gt_atTop (0 : ℝ)] with x ⟨p, hp, hxp, hpx⟩ hx
  exact ⟨p, hp, hxp, hpx.trans_lt (by nlinarith)⟩


attribute [blueprint
  "mun"
  (statement := /-- We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$. -/)
  (proof := /--
  From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
    $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
    $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
    and the claim follows. Tau Ceti proves this as the case of all primes of Tao's bound
    $|\sum_{n \leq x,\ n \in \langle S \rangle} \mu(n)/n| \leq 1$ for every set $S$ of primes.
  -/)
  (latexEnv := "proposition")]
  TauCeti.abs_moebiusDivSum_le_one


attribute [blueprint
  "mu-pnt"
  (title := "M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n) = o(x)$. -/)
  (proof := /--
  From the Dirichlet convolution identity
    $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
  and summing we obtain
  $$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
  For any $\eps>0$, we have from the prime number theorem that
  $$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
  (divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
  We conclude that
  $$ \sum_{n \leq x} \mu(n) \log n
    = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
  Applying \eqref{mun} we conclude that
  $$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
  and hence
  $$ \sum_{n \leq x} \mu(n) \log x
    = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
  From Stirling's formula one has
  $$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
  thus
  $$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
  and thus
  $$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
  Sending $\eps \to 0$ we obtain the claim.
  -/)
  (proofUses := ["WeakPNT", "mun"])
  (latexEnv := "proposition")]
  TauCeti.moebiusSum_isLittleO


@[blueprint
  "lambda-pnt"
  (statement := /-- We have $\sum_{n \leq x} \lambda(n) = o(x)$. -/)
  (proof := /--
  From the identity
    $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
  and summing, we have
  $$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
  For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
  $$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
  and hence on summing in $d$
  $$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
  Sending $\eps \to 0$ we obtain the claim. This transfer from $M(x)=o(x)$ is Tau Ceti's
  \texttt{TauCeti.liouvilleSum\_isLittleO\_iff}.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  have hL : TauCeti.liouvilleSum =o[atTop] fun x ↦ x := TauCeti.liouvilleSum_isLittleO
  have hb : (fun x : ℝ ↦ 1 - (-1 : ℝ) ^ Ω ⌊x⌋₊) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
    refine IsBigO.of_bound 2 (Eventually.of_forall fun x ↦ ?_)
    rcases neg_one_pow_eq_or ℝ (Ω ⌊x⌋₊) with h | h <;> norm_num [h]
  have hr : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1 : ℝ) ^ Ω n) =o[atTop] fun x ↦ x := by
    refine (hL.add (hb.trans_isLittleO (isLittleO_const_id_atTop (1 : ℝ)))).congr' ?_ .rfl
    filter_upwards [eventually_ge_atTop 1] with x hx
    have h1 := Finset.sum_range_succ (fun n ↦ (-1 : ℝ) ^ Ω n) ⌊x⌋₊
    rw [Finset.sum_range_succ', cardFactors_zero, pow_zero] at h1
    have h2 : ∑ n ∈ Icc 1 ⌊x⌋₊, (-1 : ℝ) ^ Ω n = ∑ k ∈ range ⌊x⌋₊, (-1 : ℝ) ^ Ω (k + 1) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n ↦ (-1 : ℝ) ^ Ω n), zero_add,
        Finset.Ico_add_one_right_eq_Icc]
    rw [TauCeti.liouvilleSum_def, Finset.sum_congr rfl fun n hn ↦
      show (liouville n : ℝ) = (-1 : ℝ) ^ Ω n by
        rw [liouville_apply (by simp at hn; omega)]; push_cast; rfl]
    linarith
  rw [← isLittleO_norm_left] at hr ⊢
  simpa only [← Int.norm_cast_real, Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one]
    using hr


attribute [blueprint
  "mu-pnt-alt"
  (title := "Alternate M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n)/n = o(1)$. -/)
  (proof := /--
  Let $N$ and $K$ be natural numbers. As in the proof of Theorem \ref{mun}, we have
    $$ 1 = \sum_{n \leq KN} \mu(n) \left\lfloor \frac{KN}{n} \right\rfloor.$$
  In the terms with $n \leq N$, write $\lfloor KN/n \rfloor = KN/n - \{KN/n\}$; these
  contribute $KN \sum_{n \leq N} \frac{\mu(n)}{n} + O(N)$. In the terms with
  $N < n \leq KN$, write $\lfloor KN/n \rfloor$ as the number of $1 \leq j < K$ with
  $n \leq KN/j$ and swap the sums; these contribute
  $$ \sum_{1 \leq j < K} \sum_{N < n \leq KN/j} \mu(n)
    = \sum_{1 \leq j < K} \left(M(KN/j) - M(N)\right).$$
  Hence
  $$ KN \left|\sum_{n \leq N} \frac{\mu(n)}{n}\right|
    \leq 1 + N + \sum_{1 \leq j < K} \left(|M(KN/j)| + |M(N)|\right).$$
  By Theorem \ref{mu-pnt}, for any $\eps > 0$ the right-hand side is at most
  $1 + N + \eps K^2 N$ once $N$ is large depending on $K$ and $\eps$, so
  $|\sum_{n \leq N} \mu(n)/n| \leq 2/K + \eps K$. Taking $K$ large and then $\eps$ small
  gives the claim along the integers, and hence for real $x$.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
  TauCeti.tendsto_moebiusDivSum_atTop_zero


blueprint_comment /--
\section{Consequences of the PNT in arithmetic progressions}
-/

blueprint_comment /--
\label{chebyshev-asymptotic-pnt}
If $a\ (q)$ is a primitive residue class, then
$\sum_{p \leq x: p = a\ (q)} \log p = x/\phi(q) + o(x)$.
This is Mathlib's `Chebyshev.tendsto_sum_log_prime_modEq_div_atTop`.
-/

blueprint_comment /--
\label{dirichlet_thm}
Any primitive residue class contains infinitely many primes. This is Mathlib's
`Nat.infinite_setOfPred_prime_and_modEq`; converting the set to its subtype and
using the reduced residue representative gives the natural-modulus form.
-/

blueprint_comment /--
\section{Consequences of the Chebotarev density theorem}

-/

blueprint_comment /--
\begin{lemma}[Cyclotomic Chebotarev]\label{Chebotarev-cyclic}
Let $m\geq 1$ and $G = \mathrm{Gal}(\mathbb{Q}(\mu_m)/\mathbb{Q}) \cong (\mathbb{Z}/m\mathbb{Z})^\times$.
For any $a$ coprime to $m$,
\[
\sum_{\substack{N\mathfrak{p}\leq x\\ N\mathfrak{p}\equiv a\pmod{m}}} \log N\mathfrak{p}
\;=\;
\frac{1}{|G|} \sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}
\;+\; o\Bigl(\sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}\Bigr).
\]
In particular the primes in the progression $a\pmod{m}$ have natural density $1/\varphi(m)$
(Dirichlet's theorem).
\end{lemma}
-/

blueprint_comment /--
\begin{proof}\uses{Chebotarev-cyclotomic-density, Dedekind-PNT, WeakPNT-AP}
Specialise Proposition~\ref{Chebotarev-cyclotomic-density} to $K=\mathbb{Q}$ and
$L=\mathbb{Q}(\mu_m)$: the Frobenius condition $\varphi_p=\sigma_a$ with
$\sigma_a(\zeta_m)=\zeta_m^a$ is exactly $p\equiv a\pmod{m}$.  The asymptotic form with
$\log N\mathfrak{p}$ follows by Fourier expansion of the indicator of the progression against
characters of $G$, using Lemma~\ref{Dedekind-PNT} to kill the nontrivial character sums and
the prime-number theorem in AP (Lemma~\ref{WeakPNT-AP}) for the main term.  Cf.\ also
Corollary~7.2.3 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.
\end{proof}
-/
