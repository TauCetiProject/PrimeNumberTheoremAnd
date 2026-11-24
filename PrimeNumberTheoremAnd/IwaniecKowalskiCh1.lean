/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
module

public import Architect
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.Data.Finset.NatDivisors
public import TauCeti.NumberTheory.ArithmeticFunction.Additive
public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.LSeries.Liouville
public import TauCeti.NumberTheory.LSeries.Moebius
public import TauCeti.NumberTheory.LSeries.Totient
import TauCeti.NumberTheory.ArithmeticFunction.Zeta
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Complex
public import TauCeti.NumberTheory.LSeries.TwoPowOmega
import TauCeti.NumberTheory.LSeries.Divisor.Basic
import TauCeti.NumberTheory.LSeries.Divisor.PowerSum
import TauCeti.NumberTheory.LSeries.Zeta.Pow


@[expose] public section

blueprint_comment /--
\label{IsCompletelyMultiplicative}
\paragraph{IsCompletelyMultiplicative}
Define Complete Multiplicativity for an arithmetic function.
-/

blueprint_comment /--
\label{IsCompletelyMultiplicative.isMultiplicative}
\paragraph{IsCompletelyMultiplicative.isMultiplicative}
A function that is completely multiplicative is also multiplicative.

Let $f$ be a completely multiplicative function. To show that $f$ is multiplicative, we need to verify that $f(1) = 1$ and that $f(ab) = f(a)f(b)$ for all coprime natural numbers $a$ and $b$. Since $f$ is completely multiplicative, we have $f(1) = 1$ by definition. For coprime $a$ and $b$, we can write $ab$ as a product of prime factors, and since $f$ is completely multiplicative, it will factor as the product of the values of $f$ at those prime factors. This means that $f(ab) = f(a)f(b)$ for coprime $a$ and $b$, which shows that $f$ is multiplicative.
-/

blueprint_comment /--
\label{sum_divisors_mul_of_coprime}
If $f$ is a multiplicative arithmetic function, then for coprime, nonzero $a$ and $b$, we have that
  $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$.
  \begin{verbatim}
  This has been upstreamed #36495.
  \end{verbatim}

Since $f$ is multiplicative, we can express the sum over divisors of $ab$ in terms of the sums over divisors of $a$ and $b$. The key idea is to use the fact that the divisors of $ab$ can be expressed as products of divisors of $a$ and divisors of $b$, due to the coprimality condition. Specifically, each divisor $d$ of $ab$ can be uniquely written as $d = d_a * d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. Therefore, we can rewrite the sum as a double sum over the divisors of $a$ and $b$, which factorizes into the product of the two separate sums.
-/

blueprint_comment /--
\label{sum_moebius_pmul_eq_prod_one_sub}
If $g$ is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$.
      \begin{verbatim}
  Upstream issue has been created #1240.
  \end{verbatim}

Multiply out and collect terms.
-/

blueprint_comment /--
\label{zeta_pow_three_eq'}
Zeta cubed: $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty}\tau(n^2) n^{-s}$.
  \begin{verbatim}
  This is IK (1.30).
  \end{verbatim}

This follows from the previous two theorems. From the corollary of Ramanujan's formula, we have $\zeta(s)^4 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$. From the Baby Rankin-Selberg result, we have $\zeta(s) \sum_{n=1}^{\infty} \tau(n^2) n^{-s} = \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$. Combining these two results, we can express $\zeta(s)^4$ in terms of $\zeta(s)$ and $\sum_{n=1}^{\infty} \tau(n^    2) n^{-s}$, which leads to the conclusion that $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n^2) n^{-s}$.
-/

blueprint_comment /--
\label{LSeries.term_isMultiplicative_if_fun_isMultiplicative}
If $f$ is a multiplicative function, then so to is $n\mapsto f(n)/n^s$.

Note that $f(mn)/(mn)^s=f(m)f(n)/(m^sn^s)=(f(m)/m^s)(f(n)/n^s)$.
-/

blueprint_comment /--
\label{two_pow_omega_LSeries.term_isMultiplicative}
We have that $n\mapsto 2^{\omega(n)}/n^{s}$ is a multiplicative function.

Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{two-pow-omega-isMultiplicative}.
-/

blueprint_comment /--
\label{moebius_sq_LSeries.term_isMultiplicative}
We have that $n\mapsto \mu^2(n)/n^{s}$ is a multiplicative function.

Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{moebius-sq-isMultiplicative}.
-/

blueprint_comment /--
\label{divisors_mul_injective}
Let $m$ and $n$ be coprime natural numbers. The function $(a,b) \mapsto ab$ is injective on the
    product of the divisors of $m$ and $n$.
    \begin{verbatim}
    Upstreamed to mathlib via PR #36495.
    \end{verbatim}

Since $m$ and $n$ are coprime, any element in the product of their divisors can be uniquely
    expressed as a product of an element from each set. The injectivity follows from the uniqueness
    of this decomposition.
-/

blueprint_comment /--
\label{liouville}
Liouville function: $\lambda(n) = (-1)^{\Omega(n)}$.

The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ is the total number of prime factors of $n$ counted with multiplicity. This means that for each prime factor of $n$, we contribute a factor of $-1$ to the product, and the overall sign of $\lambda(n)$ depends on whether the total number of prime factors is even or odd. Thus, we have $\lambda(n) = (-1)^{\Omega(n)}$ by definition.
-/


open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

open scoped ArithmeticFunction.Moebius

open scoped LSeries.notation

namespace ArithmeticFunction

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
Here we collect facts from Chapter 1 that are not already in Mathlib.
We will try to upstream as much as possible.
-/

/-- `τ` (tau) is the divisor count function, equal to `σ 0`. -/
abbrev tau : ArithmeticFunction ℕ := σ 0

@[inherit_doc tau]
scoped notation "τ" => tau

variable {R : Type*}

attribute [blueprint
  "IsAdditive"
  (title := "IsAdditive")
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
  IsAdditiveOnCoprime

@[blueprint
  "IsCompletelyAdditive"
  (title := "IsCompletelyAdditive")
  (statement := /-- Completely additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for all $m, n \ne 0$. -/)]
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive.isAdditive"
  (title := "IsCompletelyAdditive.isAdditive")
  (statement := /-- A completely additive function is additive. -/)]
lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditiveOnCoprime f :=
  ⟨fun hm hn _ ↦ hf hm hn⟩

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

attribute [blueprint
  "unique_divisor_decomposition"
  (title := "unique divisor decomposition")
  (statement := /-- If $a$ and $b$ are coprime, then any divisor $d$ of $ab$ can be uniquely expressed as a product of a divisor of $a$ and a divisor of $b$.
    \begin{verbatim}
  This has been upstreamed #36495.
  \end{verbatim}
-/)
  (proof := /--
  Let $a$ and $b$ be coprime natural numbers, and let $d$ be a divisor of $ab$. Since $a$ and $b$ are coprime, we can use the fact that the divisors of $ab$ correspond to pairs of divisors of $a$ and $b$. Specifically, we can express $d$ as $d = d_a \cdot d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. The uniqueness of this decomposition follows from the coprimality of $a$ and $b$, which ensures that the divisors of $a$ and $b$ do not share any common factors. Therefore, there is a one-to-one correspondence between the divisors of $ab$ and the pairs of divisors of $a$ and $b$, which guarantees the uniqueness of the decomposition.
  -/)]
  Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime

blueprint_comment /--
For a multiplicative arithmetic function, its divisor sum is multiplicative. This is Mathlib's
multiplicativity of convolution with the constant-one arithmetic function. The Möbius-weighted
divisor sum is the product over prime factors of one minus the function value; Mathlib supplies
this as `IsMultiplicative.prodPrimeFactors_one_sub`.
-/

attribute [blueprint
  "zeta_mul_zeta"
  (title := "zeta mul zeta")
  (statement := /-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/)
  (proof := /--
  By definition of $\zeta$, we have $\zeta(n) = 1$ for all $n \geq 1$. Thus, the Dirichlet convolution
  $(\zeta * \zeta)(n)$ counts the number of ways to write $n$ as a product of two positive integers,
  which is exactly the number of divisors of $n$, i.e., $\tau(n)$.
  -/)]
  ArithmeticFunction.zeta_mul_pow_eq_sigma

/-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/
@[blueprint
  "LSeries_tau_eq_riemannZeta_sq"
  (title := "LSeries tau eq riemannZeta sq")
  (statement := /-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/)
  (proof := /--
  From the previous theorem, we have that the Dirichlet convolution of $\zeta$ with itself is $\tau$.
  Taking L-series on both sides, we get $L(\tau, s) = L(\zeta, s) \cdot L(\zeta, s)$.
  Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, we conclude that
  $L(\tau, s) = \zeta(s)^2$ for $\Re(s) > 1$.
  -/)]
theorem LSeries_tau_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗τ) s = riemannZeta s ^ 2 := by
  rw [← (LSeriesHasSum_zeta_pow 2 hs).LSeries_eq, tau, ← zeta_mul_pow_eq_sigma,
    pow_zero_eq_zeta, ← sq]

blueprint_comment /--
\label{d}
\paragraph{d}
 $d_k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/

blueprint_comment /--
\label{d_zero}
\paragraph{d zero}
 $d_0$ is the multiplicative identity (indicator at 1). \paragraph{Proof}
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/

blueprint_comment /--
\label{d_one}
\paragraph{d one}
 $d_1$ is $\zeta$. \paragraph{Proof}
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d_1 = \zeta^1 = \zeta$.
  -/

blueprint_comment /--
\label{d_two}
\paragraph{d two}
 $d_2$ is the classical divisor count function $\tau$. \paragraph{Proof}
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d_2 = \zeta^2 = \tau$.
  -/

blueprint_comment /--
\label{d_succ}
\paragraph{d succ}
 Recurrence: $d_{k+1} = d_k * \zeta$. \paragraph{Proof}
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d_{k + 1}$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d_k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d_{k + 1} = d_k * \zeta$.
  -/

/-- The L-series of every convolution power of zeta converges for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_summable"
  (title := "LSeries d summable")
  (statement := /-- The L-series for $d_k$ is summable for $\Re(s) > 1$. -/)
  (proof := /--
  Since $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$, and we know that the L-series of $\zeta$ converges for $\Re(s) > 1$, it follows that the L-series of $d_k$ also converges for $\Re(s) > 1$. This is because the convolution of functions with convergent L-series will also have a convergent L-series in the same region. Therefore, we can conclude that $L(d_k, s)$ is summable for $\Re(s) > 1$.
  -/)]
theorem LSeriesSummable_zeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (↗((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s :=
  (LSeriesHasSum_zeta_pow k hs).LSeriesSummable

/-- The L-series of a convolution power of zeta equals the corresponding power of Riemann zeta. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (title := "LSeries d eq riemannZeta pow")
  (statement := /-- The $L$-series of $d_k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d_k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d_k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d_k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_zeta_pow_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(ζ ^ k : ArithmeticFunction ℕ)) s = riemannZeta s ^ k :=
  (LSeriesHasSum_zeta_pow k hs).LSeries_eq


blueprint_comment /--
\label{d_isMultiplicative}
\paragraph{d isMultiplicative}
 $d_k$ is multiplicative for all $k$. \paragraph{Proof}
  The function $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$. Since $\zeta$ is a multiplicative function, and the Dirichlet convolution of multiplicative functions is also multiplicative, it follows that $d_k$ is multiplicative for all $k$. This can be shown by induction on $k$, using the fact that the convolution of a multiplicative function with another multiplicative function remains multiplicative.
  -/

blueprint_comment /--
\label{d_apply_prime_pow}
\paragraph{d apply prime pow}
 Explicit formula: $d_k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. \paragraph{Proof}
  The function $d_k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/

blueprint_comment /--
\label{d_apply}
\paragraph{d apply}
 (1.25) in Iwaniec-Kowalski: a formula for $d_k$ for all $n$. \paragraph{Proof}
  The function $d_k$ is multiplicative, so to compute $d_k(n)$ for a general natural number $n$, we can factor $n$ into its prime power decomposition: $n = p_1^{a_1} p_2^{a_2} ... p_m^{a_m}$. Since $d_k$ is multiplicative, we have:

  \[
  d_k(n) = d_k(p_1^{a_1}) \cdot d_k(p_2^{a_2}) \cdot ... \cdot d_k(p_m^{a_m})
  \]

  Using the explicit formula for prime powers from the previous theorem, we can substitute to get:

  \[
  d_k(n) = \prod_{i=1}^{m} (a_i + k - 1).choose (k - 1)
  \]

  This gives us a complete formula for $d_k(n)$ in terms of the prime factorization of $n$.
  -/

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
@[blueprint
  "sigmaR"
  (title := "sigmaR")
  (statement := /-- Divisor power sum with complex exponent. -/)]
noncomputable def sigmaR {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- For natural exponents, sigmaR agrees with sigma. -/
@[blueprint
  "sigmaR_natCast"
  (title := "sigmaR-natCast")
  (statement := /-- For natural exponents, $\sigma^R$ agrees with $\sigma$. -/)
  (proof := /--
  The function $\sigma^R$ is defined as the sum of the $s$-th powers of the divisors of $n$. When
  $s$ is a natural number $k$, this definition coincides with the classical divisor power sum
  function $\sigma_k(n)$, which also sums the $k$-th powers of the divisors of $n$. Therefore, for
  natural exponents, we have $\sigma^R_k(n) = \sigma_k(n)$ when we view $\sigma_k(n)$ as a complex
  number. This can be shown by directly comparing the definitions and noting that both functions sum
  over the same set of divisors with the same exponentiation.
  -/)]
lemma sigmaR_natCast (k n : ℕ) :
    σᴿ k n = σ k n := by
  unfold sigmaR sigma
  simp only [cast_id, coe_mk]

@[blueprint
  "sigmaR_apply"
  (title := "sigmaR-apply")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}d^s.$
  -/)
  (proof := /--
    This follows immediately from the definition.
  -/)]
lemma sigmaR_apply {n : ℕ} {s : ℂ} : σᴿ s n = ∑ d ∈ divisors n, (d : ℂ) ^ s := by
  rfl

@[blueprint
  "sigmaR_natCast'"
  (title := "sigmaR-natCast'")
  (statement := /--
    A casting lemma for $\sigma^R$.
  -/)]
lemma sigmaR_natCast' (k n : ℕ) :
    σᴿ (k : ℂ) n = σᴿ k n := by
  simp only [sigmaR_apply, Complex.cpow_natCast, sigmaR_natCast, sigma_apply, cast_sum, cast_pow]

@[blueprint
  "sigmaR_apply_prime_pow"
  (title := "sigmaR-apply-prime-pow")
  (statement := /--
    For a prime power, we have that $\sigma^R_s(p^i)=\sum_{j=0}^ip^{js}$.
  -/)
  (proof := /--
    Note that $d\mid p^i$ implies that $d=p^j$ with $0\leq j\leq i$. Thus,
    $$\sigma^R_s(p^i)=\sum_{d\mid p^i}d^s=\sum_{j=0}^i(p^j)^s=\sum_{j=0}^ip^{js}.$$
  -/)]
lemma sigmaR_apply_prime_pow {p i : ℕ} {s : ℂ} (hp : p.Prime) :
    σᴿ s (p ^ i) = ∑ j ∈ .range (i + 1), (p : ℂ) ^ (j * s) := by
  simp only [sigmaR_apply, divisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, cast_pow]
  congr 1
  funext x
  exact Eq.symm (Complex.natCast_cpow_natCast_mul p x s)

@[blueprint
  "sigmaR_one_apply"
  (title := "sigmaR-one-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply (n : ℕ) : σᴿ (1 : ℂ) n = ∑ d ∈ divisors n, d := by
  simp only [sigmaR_apply, Complex.cpow_one, cast_sum]

@[blueprint
  "sigmaR_one_apply_prime_pow"
  (title := "sigmaR-one-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (1 : ℂ) (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp only [sigmaR_apply_prime_pow hp, mul_one, Complex.cpow_natCast, cast_sum, cast_pow]

@[blueprint
  "sigmaR_eq_sum_div"
  (title := "sigmaR-eq-sum-div")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}(n/d)^s$.
  -/)
  (proof := /--
    Note that $d \mapsto n/d$ forms a one-to-one mapping between the divisors of $n$. Using this in
    combination with the definiton we have that
    $$\sigma^R_s(n)=\sum_{d\mid n}d^s=\sum_{d\mid n}(n/d)^s.$$
  -/)]
lemma sigmaR_eq_sum_div {n : ℕ} {s : ℂ} :
    σᴿ s n = ∑ d ∈ divisors n, ((n / d) : ℂ) ^ s := by
  rw[sigmaR_apply, ← sum_div_divisors]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw[Nat.cast_div (dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]

@[blueprint
  "sigmaR_zero_apply"
  (title := "sigmaR-zero-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply (n : ℕ) :
    σᴿ (0 : ℂ) n = #n.divisors := by
  simp only [sigmaR_apply, Complex.cpow_zero, sum_const, nsmul_eq_mul, mul_one]

@[blueprint
  "sigmaR_zero_apply_prime_pow"
  (title := "sigmaR-zero-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (0 : ℂ) (p ^ i) = i + 1 := by
  simp only [sigmaR_apply_prime_pow hp, mul_zero, Complex.cpow_zero, sum_const, card_range,
    nsmul_eq_mul, cast_add, cast_one, mul_one]

@[blueprint
  "sigmaR_one"
  (title := "sigmaR-one")
  (statement := /--
    We have that $\sigma^R_s(1)=1$.
  -/)
  (proof := /--
    By definition we have that
    $$\sigma^R_s(1)=\sum_{d \mid 1}d^s=1^s=1.$$
  -/)]
lemma sigmaR_one (s : ℂ) :
    σᴿ s 1 = 1 := by
  simp only [sigmaR_apply, divisors_one, sum_singleton, cast_one, Complex.one_cpow]

attribute [blueprint
  "powR"
  (title := "powR")
  (statement := /-- Arithmetic function with complex parameter $\nu$. Evaluates as $n\mapsto n^{\nu}$ for $n\neq 0$ and $0$ at $n=0$. -/)]
  TauCeti.ArithmeticFunction.cpow

attribute [blueprint
  "isMultiplicative_powR"
  (title := "isMultiplicative-powR")
  (statement := /--
    For fixed $\nu$ the function $n\mapsto n^\nu$ is multiplicative.
  -/)
  (proof := /--
    This immediately follows from the fact that exponentiation with a fixed power is a homomorphism.
  -/)]
  TauCeti.ArithmeticFunction.isMultiplicative_cpow

@[blueprint
  "sigmaR_eq_zeta_mul_powR"
  (title := "sigmaR-eq-zeta-mul-powR")
  (statement := /-- $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$, where $\zeta$ is the constant function $1$. -/)
  (proof := /--
  The function $\sigma^R(\nu)$ is defined as the sum of the $\nu$-th powers of the divisors of $n$. The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The Dirichlet convolution of $\zeta$ (the constant function $1$) and $\text{pow}^R(\nu)$ is exactly $\sigma^R(\nu)$, since for each divisor $d$ of $n$, we have $(\zeta * \text{pow}^R(\nu))(n) = \sum_{d|n} 1 \cdot d^\nu = \sigma^R(\nu)(n)$. Thus, we have $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$.
  -/)]
lemma sigmaR_eq_zeta_mul_powR (ν : ℂ) :
    sigmaR ν = (zeta : ArithmeticFunction ℂ) * TauCeti.ArithmeticFunction.cpow ν := by
  rw [← TauCeti.ArithmeticFunction.sigmaC_eq_zeta_mul_cpow]
  ext n
  rw [sigmaR_apply, TauCeti.ArithmeticFunction.sigmaC_apply]

@[blueprint
  "isMultiplicative_sigmaR"
  (title := "isMultiplicative-sigmaR")
  (statement := /--
    For fixed $s$ function $n\mapsto\sigma^R_s(n)$ is multiplicative.
  -/)
  (proof := /--
    Recall from Lemma \ref{sigmaR-eq-zeta-mul-powR} that $\sigma^R$ is $\zeta$ convolved with
    Definition \ref{powR}. Since both of these are multiplicative functions, their convolution is
    also multiplicative.
  -/)]
lemma isMultiplicative_sigmaR {s : ℂ} :
    IsMultiplicative (σᴿ s) := by
  rw [sigmaR_eq_zeta_mul_powR]
  exact isMultiplicative_zeta.natCast.mul (TauCeti.ArithmeticFunction.isMultiplicative_cpow s)

@[blueprint
  "sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul"
  (title := "sigmaR-eq-prod-primeFactors-sum-range-factorization-pow-mul")
  (statement := /--
    We have that
    $$\sigma^R_s(n)=\prod_{p\mid n}\sum_{j=0}^{v_p(n)}p^{js}.$$
  -/)
  (proof := /--
    Since $\sigma^R_s$ is multiplicative, it suffices to understand it at primes powers.
    $$\sigma^R_s(n)=\prod_{p\mid n}\sigma^R_s(p^{v_p(n)}).$$
    Applying Lemma \ref{sigmaR-apply-prime-pow}.
  -/)]
lemma sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul {n : ℕ} {s : ℂ} (hn : n ≠ 0) :
    σᴿ s n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), (p : ℂ) ^ (i * s) := by
  rw [isMultiplicative_sigmaR.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigmaR_apply_prime_pow <| prime_of_mem_primeFactors h

@[blueprint
  "LSeries_powR_eq"
  (title := "LSeries powR eq")
  (statement := /-- $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ for $\Re(s - \nu) > 1$.
  \begin{verbatim}
  This is IK (1.27).
  \end{verbatim}
  -/)
  (proof := /--
  The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The L-series of $\text{pow}^R(\nu)$ at $s$ is given by the sum $\sum_{n=1}^{\infty} n^{\nu - s}$. This series converges to the Riemann zeta function $\zeta(s - \nu)$ for $\Re(s - \nu) > 1$, since the zeta function is defined as $\zeta(s) = \sum_{n=1}^{\infty} n^{-s}$ for $\Re(s) > 1$. Therefore, we have $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ under the condition that $\Re(s - \nu) > 1$.
  -/)]
lemma LSeries_powR_eq (ν : ℂ) {s : ℂ} (hs : 1 < (s - ν).re) :
    LSeries (TauCeti.ArithmeticFunction.cpow ν) s = riemannZeta (s - ν) :=
  TauCeti.LSeries.LSeries_cpow (by rw [Complex.sub_re] at hs; linarith)

@[blueprint
  "abscissa_powR_le"
  (title := "abscissa powR le")
  (statement := /-- The abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$. -/)
  (proof := /--
  We apply \ref{LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow} which states that if there exists a constant $C$ such that $\|f(n)\| \leq C \cdot n^r$ for all $n$ sufficiently large, then the abscissa of absolute convergence of $L(f, s)$ is at most $r + 1$. In our case, we can take $f(n) = n^\nu$ and observe that $\|n^\nu\| = n^{\Re(\nu)}$. Thus, we can choose $C = 1$ and $r = \Re(\nu)$, which gives us the desired result that the abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$.
  -/)]
lemma abscissa_powR_le (ν : ℂ) :
    LSeries.abscissaOfAbsConv (TauCeti.ArithmeticFunction.cpow ν) ≤ ν.re + 1 := by
  rw [TauCeti.LSeries.abscissaOfAbsConv_cpow, add_comm]
  exact_mod_cast le_rfl

/-- `ζ(s)ζ(s - ν) = Σ σ_ν(n) n^(-s)` for `Re(s) > 1` and `Re(s - ν) > 1`. -/
@[blueprint
  "LSeries_sigma_eq_riemannZeta_mul"
  (title := "LSeries sigma eq riemannZeta mul")
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(σᴿ ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [sigmaR_eq_zeta_mul_powR, ← TauCeti.ArithmeticFunction.sigmaC_eq_zeta_mul_cpow]
  exact TauCeti.LSeries.LSeries_sigmaC (max_lt hs (by rw [Complex.sub_re] at hsν; linarith))

/-- The native fourth divisor-function coefficient dominates the squared divisor count. -/
private lemma ramanujan_square_le_choose (k : ℕ) : (k + 1) ^ 2 ≤ (k + 3).choose 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 * k + 3 ≤ (k + 3).choose 2 := by
      rw [Nat.choose_two_right]
      have h : 2 * (2 * k + 3) ≤ (k + 3) * (k + 3 - 1) := by
        have : k + 3 - 1 = k + 2 := by omega
        rw [this]
        nlinarith
      omega
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, Nat.choose_succ_succ]
    nlinarith

private lemma ramanujan_norm_sigmaR_le (α : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖sigmaR α n‖ ≤ (tau n : ℝ) * (n : ℝ) ^ max α.re 0 := by
  rw [sigmaR_apply]
  apply (norm_sum_le _ _).trans
  have hd (d : ℕ) (hd : d ∈ n.divisors) :
      ‖(d : ℂ) ^ α‖ ≤ (n : ℝ) ^ max α.re 0 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_mem_divisors hd)]
    apply (Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr (Nat.pos_of_mem_divisors hd)) (le_max_left α.re 0)).trans
    have hdn : (d : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd))
    exact Real.rpow_le_rpow (by positivity) hdn (le_max_right α.re 0)
  apply (Finset.sum_le_sum hd).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  simp [tau, sigma_zero_apply]

private lemma ramanujan_norm_sigma_product_le (α β : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖sigmaR α n * sigmaR β n‖ ≤ ((ζ ^ 4 : ArithmeticFunction ℕ) n : ℝ) *
      (n : ℝ) ^ (max α.re 0 + max β.re 0) := by
  rw [norm_mul]
  apply ((mul_le_mul (ramanujan_norm_sigmaR_le α hn) (ramanujan_norm_sigmaR_le β hn)
    (norm_nonneg _) (by positivity))).trans
  calc
    ((tau n : ℝ) * (n : ℝ) ^ max α.re 0) *
        ((tau n : ℝ) * (n : ℝ) ^ max β.re 0) =
        (tau n : ℝ)^2 * (n : ℝ) ^ (max α.re 0 + max β.re 0) := by
      rw [Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast sigma_zero_sq_le_zeta_pow_four n)
      (Real.rpow_nonneg (by positivity) _)

/-- The four original half-plane hypotheses give absolute convergence for complex parameters. -/
private lemma ramanujan_product_sigma_summable (α β s : ℂ)
    (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    LSeriesSummable (fun n ↦ sigmaR α n * sigmaR β n) s := by
  let ρ := max α.re 0 + max β.re 0
  have hr : 1 < (s - (ρ : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re] at *
    dsimp only [ρ]
    rcases le_total α.re 0 with ha | ha <;> rcases le_total β.re 0 with hb | hb
    · simpa only [max_eq_right ha, max_eq_right hb, zero_add, sub_zero] using h1
    · simpa only [max_eq_right ha, max_eq_left hb, zero_add] using h3
    · simpa only [max_eq_left ha, max_eq_right hb, add_zero] using h2
    · rw [max_eq_left ha, max_eq_left hb]
      linarith
  refine Summable.of_norm_bounded (LSeriesSummable_zeta_pow 4 hr).norm ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, le_refl]
  simp only [LSeries.norm_term_eq, hn, ↓reduceIte, ArithmeticFunction.natCoe_apply, Complex.norm_natCast,
    Complex.sub_re, Complex.ofReal_re]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Real.rpow_sub hnpos]
  calc
    ‖sigmaR α n * sigmaR β n‖ / (n : ℝ) ^ s.re ≤
        (((ζ ^ 4 : ArithmeticFunction ℕ) n : ℝ) * (n : ℝ) ^ ρ) / (n : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right (ramanujan_norm_sigma_product_le α β hn) (Real.rpow_nonneg hnpos.le _)
    _ = _ := by rw [div_div_eq_mul_div]

private lemma ramanujan_geom_weighted_relation {a x : ℂ}
    (h : Summable (fun k : ℕ ↦ (∑ i ∈ range (k + 1), a ^ i) * x ^ k)) (hx : ‖x‖ < 1) :
    (1 - a*x) * (∑' k : ℕ, (∑ i ∈ range (k + 1), a ^ i) * x ^ k) = (1-x)⁻¹ := by
  have H := sub_eq_of_eq_add' <| h.hasSum.eq_smul_add_of_linearRec₁ (D := a*x)
    (hasSum_geometric_of_norm_lt_one hx) (by simp) (fun r ↦ ?_)
  · simpa only [smul_eq_mul, sub_mul, one_mul] using H
  · change (∑ i ∈ range (r+1+1), a^i) * x^(r+1) =
      (a*x)*((∑ i ∈ range (r+1), a^i)*x^r)+x^(r+1)
    rw [show (∑ i ∈ range (r+1+1), a^i) = a*(∑ i ∈ range (r+1), a^i)+1
      from geom_sum_succ, pow_succ]
    ring

private lemma ramanujan_geom_product_relation (a b : ℂ) (k : ℕ) :
    (∑ i ∈ range (k+2), a^i) * (∑ i ∈ range (k+2), b^i) =
      a*b*((∑ i ∈ range (k+1), a^i) * (∑ i ∈ range (k+1), b^i)) +
      (∑ i ∈ range (k+2), a^i) + (∑ i ∈ range (k+2), b^i) - 1 := by
  have ha : (∑ i ∈ range (k+2), a^i) = a*(∑ i ∈ range (k+1), a^i)+1 := geom_sum_succ
  have hb : (∑ i ∈ range (k+2), b^i) = b*(∑ i ∈ range (k+1), b^i)+1 := geom_sum_succ
  rw [ha,hb]
  ring

/-- A native first-order recurrence computes the local factor without dividing by 1-a or 1-b. -/
private lemma ramanujan_geom_product_sum {a b x : ℂ}
    (ha : Summable (fun k : ℕ ↦ (∑ i ∈ range (k+1), a^i)*x^k))
    (hb : Summable (fun k : ℕ ↦ (∑ i ∈ range (k+1), b^i)*x^k))
    (h : Summable (fun k : ℕ ↦ (∑ i ∈ range (k+1), a^i)*(∑ i ∈ range (k+1), b^i)*x^k))
    (hx : ‖x‖ < 1) (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0) (habx : 1-a*b*x ≠ 0) :
    (∑' k : ℕ, (∑ i ∈ range (k+1), a^i)*(∑ i ∈ range (k+1), b^i)*x^k) =
      (1-a*b*x^2) / ((1-x)*(1-a*x)*(1-b*x)*(1-a*b*x)) := by
  have hx0 : 1-x ≠ 0 := by
    intro hc
    have he : x = 1 := (sub_eq_zero.mp hc).symm
    simp only [he, norm_one, lt_self_iff_false] at hx
  have HA := ramanujan_geom_weighted_relation ha hx
  have HB := ramanujan_geom_weighted_relation hb hx
  have HG : (1-x) * (1-x)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have H := sub_eq_of_eq_add' <| h.hasSum.eq_smul_add_of_linearRec₁ (D := a*b*x)
    ((ha.hasSum.add hb.hasSum).sub (hasSum_geometric_of_norm_lt_one hx))
    (by simp) (fun r ↦ ?_)
  · apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hx0 hax) hbx) habx)).2
    simp only [smul_eq_mul] at H
    linear_combination
      ((1-x)*(1-a*x)*(1-b*x))*H + ((1-x)*(1-b*x))*HA +
      ((1-x)*(1-a*x))*HB + (1-a*b*x^2)*HG
  · change (∑ i ∈ range (r+1+1), a^i)*(∑ i ∈ range (r+1+1), b^i)*x^(r+1) =
      (a*b*x)*((∑ i ∈ range (r+1), a^i)*(∑ i ∈ range (r+1), b^i)*x^r) +
      ((∑ i ∈ range (r+1+1), a^i)*x^(r+1)+(∑ i ∈ range (r+1+1), b^i)*x^(r+1)-x^(r+1))
    rw [show r+1+1 = r+2 by omega, ramanujan_geom_product_relation, pow_succ]
    ring

private lemma ramanujan_sigma_summable {α s : ℂ} (h1 : 1 < s.re) (h2 : 1 < (s - α).re) :
    LSeriesSummable (sigmaR α) s := by
  rw [sigmaR_eq_zeta_mul_powR, ← TauCeti.ArithmeticFunction.sigmaC_eq_zeta_mul_cpow]
  exact TauCeti.LSeries.LSeriesSummable_sigmaC_iff.mpr
    (max_lt h1 (by rw [Complex.sub_re] at h2; linarith))

private lemma ramanujan_sigma_term_prime_power (p : ℕ) (hp : p.Prime) (α s : ℂ) (k : ℕ) :
    LSeries.term (sigmaR α) s (p^k) =
      (∑ i ∈ range (k+1), ((p : ℂ)^α)^i) * ((p : ℂ)^(-s))^k := by
  rw [TauCeti.LSeries.term_pow p hp.ne_zero k, sigmaR_apply_prime_pow hp]
  simp only [Complex.cpow_nat_mul]

private lemma ramanujan_local (α β s : ℂ) (p : Nat.Primes)
    (h1 : 1 < s.re) (h2 : 1 < (s - α).re) (h3 : 1 < (s - β).re)
    (h4 : 1 < (s - α - β).re) :
    ∑' k : ℕ, LSeries.term (fun n ↦ sigmaR α n * sigmaR β n) s (p.val^k) =
      (1 - (p : ℂ)^(-(2*s-α-β))) /
        ((1-(p : ℂ)^(-s))*(1-(p : ℂ)^(-(s - α)))*
          (1-(p : ℂ)^(-(s - β)))*(1-(p : ℂ)^(-(s - α - β)))) := by
  let a : ℂ := (p : ℂ)^α
  let b : ℂ := (p : ℂ)^β
  let x : ℂ := (p : ℂ)^(-s)
  have ha : Summable (fun k : ℕ ↦ (∑ i ∈ range (k+1), a^i)*x^k) := by
    convert (ramanujan_sigma_summable h1 h2).comp_injective (Nat.pow_right_injective p.prop.two_le) using 1
    ext k
    exact (ramanujan_sigma_term_prime_power p p.prop α s k).symm
  have hb : Summable (fun k : ℕ ↦ (∑ i ∈ range (k+1), b^i)*x^k) := by
    convert (ramanujan_sigma_summable h1 h3).comp_injective (Nat.pow_right_injective p.prop.two_le) using 1
    ext k
    exact (ramanujan_sigma_term_prime_power p p.prop β s k).symm
  have hterm (k : ℕ) : LSeries.term (fun n ↦ sigmaR α n * sigmaR β n) s (p.val^k) =
      (∑ i ∈ range (k+1), a^i)*(∑ i ∈ range (k+1), b^i)*x^k := by
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero k,
      sigmaR_apply_prime_pow p.prop, sigmaR_apply_prime_pow p.prop]
    simp only [Complex.cpow_nat_mul]
    rfl
  have h : Summable (fun k : ℕ ↦
      (∑ i ∈ range (k+1), a^i)*(∑ i ∈ range (k+1), b^i)*x^k) := by
    convert! (ramanujan_product_sigma_summable α β s h1 h2 h3 h4).comp_injective
      (Nat.pow_right_injective p.prop.two_le) using 1
    ext k
    exact (hterm k).symm
  have hx : ‖x‖ < 1 := by
    dsimp only [x]
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    have hp1 : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.prop.one_lt
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hp1
      (show -s.re < 0 by linarith)
  have hax : a*x = (p : ℂ)^(-(s - α)) := by
    dsimp only [a,x]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]
    congr 1
    ring
  have hbx : b*x = (p : ℂ)^(-(s - β)) := by
    dsimp only [b,x]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]
    congr 1
    ring
  have habx : a*b*x = (p : ℂ)^(-(s - α - β)) := by
    dsimp only [a,b,x]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero),
      ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]
    congr 1
    ring
  have habxx : a*b*x^2 = (p : ℂ)^(-(2*s-α-β)) := by
    rw [pow_two, ← mul_assoc, habx]
    dsimp only [x]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]
    congr 1
    ring
  have H := ramanujan_geom_product_sum ha hb h hx
    (by rw [hax]; exact Complex.one_sub_prime_cpow_ne_zero p.prop h2)
    (by rw [hbx]; exact Complex.one_sub_prime_cpow_ne_zero p.prop h3)
    (by rw [habx]; exact Complex.one_sub_prime_cpow_ne_zero p.prop h4)
  simpa only [hterm, habxx,habx,hax,hbx] using H


/--
Ramanujan formula:
`ζ(s)ζ(s - α)ζ(s - β)ζ(s - α - β)=ζ(2s-α-β) ∑ σ_α(n)σ_β(n)n^(-s)`. -/
@[blueprint
  "zeta_mul_zeta_mul_zeta_mul_zeta_eq"
  (title := "zeta mul zeta mul zeta mul zeta eq")
  (statement := /-- Ramanujan formula: $\zeta(s)\zeta(s-\alpha)\zeta(s-\beta)\zeta(s-\alpha-\beta)=\zeta(2s-\alpha-\beta) \sum_{n=1}^{\infty} \sigma_\alpha(n)\sigma_\beta(n)n^{-s}$ for $\Re(s) > 1$, $\Re(s-\alpha) > 1$, $\Re(s-\beta) > 1$, and $\Re(s-\alpha-\beta) > 1$.
  \begin{verbatim}
  This is IK (1.28).
  \end{verbatim}
   -/)
  (proof := /--
  Write $\rho=\max(\Re\alpha,0)+\max(\Re\beta,0)$. The four hypotheses give
  $\Re s>1+\rho$, and the coefficient is bounded in norm by $d_4(n)n^\rho$, so its
  $L$-series converges absolutely. At a prime $p$, put $a=p^\alpha$, $b=p^\beta$,
  and $x=p^{-s}$. The finite geometric sums $S_a(k)=\sum_{i=0}^k a^i$ satisfy
  $S_a(k+1)=aS_a(k)+1$ and
  $S_a(k+1)S_b(k+1)=abS_a(k)S_b(k)+S_a(k+1)+S_b(k+1)-1$.
  The native first-order recurrence identity therefore evaluates the local factor as
  $(1-abx^2)/((1-x)(1-ax)(1-bx)(1-abx))$, without requiring $a\ne1$ or $b\ne1$.
  Multiplying by the Euler factor of $\zeta(2s-\alpha-\beta)$ cancels its numerator;
  uniqueness of the native Euler products proves the identity.
  -/)]
theorem zeta_mul_zeta_mul_zeta_mul_zeta_eq (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    riemannZeta s * riemannZeta (s - α) * riemannZeta (s - β) * riemannZeta (s - α - β) =
      riemannZeta (2 * s - α - β) *
      LSeries (fun n ↦ σᴿ α n * σᴿ β n) s := by
  have h5 : 1 < (2*s-α-β).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero] at *
    linarith
  let a : ℕ → ℂ := fun n ↦ sigmaR α n * sigmaR β n
  have hsum : LSeriesSummable a s := ramanujan_product_sigma_summable α β s h1 h2 h3 h4
  have hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      a (m*n) = a m * a n := by
    intro m n _ _ hmn
    dsimp only [a]
    rw [(isMultiplicative_sigmaR (s := α)).map_mul_of_coprime hmn,
      (isMultiplicative_sigmaR (s := β)).map_mul_of_coprime hmn]
    ring
  have Hprod : HasProd (fun p : Nat.Primes ↦ ∑' k : ℕ, LSeries.term a s (p.val^k))
      (LSeries a s) :=
    EulerProduct.eulerProduct_hasProd (by simp [a,sigmaR_one])
      (TauCeti.LSeries.term_mul_of_coprime hmul) hsum.norm (LSeries.term_zero a s)
  have Hfour := (((riemannZeta_eulerProduct_hasProd h1).mul
    (riemannZeta_eulerProduct_hasProd h2)).mul
    (riemannZeta_eulerProduct_hasProd h3)).mul (riemannZeta_eulerProduct_hasProd h4)
  have hfactor (p : Nat.Primes) :
      (1-(p : ℂ)^(-(2*s-α-β)))⁻¹ * (∑' k : ℕ, LSeries.term a s (p.val^k)) =
        (1-(p : ℂ)^(-s))⁻¹*(1-(p : ℂ)^(-(s - α)))⁻¹*
          (1-(p : ℂ)^(-(s - β)))⁻¹*(1-(p : ℂ)^(-(s - α - β)))⁻¹ := by
    rw [ramanujan_local α β s p h1 h2 h3 h4]
    rw [← mul_div_assoc, inv_mul_cancel₀ (Complex.one_sub_prime_cpow_ne_zero p.prop h5),
      one_div]
    simp only [mul_inv]
  have Hfinal : HasProd (fun p : Nat.Primes ↦
      (1-(p : ℂ)^(-s))⁻¹*(1-(p : ℂ)^(-(s - α)))⁻¹*
        (1-(p : ℂ)^(-(s - β)))⁻¹*(1-(p : ℂ)^(-(s - α - β)))⁻¹)
      (riemannZeta (2*s-α-β)*LSeries a s) := by
    simpa only [hfactor] using (riemannZeta_eulerProduct_hasProd h5).mul Hprod
  exact Hfour.unique Hfinal

blueprint_comment /--
\label{zeta_pow_four_eq}
\textbf{zeta pow four eq}
Corollary: $\zeta(s)^4 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$ for $\Re(s) > 1$.
  \begin{verbatim}
  This is IK (1.29).
  \end{verbatim}

Proof.
This is a special case of the previous theorem where we set $\alpha = \beta = 0$.

Formal theorem: `TauCeti.riemannZeta_pow_four_eq_mul_LSeries_divisor_sq`,
in `TauCeti.NumberTheory.LSeries.Divisor`.
-/

/--
Baby Rankin-Selberg:
`ζ(s)∑τ(n^2)n^-s = ∑τ(n)^2 n^-s`. -/
@[blueprint
  "zeta_mul_tau_square_eq"
  (title := "zeta mul tau square eq")
  (statement := /-- Baby Rankin-Selberg: $\zeta(s)\sum_{n=1}^{\infty}\tau(n^2)n^{-s} = \sum_{n=1}^{\infty}\tau(n)^2 n^{-s}$ for $\Re(s) > 1$.
  \begin{verbatim}
  Precursor to IK (1.30).
  \end{verbatim}
  -/)
  (proof := /--
  This follows from the multiplicative properties of the divisor function $\tau$ and the definition of the L-series. The left-hand side can be expressed as a product of L-series corresponding to $\zeta$ and the function $n \mapsto \tau(n^2)$. The right-hand side is the L-series of the function $n \mapsto \tau(n)^2$. By analyzing the Euler products and using the fact that $\tau(n)$ counts divisors, we can derive the stated equality.
  -/)]
lemma zeta_mul_tau_square_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s * LSeries (fun n ↦ τ (n ^ 2)) s
      = LSeries (fun n ↦ (τ n) ^ 2) s := by
  simp only [tau, sigma_zero_apply]
  rw [(TauCeti.LSeriesHasSum_card_divisors_comp_sq hs).LSeries_eq,
    (TauCeti.LSeriesHasSum_card_divisors_sq hs).LSeries_eq]
  ring
  
blueprint_comment /--
The zeta-cubed identity can also be deduced by cancelling a zeta factor from the Ramanujan formula
and the baby Rankin–Selberg identity. The canonical theorem below uses the direct Euler-product
proof, which is independent of the general Ramanujan formula.
-/

-- `zeta_pow_three_eq` (IK 1.30) is proved below via Euler products, after the
-- `two_pow_omega` / `sumOnPrimePows` infrastructure (independent of Ramanujan).

@[blueprint
  "two_pow_omega_le_sigma_zero"
  (title := "two-pow-omega-le-sigma-zero")
  (statement := /--
    We have the inequality $2^{\omega(n)}\leq\sigma_0(n)$ when $n\neq 0$.
  -/)
  (proof := /--
    Recall that $\omega(n)$ is the number of distinct prime factors of $n$. Thus,
    $$2^{\omega(n)}=\prod_{p|n}2.$$
    Likewise, $\sigma_0(n)$ is the number of divisors of $n$. We can write this as
    $$\prod_{p|n}(1+v_p(n))=\sigma_0(n)$$
    where $v_p(n)$ denotes the $p$-adic valuation of $n$. For $p|n$ we have that $2\leq 1+v_p(n)$.
    Thus the result immediately follows.
  -/)]
lemma two_pow_omega_le_sigma_zero {n : ℕ} (hn : n ≠ 0) :
    2 ^ (ω n) ≤ σ 0 n := by
  rw [show ω n = (Nat.primeFactors n).card from rfl, ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod
  intro p hp
  simpa [two_mul] using
  (Nat.Prime.dvd_iff_one_le_factorization (prime_of_mem_primeFactors hp) hn).mp
    (dvd_of_mem_primeFactors hp)

blueprint_comment /--
Termwise norm domination gives absolute convergence by Mathlib's `Summable.of_norm_bounded`.
-/

@[blueprint
  "LSeriesSummable_two_pow_omega"
  (title := "LSeriesSummable-two-pow-omega")
  (statement := /--
    The $L$-series with coefficients given by $2^{\omega(n)}$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the $L$-series with coefficients given by $\sigma_0(n)$.
  -/)]
lemma LSeriesSummable_two_pow_omega {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ 2 ^ (ω n)) s :=
  TauCeti.LSeriesSummable_two_pow_cardDistinctFactors_iff.mpr hs

blueprint_comment /--
Dirichlet-series terms preserve multiplicativity on coprime inputs, using
`TauCeti.LSeries.term_mul_of_coprime`.
-/

@[blueprint
  "powOfAdditive_isMultiplicative"
  (title := "powOfAdditive-isMultiplicative")
  (statement := /--
    If $f$ is an additive function, then so to is $n\mapsto k^{f(n)}$ for any fixed $k$.
  -/)
  (proof := /--
    Note that $k^{f(mn)}=k^{f(m)+f(n)}=k^{f(m)}k^{f(n)}$.
  -/)]
lemma powOfAdditive_isMultiplicative
    {R : Type u_1} [CommMonoidWithZero R] (k : R)
    {f : ArithmeticFunction ℕ} (hf : f.IsAdditiveOnCoprime) :
    (toArithmeticFunction (fun n ↦ k ^ (f n))).IsMultiplicative :=
  hf.isAdditive.isMultiplicative_of_eq_monoidHom (powersHom R k) fun n hn ↦ by
    simp [toArithmeticFunction, hn]

@[blueprint
  "two_pow_omega_isMultiplicative"
  (title := "two-pow-omega-isMultiplicative")
  (statement := /--
    The function $n\mapsto 2^{\omega(n)}$ is multiplicative.
  -/)
  (proof := /--
    This follows directly from Lemma \ref{powOfAdditive-isMultiplicative} and the fact that $\omega(mn)=\omega(m)+\omega(n)$.
  -/)]
lemma two_pow_omega_isMultiplicative :
    (toArithmeticFunction (fun n ↦ (2 : ℂ) ^ ω n)).IsMultiplicative := by
  exact powOfAdditive_isMultiplicative 2 ⟨fun _ _ h ↦ cardDistinctFactors_mul h⟩

@[blueprint
  "sumOnPrimePows"
  (title := "sumOnPrimePows")
  (statement := /--
    Shorthand for the sum of a function $f:\mathbb{N}\to\mathbb{C}$ at prime powers for a prime $p$.
  -/)]
noncomputable def sumOnPrimePows (f : ℕ → ℂ) (p : Primes) : ℂ := ∑' e, f (p ^ e)

@[blueprint
  "sumOnPrimePows_apply"
  (title := "sumOnPrimePows-apply")
  (statement := /--
    Helper lemma for sumOnPrimePows that rewrites the shorthand as its sum.
  -/)]
lemma sumOnPrimePows_apply (f : ℕ → ℂ) (p : Primes) :
  sumOnPrimePows f p = ∑' e, f (p ^ e) := by rfl

@[blueprint
  "two_pow_omega_tsum_prime_pow"
  (title := "two-pow-omega-tsum-prime-pow")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=\frac{1+p^{-s}}{1-p^{-s}}.$$
  -/)
  (proof := /--
    Note that $\omega(p^0)=0$ and $\omega(p^k)=1$ whenever $0<k$. Thus,
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=1+2p^{-s}+2p^{-2s}+\ldots.$$
    Now apply a geometric sum to the non-constant terms and simplify. We have the necessary
    convergence as $1<\Re(s)$.
  -/)]
lemma two_pow_omega_tsum_prime_pow {s : ℂ} (hs : 1 < s.re)
    (p : Primes) : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) :=
  TauCeti.tsum_term_prime_pow_two_pow_cardDistinctFactors (zero_lt_one.trans hs)

@[blueprint
  "Complex.one_add_prime_cpow_ne_zero"
  (title := "Complex.one-add-prime-cpow-ne-zero")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that $1+p^{-s}\neq 0$. The naming convention is to mimic
    \begin{verbatim}
      Complex.one_sub_prime_cpow_ne_zero
    \end{verbatim}
  -/)
  (proof := /--
    Suppose for contradiction $1+p^{-s}=0$, then $|p^{-s}|=1$. However, this can not happen per
    \begin{verbatim}
      Complex.norm_prime_cpow_le_one_half
    \end{verbatim}
  -/)]
lemma Complex.one_add_prime_cpow_ne_zero {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    1 + (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have one_add_prime_cpow_h : ‖(p : ℂ) ^ (-s)‖ = 1 := by
    have := congr_arg norm (neg_eq_of_add_eq_zero_left h)
    simp only [norm_neg, one_mem, CStarRing.norm_of_mem_unitary] at this
    exact this
  linarith [Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs]

attribute [blueprint
  "two_pow_omega_LSeries_eulerProduct_hasProd"
  (title := "two-pow-omega-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
  TauCeti.LSeries_two_pow_cardDistinctFactors_eulerProduct_hasProd

@[blueprint
  "two_pow_omega_LSeries_eulerProduct_tprod"
  (title := "two-pow-omega-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
lemma two_pow_omega_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ 2 ^ (ω n)) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  exact (TauCeti.LSeries_two_pow_cardDistinctFactors_eulerProduct_hasProd hs).tprod_eq.symm

attribute [blueprint
  "zeta_pow_two"
  (title := "zeta pow two")
  (statement := /--
  $$\zeta(s)^2 =\zeta(2s) \sum_{n=1}^{\infty} 2^{\omega(n)} n^{-s}$$ for $\Re(s) > 1$.
  \begin{verbatim}
    An expression for `ζ^2`, in IK (1.31).
  \end{verbatim}
  -/)
  (proof := /--
    Note that
    $$\zeta(s)^2=\prod_p\frac{1}{(1-p^{-s})^2}.$$
    Similarly
    $$\zeta(2s)=\prod_p\frac{1}{(1-p^{-2s})}.$$
    Applying Theorems \ref{two-pow-omega-LSeries-eulerProduct-tprod} and \ref{two-pow-omega-LSeries-eulerProduct-hasProd} we have
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    Thus
    $$\zeta(2s)\left(\sum_{1\leq n}2^{\omega(n)}n^{-s}\right)=\prod_p\frac{1+p^{-s}}{(1-p^{-s})(1-p^{-2s})}=\prod_p\frac{1}{(1-p^{-s})^2}$$
    by the difference of squares. This is exactly the Euler product for $\zeta(s)^2$ mentioned earlier.
  -/)]
  TauCeti.riemannZeta_sq_eq_mul_LSeries_two_pow_cardDistinctFactors

private lemma LSeriesSummable_tau_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (τ (n ^ 2) : ℂ)) s := by
  simpa only [tau, sigma_zero_apply] using
    (TauCeti.LSeriesHasSum_card_divisors_comp_sq hs).LSeriesSummable

/--
Zeta cubed:
`ζ(s)^3 = ζ(2s) ∑ τ(n^2) n^(-s)`. -/
@[blueprint
  "zeta_pow_three_eq"
  (title := "zeta pow three eq")
  (statement := /-- Zeta cubed: $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty}\tau(n^2) n^{-s}$ for $\Re(s) > 1$.
  \begin{verbatim}
  This is IK (1.30).
  \end{verbatim}
  -/)
  (proof := /--
  Direct Euler-product proof (independent of Ramanujan / Baby Rankin--Selberg).
  Locally $\tau((p^k)^2)=\tau(p^{2k})=2k+1$, and $\sum_k(2k+1)x^k=(1+x)/(1-x)^2$ for $|x|<1$.
  Multiplying by the local factor $1/(1-x^2)$ of $\zeta(2s)$ recovers $1/(1-x)^3$, the local
  factor of $\zeta(s)^3$. Absolute convergence follows by comparing $\tau(n^2)\le d_3(n)$.
  -/)]
lemma zeta_pow_three_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 = riemannZeta (2 * s) * LSeries (fun n ↦ τ (n ^ 2)) s := by
  simpa only [tau, sigma_zero_apply] using
    TauCeti.riemannZeta_pow_three_eq_mul_LSeries_card_divisors_comp_sq hs

/-- The coefficient at n is the native product-series sum over the fiber d²m=n.
The zero fiber is infinite, but every Dirichlet term in it is zero. -/
private lemma zeta_cube_divisor_pair_term (s : ℂ) (n : ℕ) :
    LSeries.term (fun n ↦ ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n,
      (tau (dm.2 ^ 2) : ℂ)) s n =
    ∑' (dm : (fun p : ℕ × ℕ ↦ p.1 ^ 2 * p.2) ⁻¹' {n}),
      LSeries.term 1 (2 * s) dm.val.1 *
        LSeries.term (fun m ↦ (tau (m ^ 2) : ℂ)) s dm.val.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    have hz : ∀ dm : (fun p : ℕ × ℕ ↦ p.1 ^ 2 * p.2) ⁻¹' {(0 : ℕ)},
        LSeries.term 1 (2 * s) dm.val.1 *
          LSeries.term (fun m ↦ (tau (m ^ 2) : ℂ)) s dm.val.2 = 0 := by
      rintro ⟨⟨d,m⟩, hdm⟩
      have H : d ^ 2 * m = 0 := hdm
      rcases Nat.mul_eq_zero.mp H with hd | hm
      · have hd0 : d = 0 := eq_zero_of_pow_eq_zero hd
        simp only [hd0, LSeries.term_zero, zero_mul]
      · simp only [hm, LSeries.term_zero, mul_zero]
    simp only [hz, tsum_zero]
  have hset : (fun p : ℕ × ℕ ↦ p.1 ^ 2 * p.2) ⁻¹' {n} =
      (↑((n.divisors ×ˢ n.divisors).filter (fun dm ↦ dm.1 ^ 2 * dm.2 = n)) : Set (ℕ × ℕ)) := by
    ext ⟨d,m⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨⟨⟨⟨d*m, by rw [←h]; ring_nf⟩,hn⟩,⟨⟨d^2, by rw [←h]; ring_nf⟩,hn⟩⟩,h⟩
    · exact And.right
  rw [hset, Finset.tsum_subtype' _ (fun dm : ℕ × ℕ ↦
    LSeries.term 1 (2 * s) dm.1 * LSeries.term (fun m ↦ (tau (m ^ 2) : ℂ)) s dm.2),
    LSeries.term_of_ne_zero hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  rintro ⟨d,m⟩ hdm
  have H : d ^ 2 * m = n := (Finset.mem_filter.mp hdm).2
  have hd : d ≠ 0 := by rintro rfl; simp at H; exact hn H.symm
  have hm : m ≠ 0 := by rintro rfl; simp at H; exact hn H.symm
  rw [LSeries.term_of_ne_zero hd, LSeries.term_of_ne_zero hm]
  simp only [Pi.one_apply, one_div]
  rw [← H, Nat.cast_mul, Complex.natCast_mul_cpow, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul d 2 s]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/--
Zeta cubed alt:
`ζ(s)^3 =  ∑_n (∑ d^2 m = n, τ (m^2)) n^(-s)`. -/
@[blueprint
  "zeta_pow_three_eq_alt"
  (title := "zeta pow three eq alt")
  (statement := /-- symmetric square $L$-function for $\zeta^2$:
  $$\zeta(s)^3 = \sum_{n=1}^{\infty} \left( \sum_{d^2 m = n} \tau(m^2) \right) n^{-s}$$ for $\Re(s) > 1$.
  \begin{verbatim}
  Alternative expression for `ζ^3`, in IK between (1.30) and (1.31).
  \end{verbatim}
  -/)
  (proof := /--
  This is an alternative expression for $\zeta(s)^3$ that can be derived from the previous results. By expressing $\zeta(s)^3$ in terms of the L-series of $\tau(n^2)$ and using the properties of Dirichlet convolutions, we can rewrite the sum in a way that involves summing over divisors $d$ and corresponding $m$ such that $d^2 m = n$. This rearrangement of the series allows us to express $\zeta(s)^3$ in the desired form.
  -/)]
lemma zeta_pow_three_eq_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 =
    LSeries (fun n ↦
      ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n, τ (dm.2 ^ 2)) s := by
  have h2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hf := LSeriesHasSum_one h2
  have hg := (LSeriesSummable_tau_sq hs).LSeriesHasSum
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  have H := (hf.mul hg hsum).tsum_fiberwise (fun p : ℕ × ℕ ↦ p.1 ^ 2 * p.2)
  have H' : LSeriesHasSum (fun n ↦
      ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n,
        (tau (dm.2 ^ 2) : ℂ)) s
      (riemannZeta (2 * s) * LSeries (fun n ↦ (tau (n ^ 2) : ℂ)) s) := by
    simpa only [LSeriesHasSum, ← zeta_cube_divisor_pair_term] using H
  exact (zeta_pow_three_eq s hs).trans H'.LSeries_eq.symm

@[blueprint
  "LSeriesSummable_moebius_sq"
  (title := "LSeriesSummable-moebius-sq")
  (statement := /--
    The $L$-series with coefficients given by $\mu^2(n)$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the Riemann zeta function.
  -/)]
theorem LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s :=
  TauCeti.LSeriesSummable_moebius_sq_iff.mpr hs

@[blueprint
  "powOfMultiplicative_isMultiplicative"
  (title := "powOfMultiplicative-isMultiplicative")
  (statement := /--
    If $f$ is a multiplicative function, then so to is $n\mapsto f(n)^k$ for any $k\in\mathbb{N}$.
  -/)
  (proof := /--
    Note that $f(mn)^k=(f(m)f(n))^k=(f(m)^k)(f(n)^k)$.
  -/)]
lemma powOfMultiplicative_isMultiplicative {R : Type u_1} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (k : ℕ) :
    (toArithmeticFunction (fun n ↦ (f n) ^ k)).IsMultiplicative := by
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, _root_.mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, hf.1, one_pow, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf.2 mCn, mul_pow]

@[blueprint
  "moebius_sq_tsum_prime_pow"
  (title := "moebius-sq-tsum-prime-pow")
  (statement := /--
    For $p$ prime, we have that
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)
  (proof := /--
    Note that $\mu^2(p^0)=1$ and $\mu^2(p^1)=1$ but $\mu^2(p^k)=0$ whenever $1<k$. Thus,
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)]
lemma moebius_sq_tsum_prime_pow {s : ℂ} (p : Nat.Primes) :
    sumOnPrimePows (LSeries.term (fun n ↦ (μ n) ^ 2) s) p = (1 + (p : ℂ) ^ (-s)) := by
  have h_rw : 1 + ↑↑p ^ (-s) = ∑' (e : ℕ), (if e ≤ 1 then 1 else 0) / ((p : ℂ) ^ e) ^ s := by
    rw [tsum_eq_sum (s := {0, 1})]
    · simp only [mem_singleton, zero_ne_one, not_false_eq_true, sum_insert, _root_.zero_le,
        ↓reduceIte, pow_zero, Complex.one_cpow, ne_eq, one_ne_zero, div_self, sum_singleton,
        le_refl, pow_one, one_div, Complex.cpow_neg]
    · intro e he; simp at he
      simp [show ¬e ≤ 1 by omega]
  simp only [sumOnPrimePows_apply, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte, ← Int.cast_pow, moebius_sq, h_rw]
  apply tsum_congr
  intro e
  congr 1
  by_cases h : (e ≤ 1) <;> simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, h, ↓reduceIte, ite_eq_left_iff,
    zero_ne_one, imp_false, Decidable.not_not, ite_eq_right_iff, one_ne_zero, imp_false]
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    interval_cases e
    · simp only [zero_mul, zero_le, implies_true]
    · simp only [one_mul, ← Nat.squarefree_iff_factorization_le_one (Nat.Prime.ne_zero p.prop)]
      exact (Nat.squarefree_and_prime_pow_iff_prime.mpr p.prop).1
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, not_forall, not_le]
    use p
    simp only [Nat.Prime.factorization_self p.prop, mul_one]
    exact Nat.lt_of_not_le h

attribute [blueprint
  "moebius_sq_LSeries_eulerProduct_hasProd"
  (title := "moebius-sq-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
  TauCeti.LSeries_moebius_sq_eulerProduct_hasProd

@[blueprint
  "moebius_sq_LSeries_eulerProduct_tprod"
  (title := "moebius-sq-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
lemma moebius_sq_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ (μ n) ^ 2) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) := by
  exact (TauCeti.LSeries_moebius_sq_eulerProduct_hasProd hs).tprod_eq.symm

-- **Zulip question** Do we want `|μ n| = μ^2 (n)` to be a standalone function? It is the indicator
-- of `n` being squarefree.

attribute [blueprint
  "zeta_alt"
  (title := "zeta alt")
  (statement := /--
  $$\zeta(s) =\zeta(2s) \sum_{n=1}^{\infty}\mu^2(n)n^{-s}.$$
  \begin{verbatim}
    An expression for `ζ`, in IK (1.32).
  \end{verbatim}
  -/)
  (proof := /--
  The series $\sum_{n=1}^{\infty}\mu^2(n)n^{-s}$ has Euler product $\prod_{p} (1 + p^{-s})$. On the other hand, $\zeta(2s)=\prod_p (1 - p^{-2s})^{-1}$. The product of these two Euler products is $\prod_p (1 - p^{-s})^{-1} = \zeta(s)$, which gives the desired formula.
  -/)]
  TauCeti.riemannZeta_eq_mul_LSeries_moebius_sq

@[blueprint
  "pow_divisors_mul"
  (title := "pow-divisors-mul")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers and let $k$ be fixed. The divisors $x$ of $mn$ with
    $x^k \mid mn$ are exactly the products $ab$ where $a \mid m$, $a^k \mid m$, $b \mid n$, and
    $b^k \mid n$.
  -/)
  (proof := /--
    Since $m$ and $n$ are coprime, every divisor of $mn$ factors uniquely as $ab$ with $a \mid m$
    and $b \mid n$. For such a factorization, $x^k \mid mn$ is equivalent to $a^k \mid m$ and
    $b^k \mid n$, again by coprimality.
  -/)]
lemma pow_divisors_mul {m n k : ℕ} (hmn : Nat.Coprime m n) :
    (m * n).divisors.filter (fun x => x ^ k ∣ m * n) =
    (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)).image
      (fun p => p.1 * p.2) := by
  ext x
  simp only [mem_image, mem_product, mem_filter, mem_divisors, ne_eq, Prod.exists]
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = x := Nat.dvd_mul.mp hx.1.1
    simp only [mul_eq_zero, not_or, ← hab, mul_pow] at hx
    exact ⟨a, b, ⟨⟨⟨⟨ha, hx.1.2.1⟩, (hmn.coprime_dvd_left ha).pow_left k |>.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx.2)⟩,
      ⟨⟨hb, hx.1.2.2⟩, (hmn.symm.coprime_dvd_left hb).pow_left k |>.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx.2)⟩⟩, hab⟩⟩
  · intro ⟨a, b, hab⟩
    rw[← hab.2, mul_pow]
    exact ⟨⟨Nat.mul_dvd_mul hab.1.1.1.1 hab.1.2.1.1, Nat.mul_ne_zero_iff.mpr ⟨hab.1.1.1.2, hab.1.2.1.2⟩⟩, mul_dvd_mul hab.1.1.2 hab.1.2.2⟩

blueprint_comment /--
For coprime natural numbers the product map is injective on the product of their divisor sets.
This is Mathlib's `Nat.Coprime.mul_injOn_divisors`.
-/

attribute [blueprint
  "pow_divisors_mul_injective"
  (title := "pow-divisors-mul-injective")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers and let $k$ be fixed. The map $(a,b) \mapsto ab$ is
    injective on the product of $\{a \mid m : a^k \mid m\}$ and $\{b \mid n : b^k \mid n\}$.
  -/)
  (proof := /--
    This is the restriction of Lemma \ref{divisors-mul-injective} to a subset of the divisor
    product, so injectivity is preserved.
  -/)]
  Nat.Coprime.mul_injOn_divisors

@[blueprint
  "sum_moebius_sq_divisors"
  (title := "sum-moebius-sq-divisors")
  (statement := /-- The function $n \mapsto \sum_{d^2|n} \mu(d)$. -/)]
noncomputable def sum_moebius_sq_divisors : ArithmeticFunction ℤ where
  toFun := fun n ↦ ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d
  map_zero' := by simp

@[blueprint
  "sum_moebius_sq_divisors_apply"
  (title := "sum-moebius-sq-divisors-apply")
  (statement := /-- A simple helper lemma for the above definition. -/)]
lemma sum_moebius_sq_divisors_apply (n : ℕ) :
  sum_moebius_sq_divisors n = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by rfl

@[blueprint
  "sum_moebius_sq_divisors_IsMultiplicative"
  (title := "sum-moebius-sq-divisors-is-multiplicative")
  (statement := /-- The function $n \mapsto \sum_{d^2|n} \mu(d)$ is multiplicative. -/)
  (proof := /--
    We will show that for coprime $m$ and $n$, we have
    $\sum_{d^2|mn} \mu(d) = \sum_{d^2|m} \mu(d) \cdot \sum_{d^2|n} \mu(d)$. This follows from
    Lemma \ref{pow-divisors-mul}: the divisors $d$ of $mn$ with $d^2 \mid mn$ factor uniquely as
    $d=ab$ with $a^2 \mid m$ and $b^2 \mid n$. Multiplicativity of $\mu$ then factors the sum.
  -/)]
lemma sum_moebius_sq_divisors_IsMultiplicative : sum_moebius_sq_divisors.IsMultiplicative := by
  unfold sum_moebius_sq_divisors
  refine ⟨by simp only [sum_filter, coe_mk, divisors_one, dvd_one, pow_eq_one_iff,
    OfNat.ofNat_ne_zero, or_false, sum_ite_eq', mem_singleton, ↓reduceIte, isUnit_iff_eq_one,
    IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero], ?_⟩
  intro m n mCn
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2)
      (m.divisors.filter (fun x => x ^ 2 ∣ m) ×ˢ n.divisors.filter (fun x => x ^ 2 ∣ n)) := by
    apply Set.InjOn.mono _ (by simpa only [Finset.coe_product] using mCn.mul_injOn_divisors)
    intro ⟨_, _⟩ hab
    simp only [Finset.coe_filter, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_coe] at hab ⊢
    exact ⟨hab.1.1, hab.2.1⟩
  simp only [coe_mk, pow_divisors_mul mCn, Finset.sum_product,
    Finset.sum_image (fun x hx y hy => hinj
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hx)
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hy))]
  trans (∑ i ∈ m.divisors.filter (fun x => x ^ 2 ∣ m), ∑ j ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ i * μ j)
  · apply Finset.sum_congr rfl
    intro _ hi
    apply Finset.sum_congr rfl
    intro _ hj
    exact isMultiplicative_moebius.map_mul_of_coprime
      (mCn.coprime_dvd_left (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hi))
        |>.coprime_dvd_right (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hj)))
  · rw [← Finset.sum_mul_sum]

@[blueprint
  "sum_moebius_sq_divisors_apply_prime_pow"
  (title := "sum-moebius-sq-divisors-apply-prime-pow")
  (statement := /-- Applied at prime powers, sum-moebius-sq-divisors coincides with $\mu^2$. -/)
  (proof := /--
    For a prime power $p^k$, note that if $k\leq 1$ then the only square divisor is $1$, so the sum
    evaluates as $\mu(1)=1$. If $k\geq 2$, then $1$ and $p^2$ are square divisors of $p^k$. Thus,
    the sum evaluates as $\mu(1)+\mu(p)+\ldots$ where the remaining terms are moebius of higher
    powers (if necessary). Since $\mu(p)=-1$ and $\mu$ of higher powers of $p$ is zero, this is
    $0$. This agrees with $\mu(p^k)^2$, which is simply an indicator function for $k\leq 1$ (i.e.
    $p^k$ is squarefree).
  -/)]
lemma sum_moebius_sq_divisors_apply_prime_pow {p k : ℕ} (hp : Nat.Prime p) :
  sum_moebius_sq_divisors (p ^ k) = (μ (p ^ k)) ^ 2 := by
  rw [sum_moebius_sq_divisors_apply, Finset.sum_filter, Nat.sum_divisors_prime_pow hp]
  rcases k with _ | _ | k
  · simp
  · have hsq : ¬ p ^ 2 ∣ p := by
      simpa only [pow_one] using
        (not_congr (Nat.pow_dvd_pow_iff_le_right hp.one_lt (k := 2) (l := 1))).mpr (by omega)
    simp [Finset.sum_range_succ, moebius_apply_prime hp, hsq]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [moebius_apply_prime_pow, moebius_apply_prime hp, hp, ← pow_mul,
      Nat.pow_dvd_pow_iff_le_right hp.one_lt]

/-- I-K (1.33): `μ^2(n) = ∑ d^2|n μ(d)`. -/
@[blueprint
  "moebius_sq_eq"
  (title := "moebius-sq-eq")
  (statement := /-- I-K (1.33): $\mu^2(n) = \sum_{d^2|n} \mu(d)$. -/)
  (proof := /-- Apply the previous two lemmas. -/)]
lemma moebius_sq_eq (n : ℕ) : (μ n) ^ 2 = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by
  have heq := (IsMultiplicative.eq_iff_eq_on_prime_powers
    sum_moebius_sq_divisors sum_moebius_sq_divisors_IsMultiplicative
    ((μ : ArithmeticFunction ℤ).ppow 2) isMultiplicative_moebius.ppow).mpr
    (fun p k hp => by
      simpa only [ppow_apply (by decide : 0 < 2)] using
        sum_moebius_sq_divisors_apply_prime_pow (k := k) hp)
  simpa only [sum_moebius_sq_divisors_apply, ppow_apply (by decide : 0 < 2)] using
    congrArg (fun f : ArithmeticFunction ℤ => f n) heq.symm


blueprint_comment /--
The Liouville function is Mathlib's canonical `ArithmeticFunction.liouville`, equal to
`(-1)^Ω(n)` away from zero and zero at zero.
-/

/-
The Liouville function is completely multiplicative. -/
blueprint_comment /--
\label{isCompletelyMultiplicative_liouville}
\paragraph{isCompletelyMultiplicative liouville}
The Liouville function is completely multiplicative.

The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. To show that $\lambda$ is completely multiplicative, we need to verify that $\lambda(1) = 1$ and that $\lambda(ab) = \lambda(a)\lambda(b)$ for all natural numbers $a$ and $b$.
-/

attribute [blueprint
  "LSeries_liouville_eq"
  (title := "LSeries liouville eq")
  (statement := /-- The Dirichlet series of the Liouville function is $\zeta(2s)/\zeta(s)$. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is multiplicative, and its value at prime powers is given by $\lambda(p^k) = (-1)^k$. The Dirichlet series of $\lambda$ can be expressed as an Euler product over primes:
\[
L(\lambda, s) = \prod_{p} \left(1 + \lambda(p)p^{-s} + \lambda(p^2)p^{-2s} + \ldots\right) = \prod_{p} \left(1 - p^{-s}\right) \left(1 - p^{-2s}\right)^{-1} = \frac{\zeta(2s)}{\zeta(s)}.
\]
  -/)]
  TauCeti.LSeriesHasSum_liouville


attribute [blueprint
  "liouville_eq_moebius_on_squarefree"
  (title := "liouville eq moebius on squarefree")
  (statement := /-- The Liouville function agrees with the Möbius function on square-free numbers. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. The Möbius function $\mu(n)$ is defined as $0$ if $n$ has a squared prime factor, and otherwise it is $(-1)^{\omega(n)}$, where $\omega(n)$ counts the number of distinct prime factors of $n$. For square-free numbers, we have $\Omega(n) = \omega(n)$, since there are no repeated prime factors. Therefore, for square-free numbers, we have $\lambda(n) = (-1)^{\omega(n)} = \mu(n)$, which shows that the Liouville function agrees with the Möbius function on square-free numbers.
  -/)]
  ArithmeticFunction.moebius_apply_of_squarefree

attribute [blueprint
  "LSeries_totient_eq"
  (title := "LSeries totient eq")
  (statement := /-- Euler totient series: $\sum_{n=1}^{\infty} \varphi(n) n^{-s} = \zeta(s-1)/\zeta(s)$ for $\Re(s) > 2$.
  \begin{verbatim}
  This is IK (1.35). The L-series converges absolutely for Re(s) > 2
  (using φ(n) ≤ n to bound terms; the original hypothesis 1 < Re(s) is incorrect).
  \end{verbatim}
   -/)
  (proof := /--
  The Euler totient function $\varphi(n)$ counts the positive integers up to $n$ that are relatively prime to $n$. It is a multiplicative function, and its value at prime powers is given by $\varphi(p^k) = p^k - p^{k-1}$. The Dirichlet series of $\varphi$ can be expressed as an Euler product over primes:
\[
L(\varphi, s) = \prod_{p} \left(1 + \varphi(p)p^{-s} + \varphi(p^2)p^{-2s} + \ldots\right) = \prod_{p} \left(1 - p^{-s  +1}\right)^{-1} \left(1 - p^{-s}\right) = \frac{\zeta(s-1)}{\zeta(s)}.
\]
  The L-series converges absolutely for Re(s) > 2, using φ(n) ≤ n to bound the terms.
  -/)]
  TauCeti.LSeriesHasSum_totient


end ArithmeticFunction
