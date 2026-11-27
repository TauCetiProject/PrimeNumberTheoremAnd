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
public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyAdditive
public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.LSeries.Liouville
public import TauCeti.NumberTheory.LSeries.Moebius
public import TauCeti.NumberTheory.LSeries.Totient
import TauCeti.NumberTheory.ArithmeticFunction.Zeta
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Complex
public import TauCeti.NumberTheory.LSeries.TwoPowOmega
import TauCeti.NumberTheory.LSeries.Divisor.Basic
import TauCeti.NumberTheory.LSeries.Divisor.PowerSum
import TauCeti.NumberTheory.LSeries.Divisor.Ramanujan
import TauCeti.NumberTheory.LSeries.Zeta.Pow
import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.LSeries.Convergence


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

Follows as a consequence of Lemma \ref{LSeries.term_isMultiplicative_if_fun_isMultiplicative}
    and \ref{two_pow_omega_isMultiplicative}.
-/

blueprint_comment /--
\label{moebius_sq_LSeries.term_isMultiplicative}
We have that $n\mapsto \mu^2(n)/n^{s}$ is a multiplicative function.

Follows as a consequence of Lemma \ref{LSeries.term_isMultiplicative_if_fun_isMultiplicative}
    and \ref{powOfMultiplicative_isMultiplicative} (with $f=\mu$, $k=2$).
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

attribute [blueprint
  "IsAdditive"
  (title := "IsAdditive")
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
  IsAdditiveOnCoprime

attribute [blueprint
  "IsCompletelyAdditive"
  (title := "IsCompletelyAdditive")
  (statement := /-- Completely additive arithmetic function: satisfies $f(1) = 0$ and
    $f(mn) = f(m) + f(n)$ for all $m, n \ne 0$. -/)]
  IsCompletelyAdditive

attribute [blueprint
  "IsCompletelyAdditive.isAdditive"
  (title := "IsCompletelyAdditive.isAdditive")
  (statement := /-- A completely additive function is additive. -/)]
  IsCompletelyAdditive.isAdditive

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

attribute [blueprint
  "sigmaR"
  (title := "sigmaR")
  (statement := /-- Divisor power sum with complex exponent: $\sigma_\nu(n)=\sum_{d\mid n}d^\nu$,
    with $\sigma_\nu(0)=0$. -/)]
  TauCeti.ArithmeticFunction.sigmaC

open TauCeti.ArithmeticFunction (sigmaC)

attribute [blueprint
  "sigmaR_natCast"
  (title := "sigmaR-natCast")
  (statement := /-- For a natural exponent $k$, the divisor power sum is Mathlib's $\sigma_k$:
    $\sigma_k(n)=\sum_{d\mid n}d^k$. -/)
  (proof := /--
  This is the definition of $\sigma_k$ as the sum of the $k$-th powers of the divisors of $n$.
  -/)]
  ArithmeticFunction.sigma_apply

attribute [blueprint
  "sigmaR_apply"
  (title := "sigmaR-apply")
  (statement := /--
    We have that $\sigma_s(n)=\sum_{d\mid n}d^s.$
  -/)
  (proof := /--
    This follows immediately from the definition.
  -/)]
  TauCeti.ArithmeticFunction.sigmaC_apply

attribute [blueprint
  "sigmaR_natCast'"
  (title := "sigmaR-natCast'")
  (statement := /--
    A casting lemma: at a natural exponent $k$, the complex-exponent divisor power sum
    $\sigma_k$ is the cast of Mathlib's $\sigma_k$ (Lemma \ref{sigmaR_natCast}).
  -/)]
  TauCeti.ArithmeticFunction.sigmaC_natCast

attribute [blueprint
  "sigmaR_apply_prime_pow"
  (title := "sigmaR-apply-prime-pow")
  (statement := /--
    For a prime power, we have that $\sigma_s(p^i)=\sum_{j=0}^i(p^s)^j$.
  -/)
  (proof := /--
    Note that $d\mid p^i$ implies that $d=p^j$ with $0\leq j\leq i$. Thus,
    $$\sigma_s(p^i)=\sum_{d\mid p^i}d^s=\sum_{j=0}^i(p^j)^s=\sum_{j=0}^i(p^s)^j.$$
  -/)]
  TauCeti.ArithmeticFunction.sigmaC_apply_prime_pow

@[blueprint
  "sigmaR_one_apply"
  (title := "sigmaR-one-apply")
  (statement := /--
    $\sigma_1(n)=\sum_{d\mid n}d$, with the sum cast to $\mathbb{C}$.
  -/)]
lemma sigmaC_one_apply (n : ℕ) : sigmaC 1 n = ∑ d ∈ divisors n, d := by
  simp [TauCeti.ArithmeticFunction.sigmaC_apply]

@[blueprint
  "sigmaR_one_apply_prime_pow"
  (title := "sigmaR-one-apply-prime-pow")
  (statement := /--
    $\sigma_1(p^i)=\sum_{k=0}^ip^k$, with the sum cast to $\mathbb{C}$.
  -/)]
lemma sigmaC_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    sigmaC 1 (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp [TauCeti.ArithmeticFunction.sigmaC_apply_prime_pow _ hp]

@[blueprint
  "sigmaR_eq_sum_div"
  (title := "sigmaR-eq-sum-div")
  (statement := /--
    We have that $\sigma_s(n)=\sum_{d\mid n}(n/d)^s$.
  -/)
  (proof := /--
    Note that $d \mapsto n/d$ forms a one-to-one mapping between the divisors of $n$. Using this in
    combination with the definiton we have that
    $$\sigma_s(n)=\sum_{d\mid n}d^s=\sum_{d\mid n}(n/d)^s.$$
  -/)]
lemma sigmaC_eq_sum_div {n : ℕ} {s : ℂ} :
    sigmaC s n = ∑ d ∈ divisors n, ((n / d) : ℂ) ^ s := by
  rw [TauCeti.ArithmeticFunction.sigmaC_apply, ← sum_div_divisors]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Nat.cast_div (dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]

@[blueprint
  "sigmaR_zero_apply"
  (title := "sigmaR-zero-apply")
  (statement := /--
    $\sigma_0(n)$ is the number of divisors of $n$, cast to $\mathbb{C}$.
  -/)]
lemma sigmaC_zero_apply (n : ℕ) : sigmaC 0 n = #n.divisors := by
  simp [TauCeti.ArithmeticFunction.sigmaC_apply]

@[blueprint
  "sigmaR_zero_apply_prime_pow"
  (title := "sigmaR-zero-apply-prime-pow")
  (statement := /--
    $\sigma_0(p^i)=i+1$ in $\mathbb{C}$.
  -/)]
lemma sigmaC_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : sigmaC 0 (p ^ i) = i + 1 := by
  simp [TauCeti.ArithmeticFunction.sigmaC_apply_prime_pow _ hp]

attribute [blueprint
  "sigmaR_one"
  (title := "sigmaR-one")
  (statement := /--
    We have that $\sigma_s(1)=1$.
  -/)
  (proof := /--
    By definition we have that
    $$\sigma_s(1)=\sum_{d \mid 1}d^s=1^s=1.$$
  -/)]
  TauCeti.ArithmeticFunction.sigmaC_one

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

attribute [blueprint
  "sigmaR_eq_zeta_mul_powR"
  (title := "sigmaR-eq-zeta-mul-powR")
  (statement := /-- $\sigma_\nu = \zeta * \text{pow}^R(\nu)$, where $\zeta$ is the constant function $1$. -/)
  (proof := /--
  The function $\sigma_\nu$ is defined as the sum of the $\nu$-th powers of the divisors of $n$. The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The Dirichlet convolution of $\zeta$ (the constant function $1$) and $\text{pow}^R(\nu)$ is exactly $\sigma_\nu$, since for each divisor $d$ of $n$, we have $(\zeta * \text{pow}^R(\nu))(n) = \sum_{d|n} 1 \cdot d^\nu = \sigma_\nu(n)$. Thus, we have $\sigma_\nu = \zeta * \text{pow}^R(\nu)$.
  -/)]
  TauCeti.ArithmeticFunction.sigmaC_eq_zeta_mul_cpow

attribute [blueprint
  "isMultiplicative_sigmaR"
  (title := "isMultiplicative-sigmaR")
  (statement := /--
    For fixed $s$ function $n\mapsto\sigma_s(n)$ is multiplicative.
  -/)
  (proof := /--
    Recall from Lemma \ref{sigmaR_eq_zeta_mul_powR} that $\sigma_s$ is $\zeta$ convolved with
    Definition \ref{powR}. Since both of these are multiplicative functions, their convolution is
    also multiplicative.
  -/)]
  TauCeti.ArithmeticFunction.isMultiplicative_sigmaC

@[blueprint
  "sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul"
  (title := "sigmaR-eq-prod-primeFactors-sum-range-factorization-pow-mul")
  (statement := /--
    We have that
    $$\sigma_s(n)=\prod_{p\mid n}\sum_{j=0}^{v_p(n)}p^{js}.$$
  -/)
  (proof := /--
    Since $\sigma_s$ is multiplicative, it suffices to understand it at primes powers.
    $$\sigma_s(n)=\prod_{p\mid n}\sigma_s(p^{v_p(n)}).$$
    Applying Lemma \ref{sigmaR_apply_prime_pow}.
  -/)]
lemma sigmaC_eq_prod_primeFactors_sum_range_factorization_pow_mul {n : ℕ} {s : ℂ} (hn : n ≠ 0) :
    sigmaC s n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), (p : ℂ) ^ (i * s) := by
  rw [(TauCeti.ArithmeticFunction.isMultiplicative_sigmaC s).multiplicative_factorization _ hn]
  refine prod_congr n.support_factorization fun p h ↦ ?_
  dsimp only
  rw [TauCeti.ArithmeticFunction.sigmaC_apply_prime_pow _ (prime_of_mem_primeFactors h)]
  exact sum_congr rfl fun i _ ↦ by rw [← Complex.cpow_nat_mul, mul_comm]

attribute [blueprint
  "LSeries_powR_eq"
  (title := "LSeries powR eq")
  (statement := /-- $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ for $\Re(s) > 1 + \Re(\nu)$.
  \begin{verbatim}
  This is IK (1.27).
  \end{verbatim}
  -/)
  (proof := /--
  The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The L-series of $\text{pow}^R(\nu)$ at $s$ is given by the sum $\sum_{n=1}^{\infty} n^{\nu - s}$. This series converges to the Riemann zeta function $\zeta(s - \nu)$ for $\Re(s - \nu) > 1$, since the zeta function is defined as $\zeta(s) = \sum_{n=1}^{\infty} n^{-s}$ for $\Re(s) > 1$. Therefore, we have $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ under the condition that $\Re(s) > 1 + \Re(\nu)$.
  -/)]
  TauCeti.LSeries.LSeries_cpow

attribute [blueprint
  "abscissa_powR_le"
  (title := "abscissa powR le")
  (statement := /-- The abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is $1 + \Re(\nu)$. -/)
  (proof := /--
  Since $\|n^{\nu}n^{-s}\| = n^{\Re(\nu)-\Re(s)}$, the series $\sum_n n^{\nu-s}$ converges absolutely
  exactly when $\Re(s) - \Re(\nu) > 1$, by comparison with $\sum_n n^{-\sigma}$. Hence the abscissa
  of absolute convergence is $1 + \Re(\nu)$.
  -/)]
  TauCeti.LSeries.abscissaOfAbsConv_cpow

attribute [blueprint
  "LSeries_sigma_eq_riemannZeta_mul"
  (title := "LSeries sigma eq riemannZeta mul")
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > \max(1, 1 + \Re(\nu))$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
  TauCeti.LSeries.LSeries_sigmaC

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
  uniqueness of the Euler products proves the identity. This is Tau Ceti's
  \texttt{TauCeti.LSeries.LSeries\_sigmaC\_mul\_sigmaC}, stated as a quotient by
  $\zeta(2s-\alpha-\beta)\neq 0$.
  -/)]
theorem zeta_mul_zeta_mul_zeta_mul_zeta_eq (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    riemannZeta s * riemannZeta (s - α) * riemannZeta (s - β) * riemannZeta (s - α - β) =
      riemannZeta (2 * s - α - β) *
      LSeries (fun n ↦ sigmaC α n * sigmaC β n) s := by
  simp only [Complex.sub_re] at h2 h3 h4
  have h5 : 1 < (2 * s - α - β).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; linarith
  rw [(TauCeti.LSeries.LSeries_sigmaC_mul_sigmaC h1 (by linarith) (by linarith)
    (by rw [Complex.add_re]; linarith)).2, mul_div_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re h5)]

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

attribute [blueprint
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
  two_pow_cardDistinctFactors_le_sigma_zero

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

attribute [blueprint
  "powOfAdditive_isMultiplicative"
  (title := "powOfAdditive-isMultiplicative")
  (statement := /--
    If $f$ is an additive function, then $n\mapsto k^{f(n)}$ (with value $0$ at $0$) is
    multiplicative for any fixed $k$.
  -/)
  (proof := /--
    Note that $k^{f(mn)}=k^{f(m)+f(n)}=k^{f(m)}k^{f(n)}$.
  -/)]
  IsAdditive.isMultiplicative_powOfAdditive

attribute [blueprint
  "two_pow_omega_isMultiplicative"
  (title := "two-pow-omega-isMultiplicative")
  (statement := /--
    The function $n\mapsto k^{\omega(n)}$ is multiplicative; in particular so is
    $n\mapsto 2^{\omega(n)}$.
  -/)
  (proof := /--
    This follows directly from Lemma \ref{powOfAdditive_isMultiplicative} and the fact that $\omega(mn)=\omega(m)+\omega(n)$.
  -/)]
  isMultiplicative_powOfAdditive_cardDistinctFactors

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

attribute [blueprint
  "two_pow_omega_tsum_prime_pow"
  (title := "two-pow-omega-tsum-prime-pow")
  (statement := /--
    For $0<\Re(s)$ and $p$ prime, we have that
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=\frac{1+p^{-s}}{1-p^{-s}}.$$
  -/)
  (proof := /--
    Note that $\omega(p^0)=0$ and $\omega(p^k)=1$ whenever $0<k$. Thus,
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=1+2p^{-s}+2p^{-2s}+\ldots.$$
    Now apply a geometric sum to the non-constant terms and simplify. We have the necessary
    convergence as $0<\Re(s)$.
  -/)]
  TauCeti.tsum_term_prime_pow_two_pow_cardDistinctFactors

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
    Immediately follows from Lemmas \ref{two_pow_omega_LSeries.term_isMultiplicative} and \ref{two_pow_omega_tsum_prime_pow}.
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
    Immediately follows from Lemmas \ref{two_pow_omega_LSeries.term_isMultiplicative} and \ref{two_pow_omega_tsum_prime_pow}.
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
    Applying Theorems \ref{two_pow_omega_LSeries_eulerProduct_tprod} and \ref{two_pow_omega_LSeries_eulerProduct_hasProd} we have
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    Thus
    $$\zeta(2s)\left(\sum_{1\leq n}2^{\omega(n)}n^{-s}\right)=\prod_p\frac{1+p^{-s}}{(1-p^{-s})(1-p^{-2s})}=\prod_p\frac{1}{(1-p^{-s})^2}$$
    by the difference of squares. This is exactly the Euler product for $\zeta(s)^2$ mentioned earlier.
  -/)]
  TauCeti.riemannZeta_sq_eq_mul_LSeries_two_pow_cardDistinctFactors

attribute [blueprint
  "zeta_pow_three_eq"
  (title := "zeta pow three eq")
  (statement := /-- Zeta cubed: $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty}\tau(n^2) n^{-s}$ for $\Re(s) > 1$,
  where $\tau(n^2)$ is the number of divisors of $n^2$.
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
  TauCeti.riemannZeta_pow_three_eq_mul_LSeries_card_divisors_comp_sq

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
  The coefficient $\sum_{d^2 m = n} \tau(m^2)$ is the Dirichlet convolution of $m \mapsto \tau(m^2)$
  with the indicator of the squares, whose $L$-series is $\zeta(2s)$. The $L$-series of a
  convolution is the product of the $L$-series, so by Theorem \ref{zeta_pow_three_eq} the series
  equals $\zeta(2s) \cdot \zeta(s)^3 / \zeta(2s) = \zeta(s)^3$.
  -/)
  (proofUses := ["zeta_pow_three_eq"])]
lemma zeta_pow_three_eq_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 =
    LSeries (fun n ↦
      ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n, τ (dm.2 ^ 2)) s := by
  let g : ArithmeticFunction ℂ := ⟨fun n ↦ τ (n ^ 2), by simp⟩
  have h2 : 1 < (2 * s).re := TauCeti.one_lt_re_two_mul hs
  have hsq : LSeriesHasSum ↗(ζ : ArithmeticFunction ℂ).dilateSq s (riemannZeta (2 * s)) := by
    refine ((Nat.pow_left_injective two_ne_zero).hasSum_iff fun n hn ↦ ?_).mp ?_
    · rw [LSeries.term_def, dilateSq_apply_of_not_isSquare, zero_div, ite_self]
      exact fun ⟨m, hm⟩ ↦ hn ⟨m, by simp [hm, sq]⟩
    · refine (LSeriesHasSum_one h2).congr_fun fun d ↦ ?_
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      simp [hd, ← Complex.natCast_cpow_natCast_mul]
  have hg : LSeriesHasSum ↗g s (riemannZeta s ^ 3 / riemannZeta (2 * s)) := by
    simpa [g, sigma_zero_apply] using TauCeti.LSeriesHasSum_card_divisors_comp_sq hs
  rw [← div_mul_cancel₀ (riemannZeta s ^ 3) (riemannZeta_ne_zero_of_one_lt_re h2),
    ← (LSeriesHasSum_mul hg hsq).LSeries_eq]
  congr 1; ext n
  rw [mul_dilateSq_apply, sum_filter, sum_filter, sum_product]
  push_cast
  refine sum_congr rfl fun d hd ↦ ?_
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hpos : 0 < d ^ 2 := pow_pos (Nat.pos_of_mem_divisors hd) 2
    rw [sum_eq_single_of_mem m (Nat.mem_divisors.2 ⟨dvd_mul_left _ _, (Nat.mem_divisors.1 hd).2⟩)
      fun b _ hb ↦ ite_eq_right fun h ↦ hb (Nat.eq_of_mul_eq_mul_left hpos h)]
    simp [g, Nat.mul_div_cancel_left _ hpos, (Nat.pos_of_mem_divisors hd).ne']
  · exact (sum_eq_zero fun m _ ↦ ite_eq_right fun hm ↦ h ⟨m, hm.symm⟩).symm

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
lemma powOfMultiplicative_isMultiplicative {R : Type*} [CommMonoidWithZero R]
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
    Immediately follows from Lemmas \ref{moebius_sq_LSeries.term_isMultiplicative} and \ref{moebius_sq_tsum_prime_pow}.
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
    Immediately follows from Lemmas \ref{moebius_sq_LSeries.term_isMultiplicative} and \ref{moebius_sq_tsum_prime_pow}.
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

attribute [blueprint
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
  Nat.Coprime.divisors_filter_pow_dvd_mul

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
    This is the restriction of Lemma \ref{divisors_mul_injective} to a subset of the divisor
    product, so injectivity is preserved.
  -/)]
  Nat.Coprime.mul_injOn_divisors

blueprint_comment /--
The function $n \mapsto \sum_{d^2 \mid n} \mu(d)$ is the Dirichlet convolution $\zeta * \mu_\square$
of $\zeta$ with the dilation $\mu_\square$ of $\mu$ by squares ($\mu_\square(d^2) = \mu(d)$, and
$\mu_\square(m) = 0$ when $m$ is not a square). The nodes below are Tau Ceti's lemmas about it.
-/

attribute [blueprint
  "sum_moebius_sq_divisors_apply"
  (title := "sum-moebius-sq-divisors-apply")
  (statement := /--
    For arithmetic functions $f$ and $g$,
    $(f * g_\square)(n) = \sum_{d \mid n,\ d^2 \mid n} f(n/d^2)\, g(d)$. With $f = \zeta$ and
    $g = \mu$ this is $\sum_{d^2 \mid n} \mu(d)$.
  -/)]
  ArithmeticFunction.mul_dilateSq_apply

attribute [blueprint
  "sum_moebius_sq_divisors_IsMultiplicative"
  (title := "sum-moebius-sq-divisors-is-multiplicative")
  (statement := /--
    For a multiplicative function $f$ and fixed $k$, the function
    $n \mapsto \sum_{d \mid n,\ d^k \mid n} f(d)$ is multiplicative; in particular so is
    $n \mapsto \sum_{d^2|n} \mu(d)$.
  -/)
  (proof := /--
    We will show that for coprime $m$ and $n$, we have
    $\sum_{d^k|mn} f(d) = \sum_{d^k|m} f(d) \cdot \sum_{d^k|n} f(d)$. This follows from
    Lemma \ref{pow_divisors_mul}: the divisors $d$ of $mn$ with $d^k \mid mn$ factor uniquely as
    $d=ab$ with $a^k \mid m$ and $b^k \mid n$. Multiplicativity of $f$ then factors the sum.
  -/)]
  ArithmeticFunction.IsMultiplicative.sum_divisors_filter_pow_dvd_mul

attribute [blueprint
  "sum_moebius_sq_divisors_apply_prime_pow"
  (title := "sum-moebius-sq-divisors-apply-prime-pow")
  (statement := /--
    At a prime power, $\sum_{d^2 \mid p^k} \mu(d)$ is $1$ for $k \le 1$ and $0$ for $k \ge 2$;
    this is $\mu(p^k)^2$.
  -/)
  (proof := /--
    For a prime power $p^k$, note that if $k\leq 1$ then the only square divisor is $1$, so the sum
    evaluates as $\mu(1)=1$. If $k\geq 2$, then $1$ and $p^2$ are square divisors of $p^k$. Thus,
    the sum evaluates as $\mu(1)+\mu(p)+\ldots$ where the remaining terms are moebius of higher
    powers (if necessary). Since $\mu(p)=-1$ and $\mu$ of higher powers of $p$ is zero, this is
    $0$. This agrees with $\mu(p^k)^2$, which is simply an indicator function for $k\leq 1$ (i.e.
    $p^k$ is squarefree).
  -/)]
  ArithmeticFunction.sum_divisors_filter_sq_dvd_moebius_prime_pow

attribute [blueprint
  "moebius_sq_eq"
  (title := "moebius-sq-eq")
  (statement := /-- I-K (1.33): $\mu^2(n) = \sum_{d^2|n} \mu(d)$. -/)
  (proof := /-- Apply the previous two lemmas. -/)]
  ArithmeticFunction.sum_divisors_filter_sq_dvd_moebius

attribute [blueprint
  "sum_moebius_sq_divisors"
  (title := "sum-moebius-sq-divisors")
  (statement := /--
    $\mu^2 = \zeta * \mu_\square$: the function $n \mapsto \sum_{d^2|n} \mu(d)$ is $\mu^2$.
  -/)
  (proof := /--
    Lemma \ref{sum_moebius_sq_divisors_apply} with $f = \zeta$ and $g = \mu$, then
    Lemma \ref{moebius_sq_eq}.
  -/)]
  ArithmeticFunction.coe_zeta_mul_dilateSq_moebius_apply

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
  TauCeti.LSeries_totient


end ArithmeticFunction
