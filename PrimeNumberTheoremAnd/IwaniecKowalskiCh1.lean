module

public import Architect
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.Data.Finset.NatDivisors
public import TauCeti.NumberTheory.LSeries.EulerProduct


@[expose] public section

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

/--
An arithmetic function `IsAdditive` if it satisfies the property that for any two coprime natural numbers `m` and `n`, the function evaluated at their product equals the sum of the function evaluated at each number individually.
-/
@[blueprint
  "IsAdditive"
  (title := "IsAdditive")
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

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
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

@[blueprint
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
lemma unique_divisor_decomposition {a b d : ℕ} (hab : Coprime a b) (hd : d ∣ a * b) :
    ∃! p : ℕ × ℕ, p.1 ∣ a ∧ p.2 ∣ b ∧ p.1 * p.2 = d := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    refine ⟨(d,1), by simp, ?_⟩
    rintro ⟨x,y⟩ ⟨_,hy,hxy⟩
    have hy1 : y = 1 := Nat.dvd_one.mp hy
    subst y
    simpa using hxy
  by_cases hb : b = 0
  · subst b
    have ha1 : a = 1 := by simpa using hab
    subst a
    refine ⟨(1,d), by simp, ?_⟩
    rintro ⟨x,y⟩ ⟨hx,_,hxy⟩
    have hx1 : x = 1 := Nat.dvd_one.mp hx
    subst x
    simpa using hxy
  obtain ⟨x,y,hx,hy,hxy⟩ := Nat.dvd_mul.mp hd
  refine ⟨(x,y), ⟨hx,hy,hxy⟩, ?_⟩
  intro p hp
  apply hab.mul_injOn_divisors
  · exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hp.1,ha⟩, Nat.mem_divisors.mpr ⟨hp.2.1,hb⟩⟩
  · exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hx,ha⟩, Nat.mem_divisors.mpr ⟨hy,hb⟩⟩
  · exact hp.2.2.trans hxy.symm


blueprint_comment /--
For a multiplicative arithmetic function, its divisor sum is multiplicative. This is Mathlib's
multiplicativity of convolution with the constant-one arithmetic function. The Möbius-weighted
divisor sum is the product over prime factors of one minus the function value; Mathlib supplies
this as `IsMultiplicative.prodPrimeFactors_one_sub`.
-/

/-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/
@[blueprint
  "zeta_mul_zeta"
  (title := "zeta mul zeta")
  (statement := /-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/)
  (proof := /--
  By definition of $\zeta$, we have $\zeta(n) = 1$ for all $n \geq 1$. Thus, the Dirichlet convolution
  $(\zeta * \zeta)(n)$ counts the number of ways to write $n$ as a product of two positive integers,
  which is exactly the number of divisors of $n$, i.e., $\tau(n)$.
  -/)]
theorem zeta_mul_zeta : (ζ : ArithmeticFunction ℕ) * ζ = τ := by
  nth_rw 2 [← pow_zero_eq_zeta]
  exact zeta_mul_pow_eq_sigma

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
  have h1 : LSeries (↗(ζ * ζ)) s = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1; ext n; simp only [← natCoe_mul, natCoe_apply]
  have h2 : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s = LSeries (↗ζ) s * LSeries (↗ζ) s :=
    LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs) (LSeriesSummable_zeta_iff.mpr hs)
  rw [← zeta_mul_zeta, h1, h2, LSeries_zeta_eq_riemannZeta hs, pow_two]

/-- `d k` is the k-fold divisor function: the number of ways to write n as an ordered
    product of k natural numbers. Equivalently, the Dirichlet convolution of ζ with
    itself k times. We have `d 0 = 1` (identity), `d 1 = ζ`, `d 2 = σ 0`. -/
@[blueprint
  "d"
  (title := "d")
  (statement := /-- $d_k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/)]
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
@[blueprint
  "d_zero"
  (title := "d zero")
  (statement := /-- $d_0$ is the multiplicative identity (indicator at 1). -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/)]
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
@[blueprint
  "d_one"
  (title := "d one")
  (statement := /-- $d_1$ is $\zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d_1 = \zeta^1 = \zeta$.
  -/)]
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
@[blueprint
  "d_two"
  (title := "d two")
  (statement := /-- $d_2$ is the classical divisor count function $\tau$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d_2 = \zeta^2 = \tau$.
  -/)]
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: `d_(k+1) = d_k * ζ`. -/
@[blueprint
  "d_succ"
  (title := "d succ")
  (statement := /-- Recurrence: $d_{k+1} = d_k * \zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d_{k + 1}$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d_k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d_{k + 1} = d_k * \zeta$.
  -/)]
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series for `d k` is summable -/
@[blueprint
  "LSeries_d_summable"
  (title := "LSeries d summable")
  (statement := /-- The L-series for $d_k$ is summable for $\Re(s) > 1$. -/)
  (proof := /--
  Since $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$, and we know that the L-series of $\zeta$ converges for $\Re(s) > 1$, it follows that the L-series of $d_k$ also converges for $\Re(s) > 1$. This is because the convolution of functions with convergent L-series will also have a convergent L-series in the same region. Therefore, we can conclude that $L(d_k, s)$ is summable for $\Re(s) > 1$.
  -/)]
theorem LSeries_d_summable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (↗(d k : ArithmeticFunction ℂ)) s := by
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, one_eq_delta]
    exact (hasSum_single 1 fun n hn => by simp [LSeries.term_delta, hn]).summable
  | succ k ih =>
    rw [(LSeriesSummable_congr s (fun {n} _ => show (d (k + 1) : ArithmeticFunction ℂ) n =
      ((d k : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]))]
    exact LSeriesSummable_mul ih (LSeriesSummable_zeta_iff.mpr hs)

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (title := "LSeries d eq riemannZeta pow")
  (statement := /-- The $L$-series of $d_k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d_k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d_k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d_k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  change LSeries (↗(d k : ArithmeticFunction ℂ)) s = riemannZeta s ^ k
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, pow_zero, one_eq_delta]
    exact congr_fun LSeries_delta s
  | succ j ih =>
    have hζ : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    rw [pow_succ, LSeries_congr (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]) s,
        LSeries_mul' (LSeries_d_summable j hs) hζ, ih]
    congr 1
    exact LSeries_zeta_eq_riemannZeta hs


/-- `d k` is multiplicative for all `k`. -/
@[blueprint
  "d_isMultiplicative"
  (title := "d isMultiplicative")
  (statement := /-- $d_k$ is multiplicative for all $k$. -/)
  (proof := /--
  The function $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$. Since $\zeta$ is a multiplicative function, and the Dirichlet convolution of multiplicative functions is also multiplicative, it follows that $d_k$ is multiplicative for all $k$. This can be shown by induction on $k$, using the fact that the convolution of a multiplicative function with another multiplicative function remains multiplicative.
  -/)]
theorem d_isMultiplicative (k : ℕ) : (d k).IsMultiplicative := by
  induction k with
  | zero => rw [d_zero]; exact isMultiplicative_one
  | succ k ih =>
      rw [d_succ]
      exact ih.mul isMultiplicative_zeta

/- MOVE HELPER LEMMA ELSEWHERE?? Not used in this file, but seems potentially useful? -/
/-- Proof route (#1686): `sum_divisorsAntidiagonal`, then `sum_divisors_prime_pow`, then `Nat.pow_div`. -/
theorem Nat.sum_divisorsAntidiagonal_prime_pow {α : Type u_1} [AddCommMonoid α] [HMul α α α] {k p : ℕ} {f : ℕ × ℕ → α} (h : Nat.Prime p) :
∑ x ∈ (p ^ k).divisorsAntidiagonal, f x = ∑ n ∈ Finset.range (k + 1), f (p ^ n, p ^ (k - n)) := by
  calc ∑ x ∈ (p ^ k).divisorsAntidiagonal, f x
      = ∑ x ∈ (p ^ k).divisorsAntidiagonal, (fun a b => f (a, b)) x.1 x.2 := rfl
    _ = ∑ d ∈ (p ^ k).divisors, (fun a b => f (a, b)) d (p ^ k / d) :=
          sum_divisorsAntidiagonal (fun a b => f (a, b))
    _ = ∑ i ∈ Finset.range (k + 1), (fun a b => f (a, b)) (p ^ i) (p ^ k / p ^ i) := by
          rw [sum_divisors_prime_pow h]
    _ = ∑ n ∈ Finset.range (k + 1), f (p ^ n, p ^ (k - n)) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          exact Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) h.pos

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
@[blueprint
  "d_apply_prime_pow"
  (title := "d apply prime pow")
  (statement := /-- Explicit formula: $d_k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. -/)
  (proof := /--
  The function $d_k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/)]
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  obtain ⟨k', rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k' generalizing a with
  | zero => simp [d_one, hp.ne_zero]
  | succ k' ih =>
      rw [d_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
      simp_rw [fun i ↦ ih i (succ_pos _)]
      simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k'

/-- (1.25) in Iwaniec-Kowalski: a formula for `d_k` for all `n`. -/
@[blueprint
  "d_apply"
  (title := "d apply")
  (statement := /-- (1.25) in Iwaniec-Kowalski: a formula for $d_k$ for all $n$. -/)
  (proof := /--
  The function $d_k$ is multiplicative, so to compute $d_k(n)$ for a general natural number $n$, we can factor $n$ into its prime power decomposition: $n = p_1^{a_1} p_2^{a_2} ... p_m^{a_m}$. Since $d_k$ is multiplicative, we have:

  \[
  d_k(n) = d_k(p_1^{a_1}) \cdot d_k(p_2^{a_2}) \cdot ... \cdot d_k(p_m^{a_m})
  \]

  Using the explicit formula for prime powers from the previous theorem, we can substitute to get:

  \[
  d_k(n) = \prod_{i=1}^{m} (a_i + k - 1).choose (k - 1)
  \]

  This gives us a complete formula for $d_k(n)$ in terms of the prime factorization of $n$.
  -/)]
lemma d_apply {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    d k n = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
  have hmult : (d k).IsMultiplicative := d_isMultiplicative k
  rw [hmult.multiplicative_factorization (d k) hn, prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl (fun p hp => ?_)
  simpa using d_apply_prime_pow hk (prime_of_mem_primeFactors hp) _

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

@[blueprint
  "powR"
  (title := "powR")
  (statement := /-- Arithmetic function with complex parameter $\nu$. Evaluates as $n\mapsto n^{\nu}$ for $n\neq 0$ and $0$ at $n=0$. -/)]
noncomputable def powR (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by grind⟩

@[blueprint
  "isMultiplicative_powR"
  (title := "isMultiplicative-powR")
  (statement := /--
    For fixed $\nu$ the function $n\mapsto n^\nu$ is multiplicative.
  -/)
  (proof := /--
    This immediately follows from the fact that exponentiation with a fixed power is a homomorphism.
  -/)]
theorem isMultiplicative_powR {ν : ℂ} : IsMultiplicative (powR ν) := by
  refine ⟨by simp [powR], fun {m n : ℕ} mCn => ?_⟩
  simp only [powR, ArithmeticFunction.coe_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, ↓reduceIte, mul_ite, mul_zero, ite_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, ↓reduceIte]
  have hmn_pos : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  simp only [hm.ne', hn.ne', hmn_pos, ite_false]
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n ν

@[blueprint
  "sigmaR_eq_zeta_mul_powR"
  (title := "sigmaR-eq-zeta-mul-powR")
  (statement := /-- $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$, where $\zeta$ is the constant function $1$. -/)
  (proof := /--
  The function $\sigma^R(\nu)$ is defined as the sum of the $\nu$-th powers of the divisors of $n$. The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The Dirichlet convolution of $\zeta$ (the constant function $1$) and $\text{pow}^R(\nu)$ is exactly $\sigma^R(\nu)$, since for each divisor $d$ of $n$, we have $(\zeta * \text{pow}^R(\nu))(n) = \sum_{d|n} 1 \cdot d^\nu = \sigma^R(\nu)(n)$. Thus, we have $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$.
  -/)]
lemma sigmaR_eq_zeta_mul_powR (ν : ℂ) : sigmaR ν = (zeta : ArithmeticFunction ℂ) * powR ν := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [sigmaR_apply, coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun d hd => by
    simp only [powR, coe_mk, ite_eq_right (Nat.pos_of_mem_divisors hd).ne']

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
  exact isMultiplicative_zeta.natCast.mul  isMultiplicative_powR

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
    LSeries (powR ν) s = riemannZeta (s - ν) := by
  convert ( LSeries_congr _ _ ) using 1;
  · rw [ zeta_eq_tsum_one_div_nat_cpow hs ];
    · refine tsum_congr fun n => ?_;
      by_cases hn : n = 0
      · simp only [LSeries.term, hn, one_div, CharP.cast_eq_zero, ↓reduceIte, inv_eq_zero, Complex.cpow_eq_zero_iff,
          ne_eq, true_and]
        exact sub_ne_zero_of_ne (by rintro rfl; norm_num at hs)
      · simp only [one_div];
        rw [← Complex.cpow_neg, neg_sub, Complex.cpow_sub];
        · exact Eq.symm (LSeries.term_of_ne_zero hn (fun n ↦ ↑n ^ ν) s)
        · exact cast_ne_zero.mpr hn
  · unfold ArithmeticFunction.powR; aesop;

@[blueprint
  "abscissa_powR_le"
  (title := "abscissa powR le")
  (statement := /-- The abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$. -/)
  (proof := /--
  We apply \ref{LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow} which states that if there exists a constant $C$ such that $\|f(n)\| \leq C \cdot n^r$ for all $n$ sufficiently large, then the abscissa of absolute convergence of $L(f, s)$ is at most $r + 1$. In our case, we can take $f(n) = n^\nu$ and observe that $\|n^\nu\| = n^{\Re(\nu)}$. Thus, we can choose $C = 1$ and $r = \Re(\nu)$, which gives us the desired result that the abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$.
  -/)]
lemma abscissa_powR_le (ν : ℂ) : LSeries.abscissaOfAbsConv (powR ν) ≤ ν.re + 1 := by
  have h_abs_le : ∀ n : ℕ, n ≠ 0 → ‖(powR ν n : ℂ)‖ ≤ (n : ℝ) ^ ν.re := by
    intros n hn_nonzero
    simp only [ArithmeticFunction.powR, hn_nonzero, coe_mk, ↓reduceIte];
    rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn_nonzero ) ]
  apply_rules [ LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ];
  exact ⟨ 1, fun n hn => by simpa using h_abs_le n hn ⟩

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
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← LSeries_powR_eq ν hsν, sigmaR_eq_zeta_mul_powR];
  apply ArithmeticFunction.LSeries_mul
  · apply (ArithmeticFunction.abscissaOfAbsConv_zeta.trans_lt _)
    exact_mod_cast hs
  · apply lt_of_le_of_lt (abscissa_powR_le ν)
    rw[Complex.sub_re] at hsν
    exact_mod_cast (by linarith)

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

private lemma ramanujan_tau_sq_le_d_four (n : ℕ) : (tau n)^2 ≤ d 4 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have ht : (tau.pmul tau).IsMultiplicative :=
    (isMultiplicative_sigma (k := 0)).pmul (isMultiplicative_sigma (k := 0))
  rw [← show tau.pmul tau n = (tau n)^2 from (pow_two _).symm,
    ht.multiplicative_factorization _ hn,
    (d_isMultiplicative 4).multiplicative_factorization _ hn,
    prod_factorization_eq_prod_primeFactors, prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_le_prod
  intro p hp
  have hpp := prime_of_mem_primeFactors hp
  simp only [ArithmeticFunction.pmul_apply]
  rw [← pow_two]
  change (tau (p ^ (n.factorization p))) ^ 2 ≤ _
  rw [sigma_zero_apply_prime_pow hpp, d_apply_prime_pow (by norm_num) hpp]
  exact ramanujan_square_le_choose _

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
    ‖sigmaR α n * sigmaR β n‖ ≤ (d 4 n : ℝ) *
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
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast ramanujan_tau_sq_le_d_four n)
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
  refine Summable.of_norm_bounded (LSeries_d_summable 4 hr).norm ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, le_refl]
  simp only [LSeries.norm_term_eq, hn, ↓reduceIte, ArithmeticFunction.natCoe_apply, Complex.norm_natCast,
    Complex.sub_re, Complex.ofReal_re]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Real.rpow_sub hnpos]
  calc
    ‖sigmaR α n * sigmaR β n‖ / (n : ℝ) ^ s.re ≤
        ((d 4 n : ℝ) * (n : ℝ) ^ ρ) / (n : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right (ramanujan_norm_sigma_product_le α β hn) (Real.rpow_nonneg hnpos.le _)
    _ = _ := by rw [div_div_eq_mul_div]

private lemma ramanujan_geom_weighted_relation {a x : ℂ}
    (h : Summable (fun k : ℕ ↦ (∑ i ∈ range (k + 1), a ^ i) * x ^ k)) (hx : ‖x‖ < 1) :
    (1 - a*x) * (∑' k : ℕ, (∑ i ∈ range (k + 1), a ^ i) * x ^ k) = (1-x)⁻¹ := by
  have H := h.hasSum.sub_smul_eq_of_linearRec₁ (D := a*x)
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
  have H := h.hasSum.sub_smul_eq_of_linearRec₁ (D := a*b*x)
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
  have hp : LSeriesSummable (powR α) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    apply (abscissa_powR_le α).trans_lt
    exact_mod_cast (show α.re+1 < s.re from by rw [Complex.sub_re] at h2; linarith)
  have hz : LSeriesSummable (zeta : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr h1
  have H := ArithmeticFunction.LSeriesSummable_mul hz hp
  simpa only [← sigmaR_eq_zeta_mul_powR] using H

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

/-- Corollary:  `ζ(s)^4=ζ(2s) ∑ τ(n)^2 n^(-s)` -/
@[blueprint
  "zeta_pow_four_eq"
  (title := "zeta pow four eq")
  (statement := /-- Corollary: $\zeta(s)^4 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$ for $\Re(s) > 1$.
  \begin{verbatim}
  This is IK (1.29).
  \end{verbatim}
  -/)
  (proof := /--
  This is a special case of the previous theorem where we set $\alpha = \beta = 0$.
  -/)]
theorem zeta_pow_four_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) * LSeries (fun n ↦ (τ n) ^ 2) s := by
  convert (zeta_mul_zeta_mul_zeta_mul_zeta_eq 0 0 s hs (by simpa using hs) (by simpa using hs)
      (by simpa using hs)) using 1
  · ring_nf
  · congr
    · ring_nf
    · simp [tau, sigma, sigmaR, pow_two]

class IsCoprimePreserving (f : ℕ → ℕ) : Prop where
  map_coprime : ∀ {m n : ℕ}, Nat.Coprime m n → Nat.Coprime (f m) (f n)

instance instIsCoprimePreservingPow (k : ℕ) :
    IsCoprimePreserving (· ^ k : ℕ → ℕ) :=
  ⟨fun h ↦ h.pow k k⟩

/-- The monoid hom `powMonoidHom k` preserves coprimality (specialization). -/
instance instIsCoprimePreservingPowMonoidHom (k : ℕ) :
    IsCoprimePreserving ((powMonoidHom k : ℕ →* ℕ) : ℕ → ℕ) :=
  inferInstanceAs (IsCoprimePreserving (· ^ k : ℕ → ℕ))

lemma IsMultiplicative.of_map_mulHom {f h : ArithmeticFunction ℕ}
    (hf : f.IsMultiplicative) (g : ℕ →* ℕ) (hh : ∀ n, h n = g (f n)) :
    h.IsMultiplicative := by
  refine ⟨by rw [hh, hf.1, g.map_one], fun {m n} hmn => ?_⟩
  rw [hh, hh, hh, hf.2 hmn, g.map_mul]

lemma IsMultiplicative.of_comp_mulHom {f h : ArithmeticFunction ℕ}
    (hf : f.IsMultiplicative) (g : ℕ →* ℕ)
    [hg : IsCoprimePreserving (g : ℕ → ℕ)]
    (hh : ∀ n, h n = f (g n)) : h.IsMultiplicative := by
  refine ⟨by rw [hh, g.map_one, hf.1], fun {m n} hmn => ?_⟩
  rw [hh, hh, hh, g.map_mul, hf.2 (hg.map_coprime hmn)]

/-- `∑_{j=0}^{k} (2j+1) = (k+1)²`. -/
lemma sum_two_mul_add_one (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (2 * j + 1) = (k + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- The arithmetic function `n ↦ τ(n²)`. -/
abbrev tauSq : ArithmeticFunction ℕ := ⟨fun n ↦ τ (n ^ 2), by simp⟩

/-- The arithmetic function `n ↦ τ(n)²`. -/
abbrev sqTau : ArithmeticFunction ℕ := ⟨fun n ↦ (τ n) ^ 2, by simp⟩

lemma isMultiplicative_tauSq : tauSq.IsMultiplicative :=
  IsMultiplicative.of_comp_mulHom (isMultiplicative_sigma (k := 0)) (powMonoidHom 2) (fun _ ↦ rfl)

lemma isMultiplicative_sqTau : sqTau.IsMultiplicative :=
  IsMultiplicative.of_map_mulHom (isMultiplicative_sigma (k := 0)) (powMonoidHom 2) (fun _ ↦ rfl)

/-- `τ(n²) ≤ d_3(n)` pointwise.  Used for L-series summability of `n ↦ τ(n²)`. -/
lemma tau_sq_le_d_three (n : ℕ) : tauSq n ≤ d 3 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · change τ ((0 : ℕ) ^ 2) ≤ _
    simp
  rw [isMultiplicative_tauSq.multiplicative_factorization _ hn,
      prod_factorization_eq_prod_primeFactors,
      (d_isMultiplicative 3).multiplicative_factorization _ hn,
      prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  set k := n.factorization p
  change τ ((p ^ k) ^ 2) ≤ d 3 (p ^ k)
  rw [← pow_mul, mul_comm k 2, sigma_zero_apply_prime_pow hp',
      d_apply_prime_pow (by norm_num) hp']
  change 2 * k + 1 ≤ Nat.choose (k + 2) 2
  rw [Nat.choose_two_right, show k + 2 - 1 = k + 1 from rfl,
      Nat.le_div_iff_mul_le (by norm_num : (0:ℕ) < 2)]
  nlinarith [Nat.zero_le k, sq_nonneg k]

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
  have hzf_mul : ((ζ : ArithmeticFunction ℕ) * tauSq).IsMultiplicative :=
    isMultiplicative_zeta.mul isMultiplicative_tauSq
  -- (a) Convolution identity  ζ * tauSq = sqTau  in  ArithmeticFunction ℕ.
  have hconv : (ζ : ArithmeticFunction ℕ) * tauSq = sqTau := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [hzf_mul.multiplicative_factorization _ hn,
        prod_factorization_eq_prod_primeFactors,
        isMultiplicative_sqTau.multiplicative_factorization _ hn,
        prod_factorization_eq_prod_primeFactors]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    set k := n.factorization p
    rw [show (ζ : ArithmeticFunction ℕ) * tauSq = tauSq * ζ from mul_comm _ _,
        mul_zeta_apply, sum_divisors_prime_pow hp']
    have key : ∀ j ∈ Finset.range (k + 1), tauSq (p ^ j) = 2 * j + 1 := by
      intro j _
      change τ ((p ^ j) ^ 2) = 2 * j + 1
      rw [← pow_mul, mul_comm j 2, sigma_zero_apply_prime_pow hp']
    rw [Finset.sum_congr rfl key, sum_two_mul_add_one]
    change (k + 1) ^ 2 = τ (p ^ k) ^ 2
    rw [sigma_zero_apply_prime_pow hp']
  -- (b) Summability of  ↗tauSq  at  s  via domination by  ↗(d 3).
  have hsumm : LSeriesSummable (↗(tauSq : ArithmeticFunction ℂ)) s := by
    refine Summable.of_norm_bounded ((LSeries_d_summable 3 hs).norm) ?_
    intro n
    by_cases hn : n = 0
    · simp [hn, LSeries.term]
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        norm_div, norm_div]
    gcongr
    change ‖((tauSq n : ℕ) : ℂ)‖ ≤ ‖((d 3 n : ℕ) : ℂ)‖
    simp only [Complex.norm_natCast, Nat.cast_le]
    exact tau_sq_le_d_three n
  -- (c) Lift to L-series.
  have h1 : LSeries (↗((ζ : ArithmeticFunction ℂ) * (tauSq : ArithmeticFunction ℂ))) s
          = LSeries (↗(ζ : ArithmeticFunction ℂ)) s
              * LSeries (↗(tauSq : ArithmeticFunction ℂ)) s :=
    LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs) hsumm
  have h2 : LSeries (↗(((ζ : ArithmeticFunction ℕ) * tauSq : ArithmeticFunction ℕ)
                       : ArithmeticFunction ℂ)) s
          = LSeries (↗((ζ : ArithmeticFunction ℂ)
                         * (tauSq : ArithmeticFunction ℂ))) s := by
    apply LSeries_congr
    intro n _hn
    simp [natCoe_mul]
  have key : LSeries (↗(sqTau : ArithmeticFunction ℂ)) s
           = riemannZeta s * LSeries (↗(tauSq : ArithmeticFunction ℂ)) s := by
    rw [← hconv, h2, h1]
    congr 1
    exact LSeries_zeta_eq_riemannZeta hs
  -- Bridge original goal's cast forms to AF form.
  have lhs_bridge : LSeries (fun n : ℕ ↦ ((τ (n ^ 2) : ℕ) : ℂ)) s
                  = LSeries (↗(tauSq : ArithmeticFunction ℂ)) s := by
    apply LSeries_congr
    intro n _hn
    rfl
  have rhs_bridge : LSeries (fun n : ℕ ↦ ((τ n : ℕ) : ℂ) ^ 2) s
                  = LSeries (↗(sqTau : ArithmeticFunction ℂ)) s := by
    apply LSeries_congr
    intro n _hn
    change ((τ n : ℕ) : ℂ) ^ 2 = (((τ n) ^ 2 : ℕ) : ℂ)
    push_cast
    rfl
  rw [lhs_bridge, rhs_bridge, key]
  
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
    LSeriesSummable (fun n ↦ 2 ^ (ω n)) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ 2 ^ ω n) s n‖ ≤ ‖LSeries.term (fun n ↦ σ 0 n) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow, Complex.norm_ofNat,
        RCLike.norm_natCast]
      exact div_le_div_of_nonneg_right (by exact_mod_cast two_pow_omega_le_sigma_zero hn) (norm_nonneg _)
  apply Summable.of_norm_bounded ?_ hgf
  rw [summable_norm_iff, ← LSeriesSummable]
  convert LSeries_d_summable 2 hs using 1;
  exact funext fun n => by rw [d_two]; rfl

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
    {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (toArithmeticFunction (fun n ↦ k ^ (f n))).IsMultiplicative := by
  simp only [IsAdditive, ne_eq] at hf
  have := hf one_ne_zero one_ne_zero (coprime_one_right 1)
  rw [mul_one, left_eq_add] at this
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, this,
    pow_zero, mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf m_eq_zero n_eq_zero mCn, pow_add]

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
  exact powOfAdditive_isMultiplicative 2 (fun hm hn h => ArithmeticFunction.cardDistinctFactors_mul h)

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
    (p : Primes) : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  have h_rw : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = 1 + ∑' e : ℕ, LSeries.term (fun n : ℕ => 2 ^ (ω n)) s (p.val ^ (e + 1)) := by
    rw [sumOnPrimePows_apply, Summable.tsum_eq_zero_add];
    · unfold LSeries.term
      simp [Nat.Prime.ne_zero p.prop]
    · have := LSeriesSummable_two_pow_omega hs;
      convert! this.comp_injective (show Function.Injective (fun e : ℕ => p.val ^ e) from fun a b h => Nat.pow_right_injective p.prop.one_lt h) using 1
  have h_term_eval : ∀ e : ℕ, LSeries.term (fun n : ℕ => 2 ^ ω n) s (p.val ^ (e + 1)) = 2 * (p.val : ℂ) ^ (-(e + 1) * s) := by
    intro e
    simp only [neg_mul, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte]
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow p.prop, pow_one]
    · simp only [Complex.cpow_neg, div_eq_mul_inv, ← Complex.natCast_cpow_natCast_mul, cast_add, cast_one]
    · linarith
  have geo_series_rw : ∑' e : ℕ, (p.val : ℂ) ^ (-(e + 1) * s) = (p.val : ℂ) ^ (-s) / (1 - (p.val : ℂ) ^ (-s)) := by
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one]
    · rw [← tsum_mul_left]; congr; ext n; rw [← Complex.cpow_nat_mul]; ring_nf
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]; ring_nf
    · rw [Complex.norm_cpow_of_ne_zero] <;> norm_num [p.2.ne_zero]
      exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt (mod_cast p.2.one_lt) (neg_lt_zero.mpr (by linarith))) (by norm_num)
  simp only [h_rw, h_term_eval, geo_series_rw, tsum_mul_left]
  rw [eq_div_iff, add_mul, one_mul, ← mul_div_assoc, div_mul_cancel₀]
  · ring_nf
  all_goals (exact Complex.one_sub_prime_cpow_ne_zero p.2 hs)

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

@[blueprint
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
lemma two_pow_omega_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s)) / (1 - ↑↑p ^ (-s))) (L (fun n ↦ (2 ^ ω n)) s) := by
  convert! EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (2 ^ ω n)) s) using 1;
  · funext p; exact Eq.symm (two_pow_omega_tsum_prime_pow hs p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact TauCeti.LSeries.term_mul_of_coprime (fun ha hb hab => by
      simpa [toArithmeticFunction, ha, hb, mul_ne_zero ha hb] using
        two_pow_omega_isMultiplicative.map_mul_of_coprime hab) mCn
  · convert! (LSeriesSummable_two_pow_omega hs).norm using 1

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
  exact (two_pow_omega_LSeries_eulerProduct_hasProd s hs).tprod_eq.symm

/--
Zeta squared:
`ζ(s)^2 = ζ(2*s) * ∑_n (2^omega(n)) n^(-s)`,
where omega is the number of distinct prime factors. -/
@[blueprint
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
lemma zeta_pow_two (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
    riemannZeta (2 * s) * LSeries (fun n ↦ 2 ^ (ω n)) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [sq, ← riemannZeta_eulerProduct_tprod hs, ← Multipliable.tprod_mul mulable mulable,
    mul_comm, ← riemannZeta_eulerProduct_tprod hs',
    two_pow_omega_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨LSeries (fun n ↦ 2 ^ (ω n)) s, two_pow_omega_LSeries_eulerProduct_hasProd s hs⟩
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩

/-- Local evaluation: $\tau((p^e)^2)=\tau(p^{2e})=2e+1$. -/
private lemma tau_sq_apply_prime_pow {p e : ℕ} (hp : p.Prime) :
    τ ((p ^ e) ^ 2) = 2 * e + 1 := by
  rw [← pow_mul, mul_comm e, sigma_zero_apply_prime_pow hp]

private lemma LSeriesSummable_tau_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (τ (n ^ 2) : ℂ)) s := by
  have hgf : ∀ n, ‖LSeries.term (fun n ↦ (τ (n ^ 2) : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n ↦ (d 3 n : ℂ)) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, RCLike.norm_natCast]
      exact div_le_div_of_nonneg_right (by exact_mod_cast tau_sq_le_d_three n) (norm_nonneg _)
  apply Summable.of_norm_bounded ?_ hgf
  rw [summable_norm_iff, ← LSeriesSummable]
  exact LSeries_d_summable 3 hs

/-- Local Euler factor: $\sum_e \tau((p^e)^2)\,p^{-es}=(1+p^{-s})/(1-p^{-s})^2$. -/
private lemma tau_sq_tsum_prime_pow {s : ℂ} (hs : 1 < s.re) (p : Primes) :
    sumOnPrimePows (LSeries.term (fun n ↦ (τ (n ^ 2) : ℂ)) s) p =
      (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2 := by
  have hsub : 1 - (p : ℂ) ^ (-s) ≠ 0 := Complex.one_sub_prime_cpow_ne_zero p.2 hs
  set x : ℂ := (p : ℂ) ^ (-s)
  have hx : ‖x‖ < 1 := by
    dsimp only [x]
    rw [Complex.norm_cpow_of_ne_zero (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    · norm_num
      exact lt_of_lt_of_le
        (Real.rpow_lt_rpow_of_exponent_lt (mod_cast p.2.one_lt) (neg_lt_zero.mpr (by linarith)))
        (by norm_num)
  have hx0 : 1 - x ≠ 0 := by simpa [x] using hsub
  have h_term (e : ℕ) :
      LSeries.term (fun n ↦ (τ (n ^ 2) : ℂ)) s (p.val ^ e) =
        (2 * (e : ℂ) + 1) * x ^ e := by
    rw [TauCeti.LSeries.term_pow p.val p.prop.ne_zero e, tau_sq_apply_prime_pow p.prop]
    push_cast
    rfl
  have hid : 2 * (x / (1 - x) ^ 2) + (1 - x)⁻¹ = (1 + x) / (1 - x) ^ 2 := by
    field_simp [hx0]
    ring
  have hsum' :
      HasSum (fun e : ℕ ↦ 2 * ((e : ℂ) * x ^ e) + x ^ e)
        (2 * (x / (1 - x) ^ 2) + (1 - x)⁻¹) :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left (2 : ℂ)).add
      (hasSum_geometric_of_norm_lt_one hx)
  have hfun : (fun e : ℕ ↦ (2 * (e : ℂ) + 1) * x ^ e) =
      (fun e : ℕ ↦ 2 * ((e : ℂ) * x ^ e) + x ^ e) := by
    ext e; ring
  have hsum : HasSum (fun e : ℕ ↦ (2 * (e : ℂ) + 1) * x ^ e)
      ((1 + x) / (1 - x) ^ 2) := by
    rw [hfun, ← hid]
    exact hsum'
  simpa [sumOnPrimePows_apply, h_term] using hsum.tsum_eq

private lemma tau_sq_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2)
      (LSeries (fun n ↦ (τ (n ^ 2) : ℂ)) s) := by
  convert! EulerProduct.eulerProduct_hasProd _ _ _
      (LSeries.term_zero (fun n ↦ (τ (n ^ 2) : ℂ)) s) using 1
  · funext p; exact Eq.symm (tau_sq_tsum_prime_pow hs p)
  · simp [LSeries.term, tau]
  · intro _ _ hmn; exact TauCeti.LSeries.term_mul_of_coprime (fun _ _ hab => by
      exact_mod_cast isMultiplicative_tauSq.map_mul_of_coprime hab) hmn
  · convert! (LSeriesSummable_tau_sq hs).norm using 1

private lemma tau_sq_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ (τ (n ^ 2) : ℂ)) s =
      ∏' p : Primes, (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2 := by
  exact (tau_sq_LSeries_eulerProduct_hasProd s hs).tprod_eq.symm

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
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulζ := (riemannZeta_eulerProduct_hasProd hs).multipliable
  change riemannZeta s ^ 3 = riemannZeta (2 * s) * LSeries (fun n ↦ (τ (n ^ 2) : ℂ)) s
  have hRHS :
      riemannZeta (2 * s) * LSeries (fun n ↦ (τ (n ^ 2) : ℂ)) s =
        ∏' p : Primes,
          (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ *
            ((1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2) := by
    rw [← riemannZeta_eulerProduct_tprod hs', tau_sq_LSeries_eulerProduct_tprod s hs,
      ← Multipliable.tprod_mul]
    · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩
    · exact ⟨LSeries (fun n ↦ (τ (n ^ 2) : ℂ)) s, tau_sq_LSeries_eulerProduct_hasProd s hs⟩
  rw [hRHS, ← riemannZeta_eulerProduct_tprod hs, ← mulζ.tprod_pow 3]
  refine tprod_congr fun p ↦ ?_
  have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
  have hadd := Complex.one_add_prime_cpow_ne_zero p.2 hs
  have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
    rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 =
        (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
    exact mul_ne_zero hsub hadd
  rw [show (-(2 * s) : ℂ) = -s + -s from by ring,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
  field_simp
  ring

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
  rw [← H, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_pow,
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
lemma LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (μ n) ^ 2) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ (μ n) ^ 2) s n‖ ≤ ‖LSeries.term (fun n ↦ 1) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Complex.norm_intCast, sq_abs, one_mem, CStarRing.norm_of_mem_unitary,
        sq_le_one_iff_abs_le_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have zetaSummable : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  rw [LSeriesSummable, ← summable_norm_iff] at zetaSummable;
  exact Summable.of_norm_bounded zetaSummable hgf

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

@[blueprint
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
lemma moebius_sq_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s))) (L (fun n ↦ (μ n) ^ 2) s) := by
  convert! EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (μ n) ^ 2) s) using 1;
  · funext p; exact Eq.symm (moebius_sq_tsum_prime_pow p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact TauCeti.LSeries.term_mul_of_coprime (fun _ _ hab => by
      rw [isMultiplicative_moebius.map_mul_of_coprime hab]
      push_cast
      ring) mCn
  · convert! (LSeriesSummable_moebius_sq hs).norm using 1

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
  exact (moebius_sq_LSeries_eulerProduct_hasProd s hs).tprod_eq.symm

-- **Zulip question** Do we want `|μ n| = μ^2 (n)` to be a standalone function? It is the indicator
-- of `n` being squarefree.

/--
Zeta alt:
`ζ(s) = ζ(2*s) * ∑_n (|μ(n)|) n^(-s)`,
where omega is the number of distinct prime factors. -/
@[blueprint
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
lemma zeta_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
    riemannZeta (2 * s) * LSeries (fun (n : ℕ) ↦ (μ n : ℂ) ^ 2) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [← riemannZeta_eulerProduct_tprod hs, ← riemannZeta_eulerProduct_tprod hs',
    moebius_sq_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩
  · exact ⟨LSeries (fun n ↦ (μ n) ^ 2) s, moebius_sq_LSeries_eulerProduct_hasProd s hs⟩

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

@[blueprint
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
lemma pow_divisors_mul_injective {m n k : ℕ} (hmn : Nat.Coprime m n) :
    Set.InjOn (fun (p : ℕ × ℕ) => p.1 * p.2) (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)) := by
  apply Set.InjOn.mono _ (by simpa only [Finset.coe_product] using hmn.mul_injOn_divisors)
  intro ⟨_, _⟩ hab
  simp only [Finset.coe_filter, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_coe] at hab ⊢
  exact ⟨hab.1.1, hab.2.1⟩

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
  simp only [coe_mk, pow_divisors_mul mCn, Finset.sum_product,
    Finset.sum_image (fun x hx y hy => pow_divisors_mul_injective (k := 2) mCn
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
  have h_filter : ((Nat.divisors (p ^ k)).filter (fun x => x ^ 2 ∣ p ^ k)) = Finset.image (fun j => p ^ j) (Finset.range (k / 2 + 1)) := by
    ext; simp only [Nat.divisors_prime_pow hp, mem_filter, mem_map, mem_range, Order.lt_add_one_iff, Function.Embedding.coeFn_mk, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨a, Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by
        rw [← pow_mul] at h
        exact Nat.le_of_not_lt fun ha' => absurd (Nat.le_of_dvd (pow_pos hp.pos _) h)
          (not_le_of_gt (pow_lt_pow_right₀ hp.one_lt ha')), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by omega, rfl⟩, by rw [← pow_mul]; exact pow_dvd_pow _ (by omega)⟩
  simp only [moebius_sq, sum_moebius_sq_divisors_apply, h_filter]
  rw [Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective hp.two_le hab, Finset.sum_range_succ']
  split_ifs with h
  · have hk : k / 2 = 0 := by
      rw [Nat.div_eq_zero_iff, or_iff_right (two_ne_zero)]
      by_contra hk
      exact absurd h (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; exact not_and_of_not_right _ (by linarith))
    simp [hk]
  · simp only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one]
    rcases k with _ | _ | _
    · simp at ⊢ h
    · simp [hp.squarefree] at ⊢ h
    · simp_all +decide [ArithmeticFunction.moebius_apply_prime_pow]

/-- I-K (1.33): `μ^2(n) = ∑ d^2|n μ(d)`. -/
@[blueprint
  "moebius_sq_eq"
  (title := "moebius-sq-eq")
  (statement := /-- I-K (1.33): $\mu^2(n) = \sum_{d^2|n} \mu(d)$. -/)
  (proof := /-- Apply the previous two lemmas. -/)]
lemma moebius_sq_eq (n : ℕ) : (μ n) ^ 2 = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by
  by_cases n_zero : n = 0
  · simp [n_zero]
  · rw[← sum_moebius_sq_divisors_apply, IsMultiplicative.multiplicative_factorization sum_moebius_sq_divisors sum_moebius_sq_divisors_IsMultiplicative n_zero]
    have hpf : ∀ p ∈ n.factorization.support, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    simp only [Finset.prod_pow, Finsupp.prod, Nat.support_factorization, Finset.prod_congr rfl (fun x hx =>
      sum_moebius_sq_divisors_apply_prime_pow ((Nat.support_factorization n ▸ hpf) x hx))]
    congr; exact IsMultiplicative.multiplicative_factorization μ isMultiplicative_moebius n_zero

blueprint_comment /--
The Liouville function is Mathlib's canonical `ArithmeticFunction.liouville`, equal to
`(-1)^Ω(n)` away from zero and zero at zero.
-/

-- **NOTE:** `def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
--  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b` exists in the `SelbergBound` file.

/--
Define Complete Multiplicativity for an arithmetic function. -/
@[blueprint
  "IsCompletelyMultiplicative"
  (title := "IsCompletelyMultiplicative")
  (statement := /-- Define Complete Multiplicativity for an arithmetic function. -/)]
def IsCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

/-- A function that is completely multiplicative is also multiplicative. -/
@[blueprint
  "IsCompletelyMultiplicative.isMultiplicative"
  (title := "IsCompletelyMultiplicative.isMultiplicative")
  (statement := /-- A function that is completely multiplicative is also multiplicative. -/)
  (proof := /--
  Let $f$ be a completely multiplicative function. To show that $f$ is multiplicative, we need to verify that $f(1) = 1$ and that $f(ab) = f(a)f(b)$ for all coprime natural numbers $a$ and $b$. Since $f$ is completely multiplicative, we have $f(1) = 1$ by definition. For coprime $a$ and $b$, we can write $ab$ as a product of prime factors, and since $f$ is completely multiplicative, it will factor as the product of the values of $f$ at those prime factors. This means that $f(ab) = f(a)f(b)$ for coprime $a$ and $b$, which shows that $f$ is multiplicative.
  -/)]
lemma IsCompletelyMultiplicative.isMultiplicative {f : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative := by
  exact ⟨hf.1, fun {m n} _ => hf.2 m n⟩

/--
The Liouville function is completely multiplicative. -/
@[blueprint
  "isCompletelyMultiplicative_liouville"
  (title := "isCompletelyMultiplicative liouville")
  (statement := /-- The Liouville function is completely multiplicative. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. To show that $\lambda$ is completely multiplicative, we need to verify that $\lambda(1) = 1$ and that $\lambda(ab) = \lambda(a)\lambda(b)$ for all natural numbers $a$ and $b$.
  -/)]
lemma isCompletelyMultiplicative_liouville : IsCompletelyMultiplicative (liouville : ArithmeticFunction ℝ) := by
  constructor
  · simp [intCoe_apply, liouville_apply_one]
  · intro a b
    simpa only [intCoe_apply, Int.cast_mul] using
      congrArg (fun x : ℤ => (x : ℝ)) (liouville_apply_mul a b)

/--
The Dirichlet series of the Liouville function is `ζ(2s)/ζ(s)`. -/
@[blueprint
  "LSeries_liouville_eq"
  (title := "LSeries liouville eq")
  (statement := /-- The Dirichlet series of the Liouville function is $\zeta(2s)/\zeta(s)$. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is multiplicative, and its value at prime powers is given by $\lambda(p^k) = (-1)^k$. The Dirichlet series of $\lambda$ can be expressed as an Euler product over primes:
\[
L(\lambda, s) = \prod_{p} \left(1 + \lambda(p)p^{-s} + \lambda(p^2)p^{-2s} + \ldots\right) = \prod_{p} \left(1 - p^{-s}\right) \left(1 - p^{-2s}\right)^{-1} = \frac{\zeta(2s)}{\zeta(s)}.
\]
  -/)]
lemma LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗liouville s = riemannZeta (2 * s) / riemannZeta s := by
  let a : ℕ → ℂ := fun n ↦ (liouville n : ℂ)
  have hsum : LSeriesSummable a s := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 1) hs
    refine ⟨1, fun n hn ↦ ?_⟩
    simp only [a, liouville_apply hn, Int.cast_pow, Int.cast_neg, Int.cast_one,
      one_mul, sub_self, Real.rpow_zero, norm_pow, norm_neg, norm_one, one_pow]
    exact le_rfl
  have hmul (m n : ℕ) : a (m * n) = a m * a n := by
    simp only [a, liouville_apply_mul, Int.cast_mul]
  have hp (p : ℕ) (hp : p.Prime) : a p = -1 := by
    simp [a, liouville_apply hp.ne_zero, cardFactors_apply_prime hp]
  have hprod : HasProd (fun p : Primes ↦ (1 + (p : ℂ) ^ (-s))⁻¹) (LSeries a s) := by
    have H := TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence
      (a := a) (c := fun _ ↦ (0 : ℂ))
      (by simp [a, liouville_apply_one]) (fun {_ _} _ _ _ ↦ hmul _ _) (fun p _ r ↦ ?_) hsum
    · convert H using 1
      funext p
      rw [hp p p.prop]
      simp only [zero_mul, add_zero, neg_mul, one_mul, sub_neg_eq_add]
    · rw [show r + 2 = (r + 1) + 1 by omega, pow_succ, hmul]
      ring
  have h2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have H := hprod.mul (riemannZeta_eulerProduct_hasProd hs)
  have H' : HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-(2 * s)))⁻¹)
      (LSeries a s * riemannZeta s) := by
    convert H using 1
    funext p
    rw [show -(2 * s) = -s + -s by ring,
      Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), ← mul_inv]
    congr 1
    ring
  have heq : LSeries a s * riemannZeta s = riemannZeta (2 * s) :=
    H'.unique (riemannZeta_eulerProduct_hasProd h2)
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr heq


/-- `liouville` agrees with `moebius` on square-free numbers -/
@[blueprint
  "liouville_eq_moebius_on_squarefree"
  (title := "liouville eq moebius on squarefree")
  (statement := /-- The Liouville function agrees with the Möbius function on square-free numbers. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. The Möbius function $\mu(n)$ is defined as $0$ if $n$ has a squared prime factor, and otherwise it is $(-1)^{\omega(n)}$, where $\omega(n)$ counts the number of distinct prime factors of $n$. For square-free numbers, we have $\Omega(n) = \omega(n)$, since there are no repeated prime factors. Therefore, for square-free numbers, we have $\lambda(n) = (-1)^{\omega(n)} = \mu(n)$, which shows that the Liouville function agrees with the Möbius function on square-free numbers.
  -/)]
lemma liouville_eq_moebius_on_squarefree (n : ℕ) (hn : Squarefree n) : liouville n = μ n := by
  have hn0 : n ≠ 0 := fun h => not_squarefree_zero (h ▸ hn)
  rw [liouville_apply hn0]
  rw [moebius_apply_of_squarefree hn,
    ← ((cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).2 hn)]

-- Private helpers for LSeries_totient_eq

/-- Cast Nat.totient to ArithmeticFunction ℂ (value at 0 is 0 since Nat.totient 0 = 0). -/
private noncomputable def totientAF : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (Nat.totient n : ℂ), by simp [Nat.totient_zero]⟩

private lemma totientAF_apply (n : ℕ) : totientAF n = (Nat.totient n : ℂ) := rfl

/-- Key identity: (totientAF * ζ) = powR 1, via ∑_{d|n} φ(d) = n. -/
private lemma totientAF_mul_zeta_eq_powR1 :
    (totientAF * (ζ : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) = powR 1 := by
  ext n
  simp only [coe_mul_zeta_apply, totientAF_apply]
  simp only [ArithmeticFunction.powR, ArithmeticFunction.coe_mk]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [hn.ne', ↓reduceIte, Complex.cpow_one]
    rw [← Nat.cast_sum]
    exact_mod_cast Nat.sum_totient n

/-- LSeriesSummable for totientAF when Re(s) > 2, via φ(n) ≤ n. -/
private lemma lseriesSummable_totientAF {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable (↗totientAF) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hs
  exact ⟨1, fun n hn ↦ by
    simp only [totientAF_apply, one_mul]
    rw [show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one]
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.totient_le n⟩

/-- Euler totient series: `∑ φ(n) n^-s = ζ(s-1)/ζ(s)`. -/
@[blueprint
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
lemma LSeries_totient_eq {s : ℂ} (hs : 2 < s.re) :
    LSeries (↗totient) s = riemannZeta (s - 1) / riemannZeta s := by
  have hs1 : 1 < s.re := by linarith
  have hs2 : 1 < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hsum_tot : LSeriesSummable (↗totientAF) s := lseriesSummable_totientAF hs
  have hsum_zeta : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs1
  have hmul : LSeries ↗(totientAF * (ζ : ArithmeticFunction ℂ)) s =
      LSeries ↗totientAF s * LSeries ↗(ζ : ArithmeticFunction ℂ) s :=
    LSeries_mul' hsum_tot hsum_zeta
  have h_prod : LSeries ↗(totientAF * (ζ : ArithmeticFunction ℂ)) s = riemannZeta (s - 1) := by
    rw [totientAF_mul_zeta_eq_powR1, LSeries_powR_eq 1 hs2]
  have h_lzeta : LSeries ↗(ζ : ArithmeticFunction ℂ) s = riemannZeta s := by
    have heq : (↗(ζ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗(ζ : ArithmeticFunction ℕ) := rfl
    rw [heq]; exact LSeries_zeta_eq_riemannZeta hs1
  rw [h_prod] at hmul
  rw [h_lzeta] at hmul
  rw [eq_div_iff hzeta_ne]
  change LSeries (↗totientAF) s * riemannZeta s = riemannZeta (s - 1)
  exact hmul.symm


end ArithmeticFunction
