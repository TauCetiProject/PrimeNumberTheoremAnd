module

public import Architect
public import TauCeti.Analysis.Complex.Hadamard.FiniteOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Hadamard


public section

blueprint_comment /--

In this file, we record the Hadamard Factorization theorem for functions of finite order,
and its specialization to the completed zeta function.

-/

attribute [blueprint "FiniteOrderHadamard"
  (title := "Hadamard factorization")
  (statement := /--
  Let $f$ be an entire function, not identically zero, such that for every $b>\rho$ there is
  $C_b>0$ with $|f(z)|\leq C_b\exp(|z|^b)$ for all $z$, and let $n=\lfloor\rho\rfloor$. Then the
  nonzero zeros $\alpha$ of $f$, counted with multiplicity $m_\alpha$, satisfy
  $\sum_\alpha m_\alpha|\alpha|^{-(n+1)}<\infty$, and
  $$f(z)=z^{m_0}e^{P(z)}\prod_{\alpha\neq 0}E_n(z/\alpha)^{m_\alpha},$$
  where $m_0$ is the order of $f$ at $0$, $P$ is a polynomial of degree at most $n$, $E_n$ is
  the Weierstrass elementary factor of degree $n$, and the product converges locally
  uniformly.
  -/)
  (proof := /--
  Jensen's formula bounds the number of zeros in a disc of radius $r$ by $O(r^b)$, which gives
  the convergence of $\sum_\alpha m_\alpha|\alpha|^{-(n+1)}$ and of the canonical product. The
  quotient of $f$ by $z^{m_0}$ times the canonical product is entire and zero-free, so it is
  $e^{g}$. Lower bounds for the canonical product on suitable circles bound $\Re g(z)$ by
  $O(|z|^{b})$, and the Borel--Carath\'eodory inequality then shows $g$ is a polynomial of degree
  at most $n$.
  -/)
  (latexEnv := "theorem")]
  TauCeti.finite_order_hadamard

attribute [blueprint "ZetaHadamardProduct"
  (title := "Hadamard product for the completed zeta function")
  (statement := /--
  Let $\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$, an entire function with $\xi(0)=1$. There
  are constants $a,b\in\C$ with $e^a=\xi(0)$ and $b=\xi'(0)/\xi(0)$ such that for all $s$,
  $$\xi(s)=e^{a+bs}\prod_{\rho}\left(\left(1-\frac{s}{\rho}\right)e^{s/\rho}\right)^{m_\rho},$$
  where $\rho$ runs over the zeros of $\xi$ with multiplicity $m_\rho$ and the product is
  multipliable.
  -/)
  (proof := /--
  $\xi$ is entire of order at most one, by Stirling's formula for $\Gamma$ and the
  polynomial growth of $(s-1)\zeta(s)$ in vertical strips. Apply
  Theorem \ref{FiniteOrderHadamard} with $\rho=1$.
  -/)
  (proofUses := ["FiniteOrderHadamard"])
  (latexEnv := "theorem")]
  TauCeti.LFunctions.zetaEntireCompletion_hadamard
