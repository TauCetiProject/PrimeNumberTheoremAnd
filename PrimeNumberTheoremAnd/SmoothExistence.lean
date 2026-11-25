module

public import Architect
import TauCeti.Analysis.Calculus.BumpFunction.Multiplicative


public section


blueprint_comment /--
Let $\nu$ be a bumpfunction.
-/

attribute [blueprint "SmoothExistence"
  (title := "SmoothExistence")
  (statement := /--
  For every $R>1$ there exists a smooth, nonnegative ``bumpfunction'' $\nu$, supported in
  $[R^{-1},R]$, with total mass one,
  $$
  \int_0^\infty \nu(x)\frac{dx}{x} = 1,
  $$
  and symmetric: $\nu(1/x)=\nu(x)$ for $x>0$. We use it with $R=2$.
  -/)
  (proof := /--
  Take a smooth bump in the additive variable $u=\log x$, supported in $[-\log R,\log R]$ and
  even, and normalize its integral to $1$; then $\nu(x)$ is its value at $\log x$.
  -/)]
  TauCeti.exists_smooth_symmetric_bump
