module

public import Architect
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PrimeNumberTheoremAnd.Rectangle
public import TauCeti.Analysis.Contour.Residue.Rectangle


@[expose] public section

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
@[blueprint
  (title := "RectangleIntegral")
  (statement := /--
  A RectangleIntegral of a function $f$ is one over a rectangle
  determined by $z$ and $w$ in $\C$.
  We will sometimes denote it by $\int_{z}^{w} f$.
  (There is also a primed version, which is
  $1/(2\pi i)$ times the original.)
  -/)]
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

attribute [blueprint
  "existsDifferentiableOn_of_bddAbove"
  (title := "existsDifferentiableOn-of-bddAbove")
  (statement := /--
  If $f$ is differentiable on a set $s$ except at $c\in s$,
  and $f$ is bounded above on $s\setminus\{c\}$, then there
  exists a differentiable function $g$ on $s$ such that $f$
  and $g$ agree on $s\setminus\{c\}$.
  -/)
  (proof := /--
  This is the Riemann Removable Singularity Theorem, slightly
  rephrased from what's in Mathlib. (We don't care what the
  function $g$ is, just that it's holomorphic.)
  -/)]
  Complex.differentiableOn_update_limUnder_of_bddAbove

attribute [blueprint
  "DifferentiableOn.vanishesOnRectangle"
  (uses := ["RectangleIntegral"])
  (title := "DifferentiableOn.vanishesOnRectangle")
  (statement := /--
  If $f$ is holomorphic on a rectangle $z$ and $w$, then the
  integral of $f$ over the rectangle with corners $z$ and $w$
  is $0$.
  -/)
  (proof := /-- This is in a Mathlib PR. -/)]
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn

attribute [blueprint
  "ResidueTheoremOnRectangleWithSimplePole"
  (uses := ["RectangleIntegral"])
  (title := "ResidueTheoremOnRectangleWithSimplePole")
  (statement := /--
  Let $\sigma_1\le\sigma_2$, $t_1\le t_2$, and let $P$ be a finite set of points in the open
  rectangle $(\sigma_1,\sigma_2)\times(t_1,t_2)$. Suppose that $f$ is continuous on the closed
  rectangle minus $P$, holomorphic on the open rectangle minus $P$, and meromorphic at each point
  of $P$. Then the integral of $f$ over the boundary of the rectangle is
  $2\pi i\sum_{p\in P}\operatorname{Res}_{s=p}f(s)$.
  In particular, if $f$ is holomorphic on a rectangle except for a simple pole at $p$, that is,
  $f = g + A/(s-p)$ with $g$ holomorphic on the rectangle and $A\in\C$, then the integral of
  $f$ over the rectangle is $2\pi i A$.
  -/)
  (proof := /--
  Excise a small disc around each pole. The integral over the boundary of the rectangle with the
  discs removed vanishes by Cauchy's theorem, and the integral over a small circle around $p$ is
  $2\pi i\operatorname{Res}_{s=p}f(s)$, computed from the Laurent expansion of $f$ at $p$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.Contour.rectangle_boundary_integral_eq_residues
