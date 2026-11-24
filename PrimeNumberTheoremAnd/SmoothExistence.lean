module

public import Architect
public import Batteries.Tactic.Lemma
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Tactic.Bound
public import Mathlib.Algebra.Notation.Support
import TauCeti.Analysis.Calculus.BumpFunction.Multiplicative


public section


open MeasureTheory Set Real
open scoped ContDiff

blueprint_comment /--
Let $\nu$ be a bumpfunction.
-/

@[blueprint
  (title := "SmoothExistence")
  (statement := /--
  There exists a smooth (once differentiable would be enough),
  nonnegative ``bumpfunction'' $\nu$,
  supported in $[1/2,2]$ with total mass one:
  $$
  \int_0^\infty \nu(x)\frac{dx}{x} = 1.
  $$
  -/)
  (proof := /-- Same idea as Urysohn-type argument. -/)]
lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  obtain ⟨ν, h1, h2, h3, h4, -⟩ := TauCeti.exists_smooth_symmetric_bump one_lt_two
  exact ⟨ν, h1, h2, by rwa [one_div], by rwa [integral_Ici_eq_integral_Ioi]⟩
