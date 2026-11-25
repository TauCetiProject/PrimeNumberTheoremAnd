module

public import Architect
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.Interval.Set.Monotone
public import TauCeti.Analysis.Complex.Rectangle


@[expose] public section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

blueprint_comment /--
This files gathers definitions and basic properties about rectangles.
-/

blueprint_comment /--
The border of a rectangle is the union of its four sides.
-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
@[blueprint
  (title := "RectangleBorder")
  (statement := /-- A Rectangle's border, given corners $z$ and $w$ is the union of the four
    sides. -/)]
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]
