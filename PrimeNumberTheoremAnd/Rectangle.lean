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


lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by
      rcases hz with ⟨hx01, hx12, hx23, hy01, hy12, hy23⟩
      exact reProdIm_subset_iff.mpr (Set.prod_mono
        (uIcc_subset_uIcc (mem_uIcc_of_le hx01 (hx12.trans hx23))
          (mem_uIcc_of_le (hx01.trans hx12) hx23))
        (uIcc_subset_uIcc (mem_uIcc_of_le hy01 (hy12.trans hy23))
          (mem_uIcc_of_le (hy01.trans hy12) hy23))), by
    refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
    obtain h | h | h | h := hp
    · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
    · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
    · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
    · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)⟩
