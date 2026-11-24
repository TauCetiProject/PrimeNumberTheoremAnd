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

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)



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

theorem Complex.nhds_hasBasis_square (p : ℂ) : (𝓝 p).HasBasis (0 < ·) (Square p ·) := by
  suffices
      (𝓝 p.re ×ˢ 𝓝 p.im).HasBasis (0 < ·)
        (equivRealProdCLM.symm.toHomeomorph ⁻¹' Square p ·)
    by simpa only [← nhds_prod_eq, Homeomorph.map_nhds_eq, Homeomorph.image_preimage]
      using! this.map equivRealProdCLM.symm.toHomeomorph
  apply ((nhds_basis_Icc_pos p.re).prod_same_index_mono (nhds_basis_Icc_pos p.im) ?_ ?_).congr
  · intro; rfl
  · intros
    rw [← uIcc_of_lt (by linarith), ← uIcc_of_lt (by linarith)]
    simpa [Square, Rectangle, show ∀ s t : Set ℝ,
      equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t from fun s t ↦ rfl] using by ring_nf
  all_goals exact (antitone_const_tsub.Icc (monotone_id.const_add _)).monotoneOn _

lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  wlog hc_pos : 0 < c generalizing c with h
  · rw [(show Square p c = Square p (-c) by
      simp [Square, Rectangle, uIcc_comm])]
    exact h (neg_ne_zero.mpr hc) <| neg_pos.mpr <| hc.lt_of_le <| not_lt.mp hc_pos
  exact (nhds_hasBasis_square p).mem_of_mem hc_pos

lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  apply reProdIm_subset_iff.mpr
  refine Set.prod_mono (uIcc_subset_uIcc ?_ ?_) (uIcc_subset_uIcc ?_ ?_)
  all_goals
    apply mem_uIcc_of_le
    all_goals
      simp only [add_re, add_im, sub_re, sub_im, neg_re, neg_im, ofReal_re, ofReal_im,
        mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero,
        add_zero, zero_add]
      linarith

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Square p c ⊆ Rectangle z w := by
  obtain ⟨ε, hε0, hε⟩ := ((Complex.nhds_hasBasis_square p).mem_iff' _).mp pInRectInterior
  filter_upwards [Ioo_mem_nhdsGT (hε0)] with _ ⟨hε'0, hε'⟩
  exact subset_trans (square_subset_square hε'0 hε'.le) hε
