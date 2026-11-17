module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Meromorphic.Divisor
public import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import TauCeti.Analysis.Contour.Argument.Rectangle.Divisor

/-!
# Rectangle argument-principle infrastructure

This file identifies the poles of a logarithmic derivative with the divisor support and
provides the rectangle-facing finite divisor sum used by the Kadiri contour lanes.
-/

open Complex Filter Topology Set BigOperators

open scoped Interval

public noncomputable section

theorem logDeriv_poles_eq_divisor_support
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    R ∩ {p | meromorphicOrderAt (logDeriv f) p < 0} =
      (MeromorphicOn.divisor f R).support := by
  ext p
  by_cases hpR : p ∈ R
  · have h0 : MeromorphicOn.divisor f R p = 0 ↔ meromorphicOrderAt f p = 0 := by
      rw [hf.divisor_apply hpR, WithTop.untop₀_eq_zero, or_iff_left (hfinite_order p hpR)]
    simp only [mem_inter_iff, hpR, true_and, mem_ofPred_eq, Function.mem_support, ne_eq, h0]
    refine ⟨fun h h0 ↦ (meromorphicOrderAt_logDeriv_nonneg (hf p hpR) h0).not_gt h, fun h ↦ ?_⟩
    rw [meromorphicOrderAt_logDeriv_eq_neg_one h (hfinite_order p hpR)]
    decide
  · exact iff_of_false (fun h ↦ hpR h.1) fun h ↦ hpR ((MeromorphicOn.divisor f R).supportWithinDomain h)

lemma divisor_support_rectangle_finite (f : ℂ → ℂ) (z w : ℂ) :
    (MeromorphicOn.divisor f (Rectangle z w)).support.Finite :=
  (MeromorphicOn.divisor f _).finiteSupport (isCompact_rectangle z w)

theorem rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : MeromorphicOn f (Rectangle z w))
    (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
    (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hno_boundary :
      Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv f) z w =
      ∑ p ∈
        ((divisor_support_rectangle_finite f z w).toFinset),
          ((MeromorphicOn.divisor f (Rectangle z w)) p : ℂ) := by
  classical
  let R : Set ℂ := Rectangle z w
  have hRfr : frontier R ⊆ R := (isClosed_rectangle z w).frontier_subset
  have hfr (x : ℂ) (hx : x ∈ frontier R) : meromorphicOrderAt f x = 0 := by
    have hd : MeromorphicOn.divisor f R x = 0 := Function.notMem_support.mp
      (disjoint_left.mp hno_boundary (by
        simp only [R, frontier_rectangle, mem_union, mem_reProdIm, mem_insert_iff,
          mem_singleton_iff] at hx
        simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff]
        tauto))
    rw [hf.divisor_apply (hRfr hx), WithTop.untop₀_eq_zero] at hd
    exact hd.resolve_right (hfinite_order x (hRfr hx))
  -- Replace `logDeriv f` by its normal form, which is analytic on the frontier.
  let g := toMeromorphicNFOn (logDeriv f) R
  have hcont : ContinuousOn g (frontier R) := fun x hx ↦
    ((meromorphicNFOn_toMeromorphicNFOn _ R (hRfr hx)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [meromorphicOrderAt_toMeromorphicNFOn hlog (hRfr hx)]
          exact meromorphicOrderAt_logDeriv_nonneg (hf x (hRfr hx)) (hfr x hx))
      ).continuousAt.continuousWithinAt
  have h := TauCeti.Contour.argumentPrinciple_rectBoundary_divisor zRe_le_wRe zIm_le_wIm
    subset_rfl hf hfr
  rw [integral_rectBoundary_congr_codiscreteWithin ((toMeromorphicNFOn_eqOn_codiscrete hlog).filter_mono
    (codiscreteWithin_mono hRfr)), integral_rectBoundary hcont] at h
  have hraw : RectangleIntegral g z w = 2 * Real.pi * I * (TauCeti.divisorCount f R R : ℂ) := h
  rw [rectangleIntegral'_toMeromorphicNFOn_eq hlog, RectangleIntegral', hraw, smul_eq_mul,
    one_div, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul, TauCeti.divisorCount_def,
    finsum_mem_eq_sum_of_inter_support_eq _ (t := (divisor_support_rectangle_finite f z w).toFinset)
      (by rw [Finite.coe_toFinset]
          exact (inter_eq_right.mpr (MeromorphicOn.divisor f R).supportWithinDomain).trans
            (inter_self _).symm),
    Int.cast_sum]

theorem rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt
    {f : ℂ → ℂ} {z w : ℂ} {argumentChange : ℝ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : MeromorphicOn f (Rectangle z w))
    (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
    (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hno_boundary :
      Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support)
    (hargumentChange :
      (argumentChange : ℂ) =
        (2 * Real.pi : ℂ) * RectangleIntegral' (logDeriv f) z w) :
    argumentChange =
      2 * Real.pi *
        ∑ p ∈ (divisor_support_rectangle_finite f z w).toFinset,
          (((MeromorphicOn.divisor f (Rectangle z w)) p : ℤ) : ℝ) := by
  classical
  have hcomplex :
      (argumentChange : ℂ) =
        (2 * Real.pi : ℂ) *
          ∑ p ∈ (divisor_support_rectangle_finite f z w).toFinset,
            (((MeromorphicOn.divisor f (Rectangle z w)) p : ℤ) : ℂ) := by
    rw [hargumentChange]
    rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt zRe_le_wRe zIm_le_wIm
      hf hlog hfinite_order hno_boundary]
  have hre := congrArg Complex.re hcomplex
  simpa [Finset.mul_sum, mul_assoc] using hre

end
