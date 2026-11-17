module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Residue.LogDeriv
public import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import TauCeti.Analysis.Contour.Argument.Rectangle.Divisor

/-!
# Rectangle argument-principle infrastructure

This file isolates the local logarithmic-derivative residue calculation and the
rectangle-facing finite divisor sum used by the Kadiri contour lanes.
-/

open Complex Filter Topology Set BigOperators Asymptotics

open scoped Interval

public noncomputable section

lemma logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, hg0, heq⟩ := TauCeti.Contour.logDeriv_eventuallyEq_principalPart hf hord
  have hbounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    (hg.logDeriv hg0).continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  refine (hbounded.mono nhdsWithin_le_nhds).congr' ?_ .rfl
  filter_upwards [heq] with z hz
  simp only [Pi.sub_apply, hz, div_eq_mul_inv, add_sub_cancel_left]

theorem logDeriv_residue_eq_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    residue (logDeriv f) p = (n : ℂ) := by
  have h := TauCeti.Contour.tendsto_sub_mul_nhds_residue hf.logDeriv
    (TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv hf)
  rw [TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt hf hord] at h
  exact residue_eq_of_tendsto h

theorem logDeriv_poles_eq_divisor_support
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    R ∩ {p | meromorphicOrderAt (logDeriv f) p < 0} =
      (MeromorphicOn.divisor f R).support := by
  classical
  let D := MeromorphicOn.divisor f R
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpR, hpneg⟩
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    by_cases hn0 : n = 0
    · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
        simpa [hn0] using hn.symm
      have hnonneg :=
        meromorphicOrderAt_logDeriv_nonneg (hf p hpR) hord0
      exact False.elim (not_lt_of_ge hnonneg hpneg)
    · have hpD_ne : D p ≠ 0 := by
        change (MeromorphicOn.divisor f R) p ≠ 0
        rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
        simp [hn0]
      simp [D, Function.mem_support, hpD_ne]
  · intro hpD
    have hpR : p ∈ R := (MeromorphicOn.divisor f R).supportWithinDomain hpD
    have hpD_ne : D p ≠ 0 := by
      simpa [D, Function.mem_support] using hpD
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hpD_ne (by rw [← hn]; simp [hn0])
    have hneg_one :=
      meromorphicOrderAt_logDeriv_eq_neg_one
        (by rw [← hn]; exact_mod_cast hn0) (hfinite_order p hpR)
    refine ⟨hpR, ?_⟩
    change meromorphicOrderAt (logDeriv f) p < 0
    rw [hneg_one]
    exact WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)

lemma divisor_support_rectangle_finite (f : ℂ → ℂ) (z w : ℂ) :
    (MeromorphicOn.divisor f (Rectangle z w)).support.Finite := by
  let R : Set ℂ := Rectangle z w
  let D := MeromorphicOn.divisor f R
  have hR_compact : IsCompact R := by
    exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  exact D.finiteSupport hR_compact

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
