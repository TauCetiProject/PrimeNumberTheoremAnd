module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Principle
public import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Rectangle argument-principle infrastructure

This file isolates the local logarithmic-derivative residue calculation and the
rectangle-facing finite divisor sum used by the Kadiri contour lanes.
-/

open Complex Filter Topology Set BigOperators Asymptotics

open scoped Interval

public noncomputable section

private lemma tendsto_mul_self_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hp_small :
      (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : ℂ => (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p] fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p))) (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal.symm
  have hsum_tendsto :
      Tendsto
        (fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hsum :
      (fun z : ℂ => (z - p) * f z) =ᶠ[𝓝[≠] p]
        fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z) := by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hsum.symm

lemma logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, hg0, heq⟩ := TauCeti.Contour.logDeriv_eventuallyEq_principalPart hf hord
  have hbounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    (TauCeti.Contour.analyticAt_logDeriv_of_analyticAt hg hg0).continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  refine (hbounded.mono nhdsWithin_le_nhds).congr' ?_ .rfl
  filter_upwards [heq] with z hz
  simp only [Pi.sub_apply, hz, div_eq_mul_inv, add_sub_cancel_left]

theorem logDeriv_residue_eq_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    residue (logDeriv f) p = (n : ℂ) :=
  residue_eq_of_tendsto
    (tendsto_mul_self_of_sub_principal_isBigO_one
      (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord))

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

private theorem sumResiduesIn_eq_finset_of_finite {F : ℂ → ℂ} {S : Set ℂ}
    (hS : S.Finite) :
    sumResiduesIn F S = ∑ z ∈ hS.toFinset, residue F z := by
  let Sfin : Finset ℂ := hS.toFinset
  change sumResiduesIn F S = ∑ z ∈ Sfin, residue F z
  rw [sumResiduesIn]
  have hS_eq : S = (Sfin : Set ℂ) := hS.coe_toFinset.symm
  rw [hS_eq, tsum_fintype, ← Finset.sum_coe_sort Sfin]
  rfl

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
  let D := MeromorphicOn.divisor f R
  have hsupport : D.support.Finite := divisor_support_rectangle_finite f z w
  have hlog_simple : HasSimplePolesOn (logDeriv f) R :=
    fun p hp ↦ TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv (hf p hp)
  have hlog_poles_eq :
      R ∩ {s | meromorphicOrderAt (logDeriv f) s < 0} = D.support := by
    simpa [R, D] using
      logDeriv_poles_eq_divisor_support (f := f) (R := R) hf hfinite_order
  have hlog_no_boundary :
      Disjoint (RectangleBorder z w) {s | meromorphicOrderAt (logDeriv f) s < 0} := by
    rw [Set.disjoint_left]
    intro s hs_border hs_log_pole
    have hsR : s ∈ R := by
      exact rectangleBorder_subset_rectangle z w hs_border
    have hsD : s ∈ D.support := by
      rw [← hlog_poles_eq]
      exact ⟨hsR, hs_log_pole⟩
    exact Set.disjoint_left.mp (by simpa [R, D] using hno_boundary) hs_border hsD
  have hlog_poles_finite :
      (Rectangle z w ∩ {s | meromorphicOrderAt (logDeriv f) s < 0}).Finite := by
    simpa [R, D, hlog_poles_eq] using hsupport
  have hrect :=
    RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hlog hlog_no_boundary
      hlog_poles_finite hlog_simple
  rw [hrect, hlog_poles_eq, sumResiduesIn_eq_finset_of_finite hsupport]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpD : p ∈ D.support := by
    simpa [D] using (hsupport.mem_toFinset.mp hp)
  have hpR : p ∈ R := D.supportWithinDomain hpD
  have hpD_ne : D p ≠ 0 := by
    simpa [Function.mem_support] using hpD
  have horder_ne_zero_or_top :
      meromorphicOrderAt f p ≠ 0 ∧ meromorphicOrderAt f p ≠ ⊤ := by
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    constructor
    · intro hzero
      exact hpD_ne (by simp [hzero])
    · intro htop
      exact hpD_ne (by simp [htop])
  obtain ⟨n, hn⟩ :=
    WithTop.ne_top_iff_exists.mp horder_ne_zero_or_top.2
  have hres :
      residue (logDeriv f) p = (n : ℂ) :=
    logDeriv_residue_eq_meromorphicOrderAt (hf p hpR) hn.symm
  rw [hres]
  change (n : ℂ) = ((MeromorphicOn.divisor f R) p : ℂ)
  rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
  simp

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
