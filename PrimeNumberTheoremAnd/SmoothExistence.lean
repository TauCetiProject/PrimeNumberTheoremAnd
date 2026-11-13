module

public import Architect
public import Batteries.Tactic.Lemma
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Tactic.Bound
public import Mathlib.Algebra.Notation.Support


public section


open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  obtain ⟨Ψ, hΨsmooth, hΨrange, hΨsupport, hΨone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) isOpen_Ioo isClosed_Icc
      (fun x hx ↦ ⟨h1.trans_le hx.1, hx.2.trans_lt h3⟩)
  refine ⟨Ψ, hΨsmooth, ?_, ?_, ?_, hΨsupport⟩
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hΨsupport ▸ Ioo_subset_Icc_self)
  · apply Set.indicator_le'
    · intro x hx
      rw [Pi.one_apply, (hΨone x).mp hx]
    · exact fun x _ ↦ (hΨrange (mem_range_self x)).1
  · intro x
    by_cases hx : x ∈ Ioo a d
    · simpa only [indicator_of_mem hx, Pi.one_apply] using
        (hΨrange (mem_range_self x)).2
    · simpa only [indicator_of_notMem hx, Pi.zero_apply] using
        (le_of_eq (Function.notMem_support.mp (hΨsupport.symm ▸ hx)))

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
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport]
      simp only [Function.support_eq_preimage, Set.preimage_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith
