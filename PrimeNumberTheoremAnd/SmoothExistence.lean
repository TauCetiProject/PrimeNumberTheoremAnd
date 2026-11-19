module

public import Architect
public import Batteries.Tactic.Lemma
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Tactic.Bound
public import Mathlib.Algebra.Notation.Support


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
  let f : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let ψ := f.normed volume
  have hψsupp : Function.support ψ ⊆ Icc (1 / 2) 2 := by
    rw [show Function.support ψ = Metric.ball 1 f.rOut from f.support_normed_eq]
    intro x hx
    change dist x 1 < 1 / 2 at hx
    rw [Real.dist_eq, abs_lt] at hx
    constructor <;> linarith
  refine ⟨fun x ↦ x * ψ x, contDiff_id.mul f.contDiff_normed, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · exact mul_nonneg (le_trans (by norm_num) (hψsupp hx).1) (f.nonneg_normed x)
  · intro x hx
    exact hψsupp (mul_ne_zero_iff.mp hx).2
  · have hquot : (fun x ↦ x * ψ x / x) = ψ := by
      funext x
      by_cases hx : x = 0
      · subst x
        have hzero : ψ 0 = 0 := by
          by_contra h
          have := (hψsupp h).1
          norm_num at this
        simp [hzero]
      · exact mul_div_cancel_left₀ (ψ x) hx
    rw [hquot, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact f.integral_normed
    · intro x hx
      by_contra h
      exact hx (le_trans (by norm_num) (hψsupp h).1)
