/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Extra logarithmic counting API

This file collects basic logarithmic-counting identities used by the Hadamard factorization API.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

/-- Total multiplicity of nonzero support points inside the closed ball of radius `|R|`. -/
noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)

/-- The nonzero mass in closed balls is monotone in the radius for non-negative functions. -/
lemma massClosedBall₀_mono {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    massClosedBall₀ D R₁ ≤ massClosedBall₀ D R₂ := by
  classical
  unfold massClosedBall₀
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => by exact_mod_cast hD z)
  intro z hz
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hz ⊢
  have hz₁ := (toClosedBall R₁ D).supportWithinDomain hz.1
  have hz₂ : z ∈ closedBall (0 : E) |R₂| := (Metric.closedBall_subset_closedBall
    (by simpa only [abs_of_nonneg hR₁, abs_of_nonneg (hR₁.trans hR₁₂)] using hR₁₂)) hz₁
  refine ⟨?_, hz.2⟩
  rw [Function.mem_support, toClosedBall_eval_within D hz₂]
  simpa only [Function.mem_support, toClosedBall_eval_within D hz₁] using hz.1

end Function.locallyFinsuppWithin
