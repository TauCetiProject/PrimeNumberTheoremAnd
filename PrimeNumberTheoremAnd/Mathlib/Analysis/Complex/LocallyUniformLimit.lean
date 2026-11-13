/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Locally uniform limits and bounded multiplication

Uniform convergence on a set is preserved under multiplication by a function that is bounded
on that set.  This is a basic estimate for locally uniform products.
-/

@[expose] public section

namespace Complex

section UniformMul

/-- On `K`, uniform convergence is preserved when multiplying on the left by a bounded function. -/
theorem _root_.TendstoUniformlyOn.mul_left_bounded {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  obtain ⟨C, hC⟩ := hh
  have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF (ε / max C 1) (div_pos hε hCpos)]
    with n hn z hz
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  calc
    ‖h z‖ * ‖f z - F n z‖ ≤ max C 1 * ‖f z - F n z‖ :=
      mul_le_mul_of_nonneg_right ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _)
    _ < max C 1 * (ε / max C 1) :=
      mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hn z hz) hCpos
    _ = ε := mul_div_cancel₀ ε hCpos.ne'

end UniformMul

end Complex
