/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Elementary complex-analysis API

Neighborhoods contained in complex half-planes.
-/

@[expose] public section

namespace Complex

/-- If `a < re z`, nested open balls around `z` stay in the half-plane `re · ≥ a`. -/
theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  have hopen : IsOpen {z : ℂ | a < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ha)
  refine ⟨r / 2, half_pos hr, fun x y hx hy ↦ le_of_lt (hball ?_)⟩
  exact (dist_triangle y x z₀).trans_lt (by linarith)

end Complex
