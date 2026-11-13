/-
Copyright (c) 2026 Matteo Cipollina and the Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order

@[expose] public section

/-- Translating the input translates the point where its natural analytic order is measured.
The outer function need not be analytic. -/
lemma analyticOrderNatAt_comp_add_const {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [CharZero 𝕜] (f : 𝕜 → 𝕜) (c z : 𝕜) :
    analyticOrderNatAt (fun w : 𝕜 ↦ f (w + c)) z = analyticOrderNatAt f (z + c) := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun w : 𝕜 ↦ w + c) (z₀ := z)
    (analyticAt_id.add analyticAt_const) (by simp)
  simpa only [analyticOrderNatAt, Function.comp_def] using congrArg ENat.toNat h
