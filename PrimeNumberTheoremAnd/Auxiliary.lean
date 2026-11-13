/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
### Auxiliary lemmas
-/

public section

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, fun hf ↦ hf.hasDerivAt.ofReal_comp.differentiableAt⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]
