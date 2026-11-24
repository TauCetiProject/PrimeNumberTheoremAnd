/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelKernel
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Abel-summation continuation of the Riemann zeta function

Writing `{u}` for the fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, the
Abel-summation tail formula is

`ζ₁(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`,

bundled as `zetaAbelContinuationFormula`. Its equality with `riemannZeta` on the punctured right
half-plane is `TauCeti.riemannZeta_eq_one_add_inv_sub_integral_fract`.

The kernel lives in `RiemannZetaAbelKernel`.
-/

@[expose] public section

open Real Set MeasureTheory Complex

/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u
