/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Digamma analyticity on the right half-plane

The all-height positive-strip growth bound is supplied by the imported native
`Complex.exists_norm_digamma_le_log`. This file retains right-half-plane analyticity.
-/

@[expose] public section

open Filter Topology Finset Nat

namespace Complex

/-- Digamma is analytic on the open right half-plane. -/
theorem analyticOnNhd_digamma_re_pos : AnalyticOnNhd ℂ digamma {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hregular := Complex.ne_neg_natCast_of_re_pos hz
  simpa only [digamma_def, logDeriv, Pi.div_def] using
    (analyticAt_Gamma hregular).deriv.div (analyticAt_Gamma hregular) (Gamma_ne_zero hregular)

end Complex
