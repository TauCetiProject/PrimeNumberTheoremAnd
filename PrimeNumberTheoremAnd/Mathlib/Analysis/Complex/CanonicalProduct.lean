/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

Convergence, holomorphy and the zero set are the constant-genus case of Tau Ceti's variable-genus
primary products (`Complex.hasProdLocallyUniformlyOn_weierstrassFactor_div`,
`Complex.differentiable_tprod_weierstrassFactor_div`,
`Complex.tprod_weierstrassFactor_div_eq_zero_iff`).
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Complex

/-- The canonical product `∏' n, E_m(z / a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl

/-- The logarithmic derivative of a genus-one sequence-indexed canonical product is the expected
sum of the logarithmic derivatives of the Weierstrass factors, away from the prescribed zero set. -/
theorem logDeriv_canonicalProduct_one_eq_tsum {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (2 : ℕ))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a) :
    logDeriv (canonicalProduct 1 a) z =
      ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
  let b : ℕ → ℂ := fun n ↦ (a n)⁻¹
  have hm : Summable (fun n ↦ ((1 : ℕ) : ℝ) * ‖b n‖ ^ 2) := by
    simpa only [b, Nat.cast_one, one_mul, norm_inv] using h_sum
  have hfun : canonicalProduct 1 a =
      (fun w ↦ ∏' n, weierstrassFactor 1 (b n * w) ^ (1 : ℕ)) := by
    ext w
    simp only [canonicalProduct, pow_one, b, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have h := logDeriv_tprod_weierstrassFactor_one_pow b (fun _ ↦ 1) hm
    (z := z) (fun n _ ↦ by
      intro hn
      apply hz
      refine ⟨n, ?_⟩
      dsimp only [b] at hn
      have he := congrArg (fun x : ℂ ↦ a n * x) hn
      simpa only [← mul_assoc, mul_inv_cancel₀ (h_nonzero n), one_mul, mul_one] using he.symm)
  rw [h]
  apply tsum_congr
  intro n
  simpa only [Nat.cast_one, one_mul] using logDerivWeierstrassFactorOneMul_inv (h_nonzero n)
    (fun hn ↦ hz ⟨n, hn.symm⟩)

end Complex
