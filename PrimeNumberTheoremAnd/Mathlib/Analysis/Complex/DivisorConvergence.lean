/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
public import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Set.Finite.Lattice


/-!
# Convergence and holomorphy of divisor-indexed canonical products

This file proves locally uniform convergence, holomorphy, and the
genus-one logarithmic-derivative identity for the divisor-indexed canonical product
`Complex.Hadamard.divisorCanonicalProduct`, under the standard summability hypothesis.

It also provides finiteness lemmas for subsets of the divisor index type cut out by a norm bound.
-/

@[expose] public section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finiteness of “small” divisor indices
-/

lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  have hs := (MeromorphicOn.divisor_finite_inter_support_of_isCompact (f := f)
    (isCompact_closedBall (0 : ℂ) B) hBU subset_rfl).sigma
    (fun z _ ↦ Set.finite_univ (α := Fin (Int.toNat (MeromorphicOn.divisor f U z))))
  refine (Set.Finite.preimage Subtype.val_injective.injOn hs).subset ?_
  intro p hp
  exact ⟨⟨(dist_zero_right _).trans_le hp,
    divisorZeroIndex₀_val_mem_divisor_support' p⟩, Set.mem_univ _⟩

/-!
## Logarithmic-derivative terms
-/

/-- The genus-one logarithmic-derivative zero terms are summable away from the zero set whenever
the genus-one divisor product is summable. -/
theorem summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  have hs := Complex.summable_norm_logDerivWeierstrassFactorOneMul
    (fun p : divisorZeroIndex₀ f Set.univ ↦ (divisorZeroIndex₀_val p)⁻¹)
    (by simpa only [norm_inv] using h_sum) z
  apply hs.of_norm.congr
  intro p
  exact Complex.logDerivWeierstrassFactorOneMul_inv (divisorZeroIndex₀_val_ne_zero p) (hz p)

/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product

These specialize Tau Ceti's variable-genus primary products to the constant genus `m`.
-/

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) :=
  hasProdLocallyUniformlyOn_weierstrassFactor_div (p := fun _ ↦ m) fun R _ ↦
    (h_sum.mul_left (R ^ (m + 1))).congr fun _ ↦ by rw [div_pow, div_eq_mul_inv, inv_pow]

theorem differentiableOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
  (differentiable_tprod_weierstrassFactor_div (p := fun _ ↦ m) fun R _ ↦
    (h_sum.mul_left (R ^ (m + 1))).congr fun _ ↦ by
      rw [div_pow, div_eq_mul_inv, inv_pow]).differentiableOn

/-- Pointwise differentiability of the divisor-indexed canonical product under the standard
summability hypothesis. -/
theorem differentiableAt_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    DifferentiableAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  ((differentiableOn_divisorCanonicalProduct_univ m f h_sum) z (by simp)).differentiableAt
    (by simp)

/-!
## Logarithmic derivative of the genus-one divisor product
-/

/-- The logarithmic derivative of a genus-one divisor canonical product is the expected sum of
zero terms.  The logarithmic-derivative term summability is derived from the genus-one divisor
summability and the assumption that the evaluation point is not one of the indexed zeros. -/
theorem logDeriv_divisorCanonicalProduct_one_eq_tsum
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  let a : divisorZeroIndex₀ f Set.univ → ℂ := fun p ↦ (divisorZeroIndex₀_val p)⁻¹
  have hm : Summable (fun p ↦ ((1 : ℕ) : ℝ) * ‖a p‖ ^ 2) := by
    simpa only [a, Nat.cast_one, one_mul, norm_inv] using h_sum
  have hfun : divisorCanonicalProduct 1 f Set.univ =
      (fun w ↦ ∏' p, Complex.weierstrassFactor 1 (a p * w) ^ (1 : ℕ)) := by
    ext w
    simp only [divisorCanonicalProduct, pow_one, a, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have h := Complex.logDeriv_tprod_weierstrassFactor_one_pow a (fun _ ↦ 1) hm
    (z := z) (fun p _ ↦ by
      dsimp only [a]
      intro hp
      apply hz p
      calc
        z = divisorZeroIndex₀_val p * ((divisorZeroIndex₀_val p)⁻¹ * z) := by
          rw [← mul_assoc, mul_inv_cancel₀ (divisorZeroIndex₀_val_ne_zero p), one_mul]
        _ = divisorZeroIndex₀_val p := by rw [hp, mul_one])
  rw [h]
  apply tsum_congr
  intro p
  simpa only [Nat.cast_one, one_mul] using
    Complex.logDerivWeierstrassFactorOneMul_inv (divisorZeroIndex₀_val_ne_zero p) (hz p)

end Complex.Hadamard
