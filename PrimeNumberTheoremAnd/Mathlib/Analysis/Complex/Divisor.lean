/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
public import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct


/-!
# Hadamard factorization (preliminaries)

This file develops preliminary lemmas towards Hadamard factorization for entire functions on `ℂ`.
Zeros are indexed with multiplicity using `MeromorphicOn.divisor`, then assembled into the
corresponding canonical product.

## Main definitions

- `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types enumerating
  zeros with multiplicity.
- `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.

## Main results

- The support of the divisor is discrete and countable, and meets compact sets in finitely many
  points.
- Under the standard summability hypothesis, the canonical product converges uniformly on compact
  sets, and its analytic order agrees with the expected multiplicity away from `0`.
-/

@[expose] public section

namespace Complex.Hadamard

open scoped Topology
open Set

/-!
## Exact multiplicity of the divisor canonical product

The infinite canonical product has precisely the zero multiplicities encoded by the divisor index.
This specializes Tau Ceti's exact zero orders of variable-genus primary products
(`Complex.analyticOrderAt_tprod_weierstrassFactor_div`).
-/

/-- The analytic order of the divisor-indexed canonical product at `z₀` is the number of
divisor indices lying over `z₀`. -/
theorem analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have hset : {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
      divisorZeroIndex₀_val p ≠ 0 ∧ divisorZeroIndex₀_val p = z₀} =
      {p | divisorZeroIndex₀_val p = z₀} := by
    ext p
    simp
  refine (analyticOrderAt_tprod_weierstrassFactor_div (p := fun _ ↦ m) (fun R _ ↦
    (h_sum.mul_left (R ^ (m + 1))).congr fun _ ↦ by rw [div_pow, div_eq_mul_inv, inv_pow])
    z₀).trans ?_
  rw [hset, Set.ncard_eq_toFinset_card _ (divisorZeroIndex₀_fiber_finite f z₀)]
  rfl

/-- Away from the indexed divisor, the divisor canonical product is nonzero. -/
theorem divisorCanonicalProduct_ne_zero_of_forall_ne
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
  have hA := (differentiableOn_divisorCanonicalProduct_univ m f h_sum).analyticOnNhd isOpen_univ
  refine ((hA z trivial).analyticOrderAt_eq_zero).1 ?_
  rw [analyticOrderAt_divisorCanonicalProduct_eq_fiber_card m f h_sum, Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  exact fun p hp ↦ hz p ((mem_divisorZeroIndex₀_fiberFinset f z p).1 hp).symm

end Hadamard
end Complex
