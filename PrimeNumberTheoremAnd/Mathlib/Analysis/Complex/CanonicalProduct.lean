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

The convergence results specialize the locally uniform product API for scaled Weierstrass factors
developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
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

/-- The canonical product converges locally uniformly on `ℂ` under the standard summability
hypothesis. -/
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using!
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero

/-- The canonical product is holomorphic on `ℂ` under the standard summability hypothesis. -/
theorem differentiable_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (canonicalProduct m a) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero)
  have hfactor : ∀ i : ℕ, Differentiable ℂ (fun z ↦ weierstrassFactor m (z / a i)) := by
    intro i
    simpa using! (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ (fun z ↦ ∏ n ∈ Finset.range N, weierstrassFactor m (z / a n))
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finsetProd (u := Finset.range N) fun i hi ↦ hfactor i)
  exact differentiableOn_univ.mp <| hloc.differentiableOn hpartial isOpen_univ

/-- The canonical product vanishes at a nonzero prescribed zero, without a summability
hypothesis. -/
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ} (n : ℕ) (hn : a n ≠ 0) :
    canonicalProduct m a (a n) = 0 := by
  exact tprod_of_exists_eq_zero ⟨n, by simp [hn, weierstrassFactor_at_one]⟩

/-- The canonical product vanishes at every nonzero point in `Set.range a`, without a
summability hypothesis. -/
theorem canonicalProduct_eq_zero_of_mem_range {m : ℕ} {a : ℕ → ℂ} {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ∈ Set.range a) : canonicalProduct m a z = 0 := by
  rcases hz with ⟨n, rfl⟩
  exact canonicalProduct_apply_eq_zero n hz0

/-- Away from the prescribed zero set `Set.range a`, the canonical product is nonzero. -/
theorem canonicalProduct_ne_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a) :
    canonicalProduct m a z ≠ 0 := by
  let f : ℕ → ℂ := fun n ↦ weierstrassFactor m (z / a n) - 1
  have hfn : ∀ n, 1 + f n ≠ 0 := by
    intro n
    have hza : z ≠ a n := by
      intro hza
      exact hz ⟨n, hza.symm⟩
    simpa [f] using (weierstrassFactor_div_ne_zero_iff (m := m) (a := a n) (z := z)
      (h_nonzero n)).2 hza
  have hnormsumm :
      Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) :=
    summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero z
  simpa [canonicalProduct, f] using
    (tprod_one_add_ne_zero_of_summable (f := f) hfn hnormsumm)

/-- The zero set of the canonical product is exactly `Set.range a`. -/
theorem canonicalProduct_eq_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z = 0 ↔ z ∈ Set.range a := by
  constructor
  · intro hz0
    by_contra hzrange
    exact (canonicalProduct_ne_zero h_sum h_nonzero hzrange) hz0
  · rintro ⟨n, rfl⟩
    exact canonicalProduct_eq_zero_of_mem_range (h_nonzero n) ⟨n, rfl⟩

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
      (fun w ↦ ∏' n, weierstrassFactorOne (b n * w) ^ (1 : ℕ)) := by
    ext w
    simp only [canonicalProduct, weierstrassFactor_one, pow_one, b, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have h := logDeriv_tprod_weierstrassFactorOne_pow b (fun _ ↦ 1) hm
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
