/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorNativeProduct
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaValues


/-!
# Hadamard factorization for the completed Riemann zeta function

This file specializes Tao's finite-order Hadamard factorization theorem
([tao246bComplexAnalysis], Thm. 22)
to the entire completed zeta function `completedRiemannZeta₀` (Λ₀) and to Riemann's entire
`riemannXi`. The analytic input is the order-one bound `completedRiemannZeta₀_order_one` from
`ZetaFiniteOrder`; the product is the divisor-indexed canonical Weierstrass product at genus
`⌊ρ⌋ = 1`. Native-support products use `TauCeti.divisorProductOne`, with multiplicities
from `MeromorphicOn.divisor`.

Note: `completedRiemannZeta` (Λ with simple poles at `0` and `1`) is a different object; Hadamard
applies to Λ₀.  The negative even integers are the trivial zeros of `riemannZeta`, not zeros of
Λ₀.  Accordingly, the divisor indices in this file remain generic zeros of Λ₀ rather than a
separate enumeration of the trivial zeros of ζ.

`RiemannZetaValues` proves `completedRiemannZeta₀_zero_ne_zero`, using the Euler-Mascheroni
formula for `Λ₀(1)` together with explicit numerical bounds.  Therefore the origin monomial in the
Λ₀ Hadamard product is also removable.

## Main results

* `completedRiemannZeta₀_entireOfOrderAtMost_one` : Λ₀ has order at most one
* `riemannXi_entireOfOrderAtMost_one` : Riemann's entire `ξ` has order at most one
* `analyticOrderNatAt_riemannXi_zero` : the origin monomial in `ξ`'s Hadamard product is absent
* `analyticOrderNatAt_completedRiemannZeta₀_zero` : the origin monomial in Λ₀'s Hadamard product
  is absent
* `completedRiemannZeta₀_hadamard_factorization` : canonical product form over divisor indices
* `completedRiemannZeta₀_hadamard_factorization_no_monomial` : Λ₀ product with the origin monomial
  removed
* `riemannXi_hadamard_factorization` : canonical product form for Riemann's entire `ξ`
* `riemannXi_hadamard_factorization_no_monomial`, `_reindex_no_monomial`,
  `_sequence_no_monomial` : xi products with the origin monomial removed
* `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq` : genus-one summability of xi's nonzero
  zero divisor
* `logDeriv_riemannXi_divisorProductOne_eq_tsum` and
  `logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` : xi-specialized zero-sum identities
* `riemannXi_hadamard_polynomial_derivative_eval_zero_eq` and
  `existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero` : theorem-level uniqueness
  of the xi Hadamard derivative constant
* `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` : logarithmic derivative formula
  obtained from the xi no-monomial factorization
* `completedRiemannZeta₀_hadamard_factorization_reindex`, `_sequence` : reindexed enumerations

The order-one estimate from `ZetaFiniteOrder` is the finite-order input to
`hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function background
* [boas1954] and [levin1980] for the general finite-order Hadamard product theorem
* [kadiri2005] for the explicit zero-free-region use of the xi logarithmic derivative

## Tags

Riemann zeta function, Hadamard factorization, canonical product, entire function of finite order
-/

@[expose] public section

noncomputable section

open Complex Set

open scoped BigOperators

/-- The completed zeta function `Λ₀` has order at most one. -/
theorem completedRiemannZeta₀_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) completedRiemannZeta₀ := by
  refine ⟨differentiable_completedZeta₀, ?_⟩
  intro ε hε
  simpa [add_comm, add_left_comm, add_assoc] using
    (Complex.completedRiemannZeta₀_order_one ε hε)

/-- The Riemann xi function `ξ` has order at most one. -/
theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi := by
  apply Complex.Hadamard.EntireOfOrderAtMost.of_orderLE (by norm_num) differentiable_riemannXi
  have hp := ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial ℂ).orderLE_eval).mono
    (show (0 : ℝ) ≤ 1 by norm_num)
  have hΛ := completedRiemannZeta₀_entireOfOrderAtMost_one.orderLE (by norm_num)
  have hxi := ((hp.mul hΛ).add (TauCeti.orderLE_const 1 1)).const_mul (1 / 2)
  convert hxi using 1
  funext z
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
    riemannXi]
  ring

/-! ### Logarithmic-derivative identities -/

/-- The genus-one summability condition for the nonzero zero divisor of Riemann's entire `ξ`.

This is the zero-counting input needed for the xi canonical product and its logarithmic derivative,
specialized from the finite-order Hadamard summability theorem. -/
theorem summable_riemannXi_divisorZeroIndex₀_norm_inv_sq :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  simpa using
    (Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
      (ρ := (1 : ℝ)) (f := riemannXi) riemannXi_entireOfOrderAtMost_one
      (by norm_num))

private theorem riemannXi_product_eq :
    Complex.Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ =
      TauCeti.divisorProductOne riemannXi := by
  ext z
  exact Complex.Hadamard.divisorCanonicalProduct_one_eq_native
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq z

/-- Since `ξ(0) = 1 / 2`, the monomial exponent in the origin-centered Hadamard product is zero. -/
theorem analyticOrderNatAt_riemannXi_zero : analyticOrderNatAt riemannXi 0 = 0 := by
  by_contra h
  have hzero : riemannXi 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := riemannXi) (z₀ := 0) h
  rw [riemannXi_zero] at hzero
  norm_num at hzero

/-- Since `Λ₀(0) ≠ 0`, the monomial exponent in the origin-centered Hadamard product for Λ₀ is
zero. -/
theorem analyticOrderNatAt_completedRiemannZeta₀_zero :
    analyticOrderNatAt completedRiemannZeta₀ 0 = 0 := by
  by_contra h
  have hzero : completedRiemannZeta₀ 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := completedRiemannZeta₀) (z₀ := 0) h
  exact completedRiemannZeta₀_zero_ne_zero hzero

/-- The logarithmic-derivative zero terms for Riemann's `ξ` are summable away from the zero set.

This follows from the general far-zero comparison and the order-one zero summability of `ξ`. -/
theorem summable_riemannXi_logDerivTerms_divisorZeroIndex₀
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz

/-- The zero-sum formula for the logarithmic derivative of the genus-one divisor canonical product
attached to Riemann's entire `ξ`. -/
theorem logDeriv_riemannXi_divisorProductOne_eq_tsum
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (TauCeti.divisorProductOne riemannXi) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  by simpa only [← riemannXi_product_eq] using
    Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum
      summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz

/-- Logarithmic derivative identity for a chosen `ξ` Hadamard factorization.

The divisor-product differentiability is supplied by
`Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ`, and xi zero summability is
supplied by `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq`.  The remaining hypotheses are the
point-not-a-zero assumptions needed for the logarithmic derivative and zero-sum terms; the product
nonvanishing is derived from the generic divisor-product nonvanishing theorem. -/
theorem logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    {P : Polynomial ℂ} {z : ℂ}
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        TauCeti.divisorProductOne riemannXi w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv riemannXi z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : ℂ → ℂ :=
    TauCeti.divisorProductOne riemannXi
  have hfun : riemannXi = fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa [G] using hfac w
  have hdiff_exp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).differentiableAt
  have hprod_ne :
      TauCeti.divisorProductOne riemannXi z ≠ 0 :=
    by simpa only [← riemannXi_product_eq] using
      Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne
        1 riemannXi summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz
  calc
    logDeriv riemannXi z =
        logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w) z := by
          rw [hfun]
    _ = logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z + logDeriv G z := by
          exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa [G] using hprod_ne)
            hdiff_exp
            (by
              simpa only [G] using
                (TauCeti.differentiable_divisorProductOne
                  (Complex.Hadamard.summable_native_divisor_inv_sq
                    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq)).differentiableAt)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
          rw [Polynomial.logDeriv_exp_eval]
          rw [show logDeriv G z =
              ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
                (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
                  1 / Complex.Hadamard.divisorZeroIndex₀_val p) from
            by
              simpa [G] using
                logDeriv_riemannXi_divisorProductOne_eq_tsum
                  hz]

/-- Any two xi Hadamard polynomials with the same divisor-canonical product have the same
derivative at every point away from the nonzero divisor-indexed zero set. -/
theorem riemannXi_hadamard_polynomial_derivative_eval_eq
    {P Q : Polynomial ℂ} {z : ℂ} (hPfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w P) *
        TauCeti.divisorProductOne riemannXi w)
    (hQfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w Q) *
        TauCeti.divisorProductOne riemannXi w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Polynomial.eval z P.derivative = Polynomial.eval z Q.derivative := by
  let S : ℂ := ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
    (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
      1 / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hP :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := z) hPfac hz
  have hQ :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := Q) (z := z) hQfac hz
  have hsum : Polynomial.eval z P.derivative + S = Polynomial.eval z Q.derivative + S := by
    rw [← hP, ← hQ]
  exact add_right_cancel hsum

/-- The xi Hadamard derivative constant `Polynomial.eval 0 P.derivative` is independent of the
Hadamard polynomial realizing the no-monomial xi factorization. -/
theorem riemannXi_hadamard_polynomial_derivative_eval_zero_eq
    {P Q : Polynomial ℂ} (hPfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        TauCeti.divisorProductOne riemannXi w)
    (hQfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w Q) *
      TauCeti.divisorProductOne riemannXi w) :
    Polynomial.eval 0 P.derivative = Polynomial.eval 0 Q.derivative := by
  refine riemannXi_hadamard_polynomial_derivative_eval_eq
    (P := P) (Q := Q) (z := 0) hPfac hQfac ?_
  intro p
  exact (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm

/-- **Hadamard factorization for Riemann's entire `ξ` at genus one. -/
theorem riemannXi_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      TauCeti.divisorProductOne riemannXi z := by
  simpa [riemannXi_product_eq] using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one)

/-- Hadamard factorization for `ξ` with the origin monomial removed using `ξ(0) ≠ 0`. -/
theorem riemannXi_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      TauCeti.divisorProductOne riemannXi z := by
  rcases riemannXi_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

/-- There is a unique complex number obtained as `Polynomial.eval 0 P.derivative` from a
degree-one no-monomial Hadamard factorization of Riemann's xi function. This is the canonical
theorem-level formulation of Kadiri's Hadamard constant, without choosing a global witness. -/
theorem existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero :
    ∃! B : ℂ, ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          TauCeti.divisorProductOne riemannXi z) ∧
      B = Polynomial.eval 0 P.derivative := by
  rcases riemannXi_hadamard_factorization_no_monomial with ⟨P, hdeg, hfac⟩
  refine ⟨Polynomial.eval 0 P.derivative, ⟨P, hdeg, hfac, rfl⟩, ?_⟩
  intro B hB
  rcases hB with ⟨Q, _hQdeg, hQfac, rfl⟩
  exact (riemannXi_hadamard_polynomial_derivative_eval_zero_eq
    (P := P) (Q := Q) hfac hQfac).symm

/-- A logarithmic derivative identity for `ξ`, obtained from the no-monomial Hadamard
factorization.

The theorem is phrased existentially in the Hadamard polynomial `P`, and keeps the origin monomial,
product differentiability, product nonvanishing, and zero-term summability hypotheses internal to
the proof. -/
theorem exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    {z : ℂ} (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :  ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧
      logDeriv riemannXi z = Polynomial.eval z P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rcases riemannXi_hadamard_factorization_no_monomial with ⟨P, hdeg, hfac⟩
  exact ⟨P, hdeg, logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hz⟩

/-- Reindexed divisor Hadamard factorization for Riemann's entire `ξ`. -/
theorem riemannXi_hadamard_factorization_reindex
    {ι : Type*} (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      (∏' i : ι, Complex.weierstrassFactorOne
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa [Complex.weierstrassFactor_one] using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

/-- Reindexed divisor Hadamard factorization for `ξ`, with the origin monomial removed. -/
theorem riemannXi_hadamard_factorization_reindex_no_monomial
    {ι : Type*} (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactorOne
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases riemannXi_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

/-- Sequence-indexed Hadamard factorization for Riemann's entire `ξ`. -/
theorem riemannXi_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

/-- Sequence-indexed Hadamard factorization for `ξ`, with the origin monomial removed. -/
theorem riemannXi_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases riemannXi_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

private theorem completedRiemannZeta₀_product_eq :
    Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ Set.univ =
      TauCeti.divisorProductOne completedRiemannZeta₀ := by
  have hs : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ Set.univ ↦
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2) := by
    simpa using
      (Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
        (ρ := (1 : ℝ)) (f := completedRiemannZeta₀) completedRiemannZeta₀_entireOfOrderAtMost_one
        (by norm_num))
  ext z
  exact Complex.Hadamard.divisorCanonicalProduct_one_eq_native hs z

/-- **Hadamard factorization for `completedRiemannZeta₀` (Λ₀) at genus one**. -/
theorem completedRiemannZeta₀_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      TauCeti.divisorProductOne completedRiemannZeta₀ z := by
  simpa [completedRiemannZeta₀_product_eq] using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one)

/-- Hadamard factorization for `completedRiemannZeta₀` (Λ₀), with the origin monomial removed
using `Λ₀(0) ≠ 0`. -/
theorem completedRiemannZeta₀_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      TauCeti.divisorProductOne completedRiemannZeta₀ z := by
  rcases completedRiemannZeta₀_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

/-- Reindexed divisor Hadamard factorization for Λ₀. -/
theorem completedRiemannZeta₀_hadamard_factorization_reindex
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      (∏' i : ι, Complex.weierstrassFactorOne
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa [Complex.weierstrassFactor_one] using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

/-- Reindexed divisor Hadamard factorization for Λ₀, with the origin monomial removed. -/
theorem completedRiemannZeta₀_hadamard_factorization_reindex_no_monomial
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactorOne
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases completedRiemannZeta₀_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

/-- Sequence-indexed Hadamard factorization for Λ₀. -/
theorem completedRiemannZeta₀_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

/-- Sequence-indexed Hadamard factorization for Λ₀, with the origin monomial removed. -/
theorem completedRiemannZeta₀_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases completedRiemannZeta₀_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z
