/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientConvergence
public import Mathlib.Analysis.Complex.RemovableSingularity


/-!
# Removable singularities and multiplicities for divisor-indexed canonical products

Building on quotient convergence and boundedness on punctured balls, this file proves removable
singularity results and identifies the exact zero multiplicity of `divisorCanonicalProduct`.
-/

@[expose] public section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Differentiability of the quotient on `ℂ \ {z₀}`

The quotient of the infinite product by `(z - z₀)^k` is holomorphic on the punctured plane.
-/

theorem differentiableOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hdiff_prod : DifferentiableOn ℂ (divisorPartialProduct m f s) (Set.univ : Set ℂ) := by
    exact (differentiable_divisorPartialProduct m f s).differentiableOn
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using! (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv

theorem differentiableOn_divisorCanonicalProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact differentiableOn_divisorPartialProduct_div_pow_sub (m := m) (f := f) (z₀ := z₀) (k := k) s

/-!
## Removable singularity for the quotient at `z₀`

Using punctured-ball boundedness and punctured differentiability, we obtain a holomorphic extension
of the quotient at `z₀` via `Mathlib.Analysis.Complex.RemovableSingularity`.
-/

theorem differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
          (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
          (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  rcases bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      differentiableOn_divisorCanonicalProduct_div_pow_sub
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb : BddAbove (norm ∘ (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
    ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)

theorem analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
        (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
      z₀ := by
  obtain ⟨r, hr, hdiff⟩ := differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    m f h_sum z₀
  exact hdiff.analyticOnNhd Metric.isOpen_ball z₀ (Metric.mem_ball_self hr)

/-- A removable analytic quotient for
`divisorCanonicalProduct m f univ z / (z - z₀)^k`, where `k` is the divisor fiber cardinality at
`z₀`. -/
theorem exists_analyticAt_divisorCanonicalProduct_quotient
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]

/-!
## Exact multiplicity of the divisor canonical product

At each `z₀`, the zero multiplicity of `divisorCanonicalProduct` equals the fiber cardinality
`card (divisorZeroIndex₀_fiberFinset z₀)`.
-/

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  let k : ℕ := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
  obtain ⟨ε, hε, u, huA, hu0, hEq⟩ :=
    exists_ball_eq_divisorCanonicalProduct_div_pow_eq m f h_sum z₀
  let g : ℂ → ℂ := fun z ↦ divisorComplementCanonicalProduct m f z₀ z * u z
  have han : AnalyticAt ℂ F z₀ :=
    (differentiableOn_divisorCanonicalProduct_univ m f h_sum).analyticOnNhd isOpen_univ z₀ trivial
  have hcomp : AnalyticAt ℂ (divisorComplementCanonicalProduct m f z₀) z₀ :=
    (differentiableOn_divisorComplementCanonicalProduct_univ m f z₀ h_sum).analyticOnNhd
      isOpen_univ z₀ trivial
  have hg : AnalyticAt ℂ g z₀ := hcomp.mul huA
  have hg0 : g z₀ ≠ 0 :=
    mul_ne_zero (divisorComplementCanonicalProduct_ne_zero_at m f z₀ h_sum) hu0
  have hfacNE : F =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ k • g z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε),
      self_mem_nhdsWithin] with z hz hz0
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
    have h := (div_eq_iff hzpow).mp (hEq z hz hz0)
    simpa only [F, k, g, smul_eq_mul, mul_comm] using h
  have hfac : F =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ k • g z :=
    (han.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (((continuousAt_id.sub (continuousAt_const (y := z₀))).pow k).smul hg.continuousAt)).1 hfacNE
  have horder := (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨g, hg, hg0, hfac⟩
  simp only [F, k, analyticOrderNatAt, horder, ENat.toNat_natCast]

/-!
## Canonical product has the same analytic order as `f` away from the origin

Away from `0`, the analytic order of the divisor-indexed canonical product agrees with that of `f`
(for differentiable `f`), assuming the standard summability hypothesis.
-/

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      analyticOrderNatAt f z₀ := by
  have hcp :
      analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
        (divisorZeroIndex₀_fiberFinset (f := f) z₀).card :=
    analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
  have hfib :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ :=
    divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := z₀) hz₀
  simpa [hfib] using hcp

end Complex.Hadamard
