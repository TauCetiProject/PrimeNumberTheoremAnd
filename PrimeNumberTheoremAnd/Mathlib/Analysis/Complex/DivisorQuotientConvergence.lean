/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorPartialProductFactor
import Mathlib.Analysis.Normed.Field.Lemmas
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp


/-!
# Quotient convergence for divisor-indexed canonical products

This file develops the convergence of quotients of finite partial products and of the
divisor-indexed canonical product by powers `(z - z₀)^k` away from `z₀`. It also proves the key
local identity on a punctured ball used later in removable-singularity arguments.
-/

@[expose] public section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using! hprod

/-!
## Quotient convergence on compacts avoiding `z₀`

If `K` is compact and avoids `z₀`, then multiplying by `((z - z₀)^k)⁻¹` preserves uniform
convergence on `K`. -/

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  have hloc :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ m f h_sum).mono (Set.subset_univ K)
  have hdenom := (TauCeti.tendstoUniformlyOn_const (fun z : ℂ ↦ (z - z₀) ^ k)
    (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))) K
  have hquot := hloc.div₀ hdenom.tendstoLocallyUniformlyOn
    ((differentiableOn_divisorCanonicalProduct_univ m f h_sum).continuousOn.mono
      (Set.subset_univ K))
    (by fun_prop) (fun z hz ↦ pow_ne_zero k (sub_ne_zero.mpr (hKz z hz)))
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hquot

/-!
## Quotient locally uniform convergence on the punctured plane `ℂ \ {z₀}`
-/

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

/-!
## Passing the fiber/complement factorization to the infinite product (punctured neighborhood)

This is the local factorization used for removability: near `z₀`, the quotient
`divisorCanonicalProduct / (z - z₀)^k` agrees (on a punctured ball) with the product of
`divisorComplementCanonicalProduct` and the analytic factor `u` coming from the fiber-only product.
-/

open Filter

theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
            (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := Filter.eventually_ge_atTop (divisorZeroIndex₀_fiberFinset f z₀)
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

/-!
## Boundedness of the quotient on a punctured ball

We only need boundedness of the analytic factor `u` near `z₀`, so `ContinuousAt` at `z₀` suffices.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  obtain ⟨ε, hε, u, huA, _, hEq⟩ :=
    exists_ball_eq_divisorCanonicalProduct_div_pow_eq m f h_sum z₀
  have hcont : ContinuousAt (fun z ↦ divisorComplementCanonicalProduct m f z₀ z * u z) z₀ :=
    ((differentiableOn_divisorComplementCanonicalProduct_univ m f z₀ h_sum).differentiableAt
      (by simp)).continuousAt.mul huA.continuousAt
  obtain ⟨C, hC⟩ := hcont.norm.isBoundedUnder_le
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_nhds_iff.mp hC
  refine ⟨min ε δ, lt_min hε hδ, C, ?_⟩
  rintro _ ⟨z, ⟨hz, hzne⟩, rfl⟩
  have hzε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball (min_le_left _ _) hz
  have hzδ : z ∈ Metric.ball z₀ δ := Metric.ball_subset_ball (min_le_right _ _) hz
  have hz_ne : z ≠ z₀ := by simpa using hzne
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply, hEq z hzε hz_ne]
    using hbound hzδ

/-!
## Nonvanishing of the complement canonical product near `z₀`

Pointwise, the complement canonical product is an infinite product of factors of the form `1 + aₚ`
with `∑ ‖aₚ‖` summable, hence the product is nonzero.
-/

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  let a : divisorZeroIndex₀ f Set.univ → ℂ :=
    fun p ↦ divisorComplementFactor m f z₀ p z₀ - 1
  have hfactor : ∀ p : divisorZeroIndex₀ f Set.univ,
      divisorComplementFactor m f z₀ p z₀ ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀_val p = z₀
    · simp [hp]
    · simpa only [divisorComplementFactor_def, ite_eq_right hp] using
        (weierstrassFactor_div_ne_zero_iff (m := m)
          (divisorZeroIndex₀_val_ne_zero p)).mpr (Ne.symm hp)
  have hs : Summable (fun p : divisorZeroIndex₀ f Set.univ ↦
      ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1)) := by
    simpa only [div_eq_mul_inv, norm_mul, norm_inv, mul_pow] using h_sum.mul_left (‖z₀‖ ^ (m + 1))
  have hnorm : Summable (fun p ↦ ‖a p‖) := by
    apply (hs.mul_left 4).of_norm_bounded_eventually
    filter_upwards [hs.tendsto_cofinite_zero.eventually_le_const
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (m + 1))] with p hp
    rw [Real.norm_eq_abs, abs_norm]
    by_cases hval : divisorZeroIndex₀_val p = z₀
    · simp only [a, divisorComplementFactor_def, ite_eq_left hval, sub_self, norm_zero]
      positivity
    · dsimp only [a]
      rw [divisorComplementFactor_def, ite_eq_right hval]
      exact weierstrassFactor_sub_one_pow_bound
        ((pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by omega : m + 1 ≠ 0)).mp hp)
  have hprod := tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a)
    (fun p ↦ by simpa only [a, ← add_sub_assoc, add_sub_cancel_left] using hfactor p) hnorm
  simpa only [a, ← add_sub_assoc, add_sub_cancel_left, divisorComplementCanonicalProduct]
    using hprod

theorem exists_ball_divisorComplementCanonicalProduct_ne_zero
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, divisorComplementCanonicalProduct m f z₀ z ≠ 0 := by
  have hdiff :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hdiffAt : DifferentiableAt ℂ (divisorComplementCanonicalProduct m f z₀) z₀ := by
    exact (hdiff z₀ (by simp)).differentiableAt (by simp)
  have hcont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    hdiffAt.continuousAt
  have h0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
    divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
  have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isClosed_singleton.isOpen_compl
  have hmem : divisorComplementCanonicalProduct m f z₀ z₀ ∈ (({0} : Set ℂ)ᶜ) := by
    simp [h0]
  rcases (Metric.mem_nhds_iff.1 (hcont (hopen.mem_nhds hmem))) with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have : divisorComplementCanonicalProduct m f z₀ z ∈ ({0} : Set ℂ)ᶜ := hr hz
  simpa using this

/-!
## Eventually: partial products factor at `z₀` with the fiber multiplicity

Along `atTop`, sufficiently large partial products contain the fiber, hence each such partial
product is locally divisible by `(z - z₀)^k`, where `k` is the fiber cardinality.
-/

theorem eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧ (fun z : ℂ => divisorPartialProduct m f s z)
        =ᶠ[𝓝 z₀] fun z : ℂ =>
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  refine (Filter.eventually_ge_atTop (divisorZeroIndex₀_fiberFinset f z₀)).mono ?_
  intro s hs
  rcases
      exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
        (m := m) (f := f) (z₀ := z₀) (s := s) hs with
    ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, hg0, ?_⟩
  simpa [divisorPartialProduct] using hEq

/-!
## On `𝓝[≠] z₀`, large partial product quotients agree with an analytic function

This is the punctured-neighborhood version of
`eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct`,
obtained by dividing the factorization by `(z - z₀)^k` away from `z₀`.
-/

theorem eventually_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ (fun z : ℂ => (divisorPartialProduct m f s z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
            =ᶠ[𝓝[≠] z₀] g := by
  refine (eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct (m := m)
    (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, ?_⟩
  have hEq' : (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝[≠] z₀]
        fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z :=
    hEq.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] z₀, z ≠ z₀ := by
    simpa [Filter.Eventually] using! (self_mem_nhdsWithin : {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀)
  filter_upwards [hEq', hne] with z hz hzne
  have hz0 : (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hzne)
  have : (divisorPartialProduct m f s z) / (z - z₀) ^ (divisorZeroIndex₀_fiberFinset
      (f := f) z₀).card = g z := by
    rw [hz]
    simpa [smul_eq_mul] using (mul_div_cancel_left₀ (g z) hz0)
  simpa [divisorPartialProduct] using this

theorem eventually_exists_ball_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ ε > 0, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ → (divisorPartialProduct m f s z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
            = g z := by
  refine (eventually_eq_punctured_quotient_of_factorization (m := m) (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hEq⟩
  rcases (Metric.nhdsWithin_basis_ball (x := z₀) (s := {z : ℂ | z ≠ z₀})).mem_iff.1 hEq with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, g, hg, ?_⟩
  intro z hz hz0
  have hz' : z ∈ Metric.ball z₀ ε ∩ {z : ℂ | z ≠ z₀} := ⟨hz, hz0⟩
  exact hball hz'

end Complex.Hadamard
