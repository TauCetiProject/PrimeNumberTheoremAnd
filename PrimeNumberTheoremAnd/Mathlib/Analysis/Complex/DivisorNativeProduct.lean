/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
public import TauCeti.Analysis.Complex.CanonicalProduct.Divisor

/-!
# Native divisor products

The general-genus product uses a separate index for each zero multiplicity.
For genus one, summing or multiplying over each finite multiplicity fiber gives
Tau Ceti's native divisor-support API, with multiplicity as a weight or power.
-/

public section

open Complex Filter Function Topology

namespace Complex.Hadamard

/-- Inverse-square summability with repeated indices implies native weighted summability. -/
theorem summable_native_divisor_inv_sq {f : ℂ → ℂ}
    (hsum : Summable (fun p : divisorZeroIndex₀ f Set.univ ↦
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ 2)) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
  let F : divisorZeroIndex f Set.univ → ℝ := fun p ↦ ‖p.1‖⁻¹ ^ 2
  have hs : support F ⊆ {p : divisorZeroIndex f Set.univ | p.1 ≠ 0} := by
    intro p hp hp0
    apply hp
    simp [F, hp0]
  have hfull : Summable F :=
    ((hasSum_subtype_iff_of_support_subset hs).mp hsum.hasSum).summable
  have hweights : Summable (fun z : ℂ ↦
      ((MeromorphicOn.divisor f Set.univ z).toNat : ℝ) * ‖z‖⁻¹ ^ 2) := by
    simpa [F, tsum_fintype] using hfull.sigma
  simpa only [norm_inv, Function.comp_def] using!
    hweights.subtype (fun z ↦ z ∈ (MeromorphicOn.divisor f Set.univ).support)

private theorem tprod_finite_fibers {ι : Type*} (m : ι → ℕ) (a : ι → ℂ)
    (h : Multipliable (fun p : (Σ i, Fin (m i)) ↦ a p.1)) :
    (∏' p : (Σ i, Fin (m i)), a p.1) = ∏' i, a i ^ m i := by
  calc
    (∏' p : (Σ i, Fin (m i)), a p.1) = ∏' i, ∏' _j : Fin (m i), a i :=
      Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) h
    _ = ∏' i, a i ^ m i := by
      apply tprod_congr
      intro i
      simp only [tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The general divisor product at genus one agrees with Tau Ceti's native divisor product. -/
theorem divisorCanonicalProduct_one_eq_native {f : ℂ → ℂ}
    (hsum : Summable (fun p : divisorZeroIndex₀ f Set.univ ↦
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ 2)) (z : ℂ) :
    divisorCanonicalProduct 1 f Set.univ z = TauCeti.divisorProductOne f z := by
  let F : divisorZeroIndex f Set.univ → ℂ := fun p ↦ weierstrassFactor 1 (z / p.1)
  have hs : mulSupport F ⊆ {p : divisorZeroIndex f Set.univ | p.1 ≠ 0} := by
    intro p hp hp0
    apply hp
    simp [F, hp0]
  have hprod : HasProd (fun p : divisorZeroIndex₀ f Set.univ ↦ F p.1)
      (divisorCanonicalProduct 1 f Set.univ z) := by
    exact (hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ 1 f hsum).hasProd
      (Set.mem_univ z)
  have hfull : HasProd F (divisorCanonicalProduct 1 f Set.univ z) :=
    (hasProd_subtype_iff_of_mulSupport_subset hs).mp hprod
  have hgroup := tprod_finite_fibers
    (fun w : ℂ ↦ (MeromorphicOn.divisor f Set.univ w).toNat)
    (fun w : ℂ ↦ weierstrassFactor 1 (z / w)) hfull.multipliable
  calc
    divisorCanonicalProduct 1 f Set.univ z = ∏' p, F p := hfull.tprod_eq.symm
    _ = ∏' w : ℂ, weierstrassFactor 1 (z / w) ^
        (MeromorphicOn.divisor f Set.univ w).toNat := hgroup
    _ = TauCeti.divisorProductOne f z := by
      rw [TauCeti.divisorProductOne_eq_tprod]
      apply tprod_congr
      intro w
      rw [weierstrassFactor_one, div_eq_mul_inv, mul_comm]

end Complex.Hadamard
