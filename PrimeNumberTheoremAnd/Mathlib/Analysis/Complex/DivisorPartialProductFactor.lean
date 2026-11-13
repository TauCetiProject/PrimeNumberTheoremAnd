/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorComplement
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Analytic.Order


/-!
# Local factorization of finite divisor-indexed products

This file packages the finite-order computation for partial products of Weierstrass factors indexed
by `divisorZeroIndex₀`, and deduces a local factorization at a point `z₀` once the finset contains
the full fiber over `z₀`.
-/

@[expose] public section

noncomputable section

open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finite product multiplicity at a point

For a finite product of elementary factors indexed by divisor-indices, the analytic order at `z₀`
equals the number of indices whose value is exactly `z₀`.
-/

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card : ℕ∞) := by
  classical
  have heq :
      (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) =
        ∏ p ∈ s, (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
    ext z
    simp
  rw [heq, TauCeti.analyticOrderAt_prod
    (fun p _ ↦ (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀)]
  calc
    _ = ∑ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℕ∞) else 0 := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      split_ifs with hp
      · simpa only [hp] using
          (analyticOrderAt_weierstrassFactor_div_self m (divisorZeroIndex₀_val_ne_zero p))
      · have han := (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
        apply han.analyticOrderAt_eq_zero.mpr
        apply (weierstrassFactor_ne_zero_iff m _).mpr
        exact mt (div_eq_one_iff_eq (divisorZeroIndex₀_val_ne_zero p)).mp (Ne.symm hp)
    _ = _ := by simp


theorem analyticOrderNatAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderNatAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ =
      (s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card := by
  simpa [analyticOrderNatAt] using
    (congrArg ENat.toNat
      (analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀ (m := m) (f := f) (s := s)
      (z₀ := z₀)))

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀_val p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀_fiberFinset
    (f := f) z₀).card)).1 ?_
  simp [hOrder]

end Complex.Hadamard
