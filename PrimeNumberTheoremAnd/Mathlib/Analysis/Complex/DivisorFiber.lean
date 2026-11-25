/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.DivisorFactorization


/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

/-!
## The multiplicity fiber is finite
-/

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub

/-- The finite fiber over `z₀` in the divisor-index type `divisorZeroIndex₀`. -/
def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset

@[simp]
lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  simp [divisorZeroIndex₀_fiberFinset]

lemma mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
  have : divisorZeroIndex₀_val p = z₀ := by
    have hm : divisorZeroIndex₀_val p ∈
        Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
      ⟨hp, divisorZeroIndex₀_val_mem_divisor_support' p⟩
    simpa only [hball, Set.mem_singleton_iff] using hm
  exact (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).2 this

lemma mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε := by
  constructor
  · intro hp
    have : divisorZeroIndex₀_val p = z₀ :=
      (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp
    simpa [this] using (Metric.mem_ball_self hε : z₀ ∈ Metric.ball z₀ ε)
  · intro hp
    exact mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp

lemma not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ≠ z₀ := by
  simp [mem_divisorZeroIndex₀_fiberFinset]

lemma weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  have hp' : divisorZeroIndex₀_val p ≠ z₀ :=
    (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hp
  intro z hz hzero
  have heq : z = divisorZeroIndex₀_val p :=
    (div_eq_one_iff_eq (divisorZeroIndex₀_val_ne_zero p)).mp
      ((_root_.Complex.weierstrassFactor_eq_zero_iff m).mp hzero)
  have hm : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε ∩
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
    ⟨heq ▸ hz, divisorZeroIndex₀_val_mem_divisor_support' p⟩
  exact hp' (by simpa only [hball, Set.mem_singleton_iff] using hm)

end Complex.Hadamard
