/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
/-!
# Prime sifting counts and explicit remainder estimates

This file identifies the prime-sifted finite set and proves the explicit
`C * level * (1 + log level)^3` remainder estimate. Finite Euler products and normalizer
lower bounds are supplied by the merged Tau Ceti Selberg-sieve API.
-/


open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

@[expose] public noncomputable section
namespace Sieve

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [hpp.dvd_primorial_iff]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [hp.dvd_primorial_iff]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1



open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  have hy := s.one_le_level
  calc ∑ d ∈ Finset.filter (fun d : ℕ => (d : ℝ) ≤ s.level) s.prodPrimes.divisors, (3 : ℝ) ^ ω d
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊s.level⌋₊, (3 : ℝ) ^ ω n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd ↦ ?_) fun _ _ _ ↦ by positivity
        obtain ⟨hd, hdy⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_floor hdy⟩
    _ ≤ s.level * (1 + Real.log s.level) ^ 2 :=
      sum_Ioc_three_pow_cardDistinctFactors_le_mul_one_add_log_sq hy
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [Real.log_nonneg hy]) (by norm_num : 2 ≤ 3)) (by linarith)

end Sieve
end
