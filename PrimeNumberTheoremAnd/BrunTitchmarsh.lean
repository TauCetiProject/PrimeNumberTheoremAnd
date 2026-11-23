/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Primorial
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds
import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.NumberTheory.SelbergSieve.Bounds
import TauCeti.NumberTheory.SelbergSieve.CoprimeDiagonal
import TauCeti.Data.Nat.Interval

open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

@[expose] public noncomputable section
namespace BrunTitchmarsh

/-- Sifting primes ≤ z from the interval [x, x+y] -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := squarefree_primorial _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply Sieve.siftedSum_eq
  · exact fun _ _ ↦ rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter Nat.Prime ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Finset.mem_union, and_imp]
  intro hx hxy hp
  by_cases hpz : p ≤ z
  · right
    rw [Nat.le_floor_iff (by linarith)]
    have := hp.ne_zero
    exact ⟨by omega, hpz⟩
  · refine Or.inl ⟨⟨hx, hxy⟩, fun q hq hqz ↦ ?_⟩
    rw [hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤
      siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) + z := by
  classical
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z))).card
  · rw [primesBetween]
    exact_mod_cast Finset.card_le_card (primesBetween_subset _ _ _)
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card +
      ↑(Finset.Icc 1 (Nat.floor z)).card
  · exact_mod_cast Finset.card_union_le _ _
  rw [siftedSum_eq_card]
  gcongr
  rw [Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

include hx in
theorem multSum_eq (d : ℕ) (_hd : d ≠ 0) :
    multSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold multSum
  rw [primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hx)]
  · rw [Nat.Ioc_filter_dvd_card]

include hx in
theorem rem_eq (d : ℕ) (hd : d ≠ 0) :
    rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold rem
  rw [multSum_eq x y z hx hz d hd]
  simp [primeInterSieve, ite_eq_right hd]

include hx hy in
theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) :
    |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| ≤ 5 := by
  have hG : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = ⌈x⌉₊ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_ceil_iff.2 hx), Nat.cast_one]
  have hc := Nat.ceil_lt_add_one hx.le
  rw [rem_eq _ _ _ hx hz _ hd, Nat.cast_sub (Nat.div_le_div_right
    (Nat.le_floor (by rw [hG]; linarith [Nat.le_ceil x])))]
  have h1 := Nat.floor_le (show 0 ≤ (x + y) / d by positivity)
  have h2 := Nat.lt_floor_add_one ((x + y) / d)
  have h3 := Nat.floor_le (show 0 ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) / d by positivity)
  have h4 := Nat.lt_floor_add_one (((⌈x⌉₊ - 1 : ℕ) : ℝ) / d)
  rw [Nat.floor_div_natCast] at h1 h2
  rw [Nat.floor_div_eq_div, hG] at h3 h4
  have h5 : 0 ≤ (x - ⌈x⌉₊ + 1) / d := div_nonneg (by linarith) (by positivity)
  have h6 : (x - ⌈x⌉₊ + 1) / d ≤ 1 := div_le_one_of_le₀ (by
    linarith [Nat.le_ceil x, (Nat.one_le_cast (α := ℝ)).2 (Nat.pos_of_ne_zero hd)]) (by positivity)
  have h7 : (x + y) / d - (⌈x⌉₊ - 1) / d - (d : ℝ)⁻¹ * y = (x - ⌈x⌉₊ + 1) / d := by ring
  rw [abs_le]
  constructor <;> linarith

end Remainder

theorem boudingSum_ge :
    (primeInterSieve x y z hz).toBoundingSieve.truncatedSelbergSum (Real.sqrt z) ≥
      Real.log z / 2 := by
  have hsqrt : Real.sqrt z ≤ z := Real.sqrt_le_self_iff.mpr (Or.inr hz)
  have h := BoundingSieve.log_le_sum_selbergTerms
    (primeInterSieve x y z hz).toBoundingSieve (Real.sqrt z) (Real.sqrt_nonneg z)
    (by
      intro p hp hpz
      exact hp.dvd_primorial_iff.mpr (Nat.le_floor (hpz.le.trans hsqrt)))
    (by
      intro p hp _
      simp only [primeInterSieve, ArithmeticFunction.pdiv_apply,
        ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hp.ne_zero,
        ArithmeticFunction.id_apply, Nat.cast_one, one_div, le_refl])
  rw [Real.log_sqrt (zero_le_one.trans hz)] at h
  rwa [ge_iff_le, BoundingSieve.truncatedSelbergSum_def]

include hx hy in
theorem primeSieve_rem_sum_le :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d *
          |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  refine rem_sum_le_of_const (primeInterSieve x y z hz) 5 (fun d hd ↦ ?_)
  apply abs_rem_le _ _ _ <;> linarith

include hx hy in
theorem siftedSum_le (hz : 1 < z) :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z (le_of_lt hz)))
      ≤ 2 * y / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1 + Real.log z) ^ 3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · exact boudingSum_ge _ _ _ _
  · exact primeSieve_rem_sum_le x y z hx hy _

include hx hy in
theorem primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 := by
  have : z ≤ z * (1 + Real.log z) ^ 3 := by
    apply le_mul_of_one_le_right
    · linarith
    · apply one_le_pow₀
      linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le _ _ _ hx hy hz, primesBetween_le_siftedSum_add x y z hz.le]

theorem primesBetween_one (n : ℕ) :
    primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  rw [primesBetween]
  congr 1
  ext p
  simp only [Nat.ceil_one, Nat.floor_natCast, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ by omega,
    fun h ↦ ⟨by have := hp.pos; omega, by omega⟩⟩

theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) :
    primesBetween a b ≤ primesBetween a c := by
  dsimp only [primesBetween]
  refine Finset.card_le_card fun p ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, and_imp]
  exact fun ha hb hp ↦ ⟨⟨ha, hb.trans (Nat.floor_mono hbc)⟩, hp⟩

theorem tmp (N : ℕ) :
    ((Finset.range N).filter Nat.Prime).card ≤
      4 * (N / Real.log N) + 6 * (N ^ (1/2 : ℝ) * (1 + 1/2 * Real.log N) ^ 3) := by
  trans ↑((Finset.range (N+1)).filter Nat.Prime).card
  · norm_cast
    refine Finset.card_le_card fun n ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range, and_imp]
    exact fun hnN hp ↦ ⟨by omega, hp⟩
  rw [← primesBetween_one]
  by_cases hN : N = 0
  · simp [hN, primesBetween]
  by_cases hN : N = 1
  · simp (config := {decide:=true}) [hN, primesBetween]
  have h : primesBetween 1 (1 + N) ≤
      2 * (N / Real.log (N ^ (1/2 : ℝ))) +
        6 * (N ^ (1 / 2 : ℝ) * (1 + Real.log (N ^ (1/2 : ℝ))) ^ 3) := by
    convert (primesBetween_le 1 N (N ^ (1/2 : ℝ)) (by norm_num) (by norm_cast; omega)
      (Real.one_lt_rpow (by norm_cast; omega) (by norm_num))) using 1
    ring
  calc
    _ ≤ (primesBetween 1 (1+N):ℝ) := by
      norm_cast
      apply primesBetween_mono_right
      norm_cast
      omega
    _ ≤ _ := by
      rw [Real.log_rpow (by norm_num; omega)] at h
      convert h using 2
      ring

theorem rpow_mul_rpow_log_isBigO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    (fun x ↦ (x : ℝ) ^ (r : ℝ) * (Real.log x) ^ k) =O[atTop]
      (fun x ↦ x / Real.log x) := by
  refine ((isLittleO_log_rpow_rpow_atTop (k + 1) (sub_pos.2 hr)).isBigO.mul
    (isBigO_refl (fun x ↦ x ^ r / Real.log x) atTop)).congr' ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 1] with x hx
  · rw [Real.rpow_add_one (Real.log_pos hx).ne']
    field_simp [(Real.log_pos hx).ne']
  · rw [mul_div_assoc', ← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]

theorem err_isBigO :
    (fun x ↦ (x ^ (1 / 2 : ℝ) * (1 + 1 / 2 * Real.log x) ^ 3)) =O[atTop]
      fun x ↦ (x / Real.log x) := by
  calc
    _ =O[atTop] (fun x ↦ x ^ (1/2:ℝ) * (Real.log x) ^ 3) := by
      apply IsBigO.mul (isBigO_refl ..)
        (Real.isLittleO_const_log_atTop.isBigO.add
          ((isBigO_refl ..).const_mul_left ..) |>.pow _)
    _ =O[atTop] _ := by
      convert rpow_mul_rpow_log_isBigO_id_div_log 3 (?_) <;> norm_num

theorem prime_or_pow (N n : ℕ) (hnN : n < N) (hnprime : IsPrimePow n) :
    Nat.Prime n ∨ (∃ (m : ℕ), m < Real.sqrt N ∧ ∃ k ≤ Nat.log 2 N, n = m ^ k) := by
  rw [isPrimePow_nat_iff_bounded n] at hnprime
  obtain ⟨p, -, k, -, hp, hk_pos, hpkn⟩ := hnprime
  by_cases hk : k = 1
  · left
    rw [← hpkn, hk, pow_one]
    exact hp
  right
  refine ⟨p, ?_, k, ?_, ?_⟩
  · rw [Real.lt_sqrt]
    · norm_cast
      calc
        p ^ 2 ≤ p ^ k := by gcongr <;> [exact hp.one_le; omega]
      _ = n := hpkn
      _ < N := hnN
    · positivity
  · calc
      _ ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt hpkn.le
      _ ≤ Nat.log 2 n := Nat.log_anti_left (by norm_num) hp.two_le
      _ ≤ Nat.log 2 N := Nat.log_mono_right hnN.le
  · exact_mod_cast hpkn.symm

theorem range_filter_isPrimePow_subset_union (N : ℕ) :
    ((Finset.range N).filter IsPrimePow) ⊆ (Finset.range N).filter Nat.Prime ∪
      ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
        (fun p ↦ p.1 ^ p.2) := by
  intro n
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, Prod.exists, and_imp]
  intro hnN hnprime
  rcases prime_or_pow N n hnN hnprime with hp | ⟨m, hm, k, hk, h⟩
  · left
    exact ⟨hnN, hp⟩
  · right
    refine ⟨m, k, ?_⟩
    by_cases hm : m = 0
    · rw [hm, zero_pow] at h
      · exact False.elim (hnprime.ne_zero h)
      · rintro rfl
        simp only [pow_zero] at h
        exact False.elim (hnprime.ne_one h)
    rw [Nat.lt_ceil, Nat.lt_succ_iff]
    have : 1 ≤ m := by omega
    aesop

theorem pows_small_primes_le (N : ℕ) :
    (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
      (fun p ↦ p.1 ^ p.2)).card ≤
        (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2) := calc
  _ ≤ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
      Finset.range (Nat.log 2 N + 1)).card : ℝ) := by
    norm_cast
    exact Finset.card_image_le
  _ ≤ _ := by
    simp only [Finset.card_product, Nat.card_Ico, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    by_cases hN : N = 0
    · simp [hN]
    have : 1 ≤ Nat.ceil (Real.sqrt N) := by
      simp only [Nat.one_le_ceil_iff, Real.sqrt_pos, Nat.cast_pos]
      omega
    gcongr ?_ * ?_
    · rw [← Real.sqrt_eq_rpow, Nat.cast_sub this, Nat.cast_one]
      have := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt N by positivity)
      linarith
    rw [← Real.natFloor_logb_natCast, Real.log_div_log, Nat.cast_two, add_comm,
      add_le_add_iff_left]
    apply Nat.floor_le
    apply Real.logb_nonneg one_lt_two
    norm_cast; omega

theorem one_add_log_div_log_two_isBigO :
    (fun N ↦ (1 + Real.log N / Real.log 2)) =O[atTop] (fun N ↦ Real.log N) := by
  refine IsBigO.add ?h₁ ?h₂
  · convert Real.isLittleO_const_log_atTop.isBigO
  simp_rw [div_eq_inv_mul]
  apply IsBigO.const_mul_left (isBigO_refl _ _)

theorem pow_half_mul_one_add_log_div_isBigO :
    (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[Filter.atTop]
      (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[atTop]
      (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * Real.log N) := by
    apply IsBigO.mul
    · apply isBigO_refl
    apply one_add_log_div_log_two_isBigO
  _ =O[atTop] (fun N ↦ (N : ℝ)/(Real.log N)) := by
    convert rpow_mul_rpow_log_isBigO_id_div_log 1 (show 1/2 < (1:ℝ) by norm_num) using 1
    simp

theorem card_pows_aux :
    (fun N ↦ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
      Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℕ → ℝ) =O[atTop]
        fun N ↦ N / Real.log N := by
  apply IsBigO.trans ?_ (pow_half_mul_one_add_log_div_isBigO.comp_tendsto tendsto_natCast_atTop_atTop)
  dsimp only [Function.comp_def]
  apply isBigO_of_le
  intro N
  simp only [RCLike.norm_natCast, one_div, norm_mul, Real.norm_eq_abs]
  rw [Real.abs_rpow_of_nonneg (by positivity), Nat.abs_cast, abs_of_nonneg]
  · convert pows_small_primes_le N using 3
    norm_num
  by_cases hN : N = 0
  · simp [hN]
  rw [Real.log_div_log]
  linarith [Real.logb_nonneg (show 1 < (2:ℝ) by norm_num)
    (show (1 : ℝ) ≤ N by norm_num; omega)]

theorem card_isPrimePow_isBigO :
    (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop]
      (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop]
      (fun N ↦ (((Finset.range N).filter Nat.Prime ∪
        ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
          Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card:ℝ)) := by
    apply isBigO_of_le
    simp only [RCLike.norm_natCast, Nat.cast_le]
    exact fun N ↦ Finset.card_le_card (range_filter_isPrimePow_subset_union _)
  _ =O[atTop] fun N ↦ (((Finset.range N).filter Nat.Prime).card +
      (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
        Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℝ) := by
    apply isBigO_of_le
    simp only [RCLike.norm_natCast, Real.norm_eq_abs]
    intro N
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Finset.card_union_le _ _
  _ =O[atTop] fun N ↦ N / Real.log N := by
    refine IsBigO.add (IsBigO.trans (isBigO_of_le _ fun N ↦ ?_)
      (Nat.isEquivalent_primeCounting.isBigO.comp_tendsto tendsto_natCast_atTop_atTop))
      card_pows_aux
    simp only [Function.comp_apply, Nat.floor_natCast, RCLike.norm_natCast, Nat.cast_le,
      ← Nat.count_eq_card_filter_range]
    exact Nat.count_monotone _ N.le_succ

theorem card_range_filter_isPrimePow_le :
    ∃ C, ∀ N, ((Finset.range N).filter IsPrimePow).card ≤ C * (N / Real.log N) := by
  convert_to (fun N ↦ ((Finset.range N).filter IsPrimePow).card : ℕ → ℝ) =O[⊤]
      (fun N ↦ (N / Real.log N))
  · simp only [isBigO_top, RCLike.norm_natCast, norm_div, Real.norm_eq_abs]
    congr! 3 with C N
    by_cases hN : N = 0
    · simp [hN]
    rw [abs_of_nonneg]
    apply Real.log_nonneg
    norm_cast; omega
  apply card_isPrimePow_isBigO.nat_of_atTop
  apply Filter.Eventually.of_forall
  have (a : ℕ) : (a : ℝ) ≠ -1 := by linarith [show 0 ≤ (a : ℝ) by positivity]
  simp [this, not_isPrimePow_zero]

end BrunTitchmarsh
