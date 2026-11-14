/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Dyadic estimates from logarithms

This file records elementary estimates for dyadic radii selected by `⌊logb 2 x⌋₊`.
The estimates are used to decompose growth bounds into summable geometric shells.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Filter

namespace Real

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `r₀ * 2^k` is a lower dyadic bound for `x`. -/
lemma dyadicShell_lower_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := Real.pow_natFloor_logb_le_self (b := (2 : ℝ)) (by norm_num) hx1
    simpa only [← Real.rpow_natCast, hk, Nat.cast_add, Nat.cast_one] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `x` is bounded by the next dyadic endpoint. -/
lemma dyadicShell_upper_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.lt_pow_natFloor_logb_add_one (b := (2 : ℝ)) (by norm_num)
      (zero_lt_one.trans_le hx1)
    simpa only [← Real.rpow_natCast, hk, Nat.cast_add, Nat.cast_one] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)

/-- Some dyadic scale is beyond any prescribed real bound. -/
lemma exists_nat_le_two_pow (A : ℝ) :
    ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)

/-- Once the dyadic scale is past `r₀⁻¹`, the upper endpoint `r₀ 2^(k+1)` is at least `1`. -/
lemma one_le_dyadicRadius_succ_of_inv_le_two_pow
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have h := (div_le_iff₀ hr0).mp (hk0 (kk + 1) hkk)
  simpa only [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- A dyadic radius `r₀ 2^(k+1)` gives polynomial growth bounded by a geometric term. -/
lemma one_add_abs_two_mul_dyadicRadius_rpow_le {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hbase : 1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))| ≤
      (1 + 4 * r0) * (2 : ℝ) ^ k := by
    rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast,
      abs_of_nonneg (by positivity)]
    nlinarith only [hpow]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ ≤
        ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ ρ :=
      Real.rpow_le_rpow (by positivity) hbase hρ
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) ρ k]

/-- A finite shell whose radii are bounded below contributes at most
`card * lower_radius⁻¹ ^ τ` to the inverse-power sum. -/
lemma tsum_inv_rpow_le_card_mul_of_lower_bound {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le

/-- Inverse powers of dyadic radii split into the initial radius and a geometric factor. -/
lemma inv_dyadicRadius_rpow_eq (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [← Real.rpow_neg_eq_inv_rpow,
    Real.mul_rpow hr0 (by positivity), Real.rpow_natCast,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (-τ) k,
    Real.rpow_neg_eq_inv_rpow r0 τ]

lemma two_rpow_sub_eq_mul_neg (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]

lemma two_rpow_sub_pow_eq_mul_pow (ρ τ : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (ρ - τ)) ^ k =
      ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
  simp [two_rpow_sub_eq_mul_neg, mul_pow]

lemma dyadic_growth_inv_term_eq (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
        ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
  have hrk_inv :
      (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
    inv_dyadicRadius_rpow_eq r0 τ k hr0
  rw [hrk_inv, two_rpow_sub_pow_eq_mul_pow]
  ac_rfl

lemma dyadic_trailing_inv_term_le (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [inv_dyadicRadius_rpow_eq r0 τ k hr0]
  have hcoeff : C / L ≤ C / L + 1 := by linarith
  have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
    Real.rpow_nonneg (inv_nonneg.2 hr0) _
  have hmul :
      (C / L) * ((r0⁻¹ : ℝ) ^ τ)
        ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
    mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
  have hqpow_nonneg : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
  have := mul_le_mul_of_nonneg_right hmul hqpow_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma dyadic_growth_mass_mul_inv_le_geometric {C L M X T Ctrail r0 ρ τ : ℝ} {k : ℕ}
    (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
    (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
    (hT : T ≤ ((C * X + Ctrail) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
    T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
        + (((Ctrail / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
    mul_le_mul_of_nonneg_left hX hC
  have hnum : C * X + Ctrail ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail :=
    add_le_add hmul le_rfl
  have hdiv :
      (C * X + Ctrail) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L :=
    div_le_div_of_nonneg_right hnum hL.le
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
  have hrk_nonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
    mul_nonneg hr0 h2k_nonneg
  have hfactor_nonneg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
    Real.rpow_nonneg (inv_nonneg.2 hrk_nonneg) τ
  have hmul' :=
    mul_le_mul_of_nonneg_right hdiv hfactor_nonneg
  have hdecomp :
      ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) *
          ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
        =
        ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
    let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
    have :
        ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) * Y
          = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
            + ((Ctrail / L) * Y) := by
      ring
    simpa [Y]
  have hpre :
      T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
    hT.trans (hmul'.trans_eq hdecomp)
  have hA := le_of_eq (dyadic_growth_inv_term_eq C L M r0 ρ τ k hr0)
  have hB := dyadic_trailing_inv_term_le Ctrail L r0 τ k hr0
  exact hpre.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)

lemma two_geometric_shift_add (A B q qσ : ℝ) (k k0 : ℕ) :
    A * q ^ (k + k0) + B * qσ ^ (k + k0)
      = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
  rw [pow_add, pow_add]
  ac_rfl

end Real
