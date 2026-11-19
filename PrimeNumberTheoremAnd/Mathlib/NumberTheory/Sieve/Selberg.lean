/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
module

public import Batteries.Tactic.Lemma
import TauCeti.NumberTheory.Divisors
public import TauCeti.NumberTheory.SelbergSieve.LambdaSquared
public import TauCeti.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


@[expose] public noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "a" => BoundingSieve.weights (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "A" => BoundingSieve.support (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "𝒜" => BoundingSieve.multSum (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => @BoundingSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)

set_option quotPrecheck false
local notation3 "S" => BoundingSieve.truncatedSelbergSum
  (SelbergSieve.toBoundingSieve (self := s)) (Real.sqrt (SelbergSieve.level (self := s)))

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [ite_eq_left hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| @BoundingSieve.selbergTerms_pos _ d hdP
  · exact (s.toBoundingSieve.truncatedSelbergSum_pos (Real.one_le_sqrt.mpr hy)).le
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| @BoundingSieve.selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst {α : Type*} [AddCommMonoid α] (k n : ℕ) {f : ℕ → α} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  · have hs : n.divisors.filter (fun m => k * m ∣ n) = (n / k).divisors := by
      simpa only [Nat.dvd_div_iff_mul_dvd hkn] using
        (Nat.divisors_filter_dvd_of_dvd hn (Nat.div_dvd_of_dvd hkn))
    calc
      _ = ∑ l ∈ n.divisors with k ∣ l, f l := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun l hl => by
          by_cases hkl : k ∣ l
          · simp [hkl]
          · simp [hkl, h l (Nat.dvd_of_mem_divisors hl) hkl]
      _ = ∑ m ∈ (n / k).divisors, f (k * m) := Nat.sum_divisors_filter_dvd hkn f
      _ = _ := by rw [← Finset.sum_filter, hs]
  · rw [Finset.sum_eq_zero (fun l hl => h l (Nat.dvd_of_mem_divisors hl)
      (fun hkl => hkn (hkl.trans (Nat.dvd_of_mem_divisors hl))))]
    symm
    exact Finset.sum_eq_zero fun m _ =>
      ite_eq_right (fun hkm => hkn ((Nat.dvd_mul_right k m).trans hkm))

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [ite_eq_right h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [ite_eq_right]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [ite_eq_left h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (@BoundingSieve.selbergTerms_isMultiplicative _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [ite_eq_right, mul_zero]
    push Not; intro h; contradiction

/-- The fork's weights are Tau Ceti's normalized Selberg weights at the cutoff `√y`. -/
theorem selbergWeights_eq_boundingSieve_selbergWeights :
    γ = s.toBoundingSieve.selbergWeights (Real.sqrt y) := by
  funext d
  by_cases hd : d ∣ P
  · apply mul_left_cancel₀ (nu_ne_zero hd)
    rw [selbergWeights_eq_dvds_sum, nu_mul_selbergWeights, mul_comm ((s.toBoundingSieve.truncatedSelbergSum (Real.sqrt y))⁻¹)]
    congr 1
    refine sum_congr rfl fun l _ ↦ ?_
    simp only [Real.le_sqrt (Nat.cast_nonneg l) (zero_le_one.trans hy)]
  · rw [selbergWeights, ite_eq_right hd, BoundingSieve.selbergWeights_eq_zero_of_not_dvd _ _ hd]

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · rw [Nat.gcd_comm, Nat.mul_comm k m]
      exact (Nat.gcd_mul_of_coprime_of_dvd h.2 hkd).symm
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    simp only [truncatedSelbergSum_def, Real.le_sqrt (Nat.cast_nonneg _) (zero_le_one.trans hy)]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [ite_eq_right]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (@BoundingSieve.selbergTerms_isMultiplicative _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply ite_eq_right
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| @BoundingSieve.selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| @BoundingSieve.selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| @BoundingSieve.selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact (s.toBoundingSieve.truncatedSelbergSum_pos (Real.one_le_sqrt.mpr hy)).ne'
    dsimp only [selbergWeights]; rw [ite_eq_left hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [selbergWeights, ite_eq_right hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    exact le_of_mul_le_mul_of_pos_right this
      (s.toBoundingSieve.truncatedSelbergSum_pos (Real.one_le_sqrt.mpr hy))
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  have hγ := s.selbergWeights_eq_boundingSieve_selbergWeights
  calc
    siftedSum ≤ X * mainSum μ⁺ + errSum μ⁺ :=
      BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius μ⁺
        (BoundingSieve.upperMoebius_lambdaSquared γ
          (hγ ▸ selbergWeights_one _ (Real.one_le_sqrt.mpr hy)))
    _ ≤ _ := ?_
  gcongr
  · rw [selbergMuPlus, hγ, mainSum_lambdaSquared_selbergWeights, div_eq_mul_inv]
  · refine errSum_lambdaSquared_le_sum_three_pow_cardDistinctFactors _ γ y
      (fun d _ => s.selberg_bound_weights d) (fun d hdP hd => ?_)
    rw [hγ, selbergWeights_eq_zero_of_lt _ _ _
      ((Real.sqrt_lt' (Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hdP))).mpr (lt_of_not_ge hd))]

end SelbergSieve
