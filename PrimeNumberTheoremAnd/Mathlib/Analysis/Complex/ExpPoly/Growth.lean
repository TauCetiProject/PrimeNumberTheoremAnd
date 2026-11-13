/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ExpPoly
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth


/-!
## Growth of functions of the form `exp (P.eval z)`

This file contains auxiliary estimates used in “degree integrality” arguments: if `exp (P.eval)`
satisfies a growth bound with exponent `ρ`, then `P.natDegree ≤ ⌊ρ⌋`.


## Main results

* `Complex.Hadamard.natDegree_le_floor_of_growth_exp_eval`
* `Complex.Hadamard.natDegree_le_floor_of_exp_eval_norm_bound` : exponential norm bound implies
  degree bound

-/

@[expose] public section

noncomputable section

namespace Complex
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric

open scoped Topology

open Polynomial

/-!
### Integer-order obstruction for `exp (P.eval)`

If `exp (P.eval)` satisfied a growth bound with exponent `ρ < natDegree P`, then along a suitable
ray we get `log (1 + ‖exp (P z)‖) ≳ ‖z‖ ^ natDegree P`, contradicting the assumed exponent `ρ`.
This is the “degree is an integer” upgrade used to get `≤ ⌊ρ⌋` rather than a ceiling-type bound.
-/

private lemma mul_conj_div_norm (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)]

private lemma exists_z_norm_eq_re_eval_ge
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hn
  have ha : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  let a := P.leadingCoeff
  let wtarget : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have hwtarget : ‖wtarget‖ = 1 := by
    simp [wtarget, a, ha]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq wtarget hn
  have hw_norm : ‖w‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn.ne').mp
    simpa only [norm_pow, hwtarget] using congrArg norm hw
  have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, _, hB⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  let z : ℂ := (R : ℂ) * w
  have hz : ‖z‖ = R := by simp [z, hw_norm, abs_of_nonneg hR0]
  have hlead : P.leadingCoeff * z ^ P.natDegree = ((‖a‖ * R ^ P.natDegree : ℝ) : ℂ) := by
    have hamul : a * w ^ P.natDegree = (‖a‖ : ℂ) := by
      rw [hw]
      exact mul_conj_div_norm a ha
    calc
      P.leadingCoeff * z ^ P.natDegree = (R : ℂ) ^ P.natDegree * (a * w ^ P.natDegree) := by
        dsimp [z, a]
        ring
      _ = ((‖a‖ * R ^ P.natDegree : ℝ) : ℂ) := by rw [hamul]; push_cast; ring
  have herror := hB (show B ≤ ‖z‖ by rw [hz]; exact (le_max_left _ _).trans hR)
  change ‖P.eval z - P.leadingCoeff * z ^ P.natDegree‖ ≤
    (1 / 2 : ℝ) * ‖P.leadingCoeff * z ^ P.natDegree‖ at herror
  have hreal := neg_le_of_abs_le (Complex.abs_re_le_norm (P.eval z - P.leadingCoeff * z ^ P.natDegree))
  rw [hlead] at herror hreal
  simp only [Complex.sub_re, Complex.ofReal_re] at hreal
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg a) (pow_nonneg hR0 _))] at herror
  refine ⟨z, hz, ?_⟩
  change (‖a‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re
  nlinarith

/-- If `exp (P.eval z)` satisfies a polynomial-type growth bound of exponent `ρ`,
then `P.natDegree ≤ ⌊ρ⌋`. -/
theorem natDegree_le_floor_of_growth_exp_eval
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · simp [hdeg]
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases exists_z_norm_eq_re_eval_ge (P := P) hnpos with ⟨R0, hR0pos, hray⟩
    rcases hgrowth with ⟨C, hCpos, hC⟩
    have hLCpos : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos hLCpos this)
    have hn_le_real : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have hnlt' : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 hnlt'
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have hR_ge1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have hR_ge_R1 : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R hR_ge_R1
      rcases hray R hR_ge_R0 with ⟨z, hz_norm, hz_re⟩
      have hlog_lower :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have hlog_upper :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have hz_re' : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have hz_re'' : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          simpa [Real.rpow_natCast, c] using hz_re'
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          hz_re''.trans hlog_lower
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans hlog_upper
        simpa [hz_norm] using this
      have h1R_le : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) h1R_le hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have hRnonneg : 0 ≤ R := le_of_lt hR_pos
        have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow hRnonneg h2nonneg (z := ρ))
      have hmain' : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt hRρ_pos
      have hdiv :
          (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right hmain' (le_of_lt hRρ_pos)
        have hRhs : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        simpa [hRhs, mul_assoc, mul_left_comm, mul_comm] using h
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have hRδ_le : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        have hLhs : c * (R ^ δ) = (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) := by
          simp [hRsub, div_eq_mul_inv, mul_left_comm, mul_comm]
        simpa [hLhs] using hdiv
      have hRδ_le' : R ^ δ ≤ K0 := by
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          refine (le_div_iff₀ hcpos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 hn_le_real

/-- A norm bound for `exp (P z)` gives the corresponding polynomial degree bound. -/
theorem natDegree_le_floor_of_exp_eval_norm_bound {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ)
    (hbound :
      ∃ C > 0, ∀ z : ℂ,
        ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
    P.natDegree ≤ Nat.floor τ := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hlog_growth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ :=
    Real.log_growth_of_norm_le_exp_mul_rpow
      (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
      (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ
      (fun z => by linarith [norm_nonneg z]) hC
  exact natDegree_le_floor_of_growth_exp_eval (ρ := τ) hτ P hlog_growth

end Hadamard
end Complex
