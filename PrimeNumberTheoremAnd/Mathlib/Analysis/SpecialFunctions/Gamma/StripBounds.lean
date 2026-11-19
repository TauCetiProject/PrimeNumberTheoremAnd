/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Stirling
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds



/-!
# Gamma bounds in half-planes

Bounds for `Complex.Gamma` and Deligne's real Gamma factor `Complex.Gammaℝ` on full
half-planes. Uncompleted zeta growth uses the plain Gamma bound; the archimedean bounds remain.
-/

@[expose] public section

noncomputable section

open Complex Real Set Metric


/-! ## Stirling-type bounds for the complex Gamma function

This section provides Stirling-type bounds on `Complex.Gamma` and the archimedean factor `Gammaℝ`
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.
-/



namespace Complex.Gamma

open Real

/-- For `re s ≥ 1`, the real Gamma bound controls `‖Γ(s)‖` in terms of `‖s‖`. -/
theorem norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  refine ⟨1, by norm_num, fun s hs ↦ ?_⟩
  rw [one_mul]
  by_cases hs2 : 2 ≤ s.re
  · have hre := Complex.re_le_norm s
    calc
      ‖Gamma s‖ ≤ Real.Gamma s.re := Complex.norm_Gamma_le_Gamma_re (by linarith)
      _ ≤ (s.re + 1) ^ (s.re + 1) := Real.Gamma_le_add_one_rpow hs2
      _ ≤ (1 + ‖s‖) ^ (s.re + 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg s]) (by linarith)
  · have hsegment : s.re ∈ segment ℝ (1 : ℝ) 2 := by
      simpa only [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)] using
        (show s.re ∈ Icc 1 2 from ⟨hs, (lt_of_not_ge hs2).le⟩)
    have hreal : Real.Gamma s.re ≤ 1 := by
      simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using
        Real.convexOn_Gamma.le_on_segment (by norm_num) (by norm_num) hsegment
    exact ((Complex.norm_Gamma_le_Gamma_re (by linarith)).trans hreal).trans
      (Real.one_le_rpow (by linarith [norm_nonneg s]) (by linarith [norm_nonneg s]))

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  refine ⟨8, by norm_num, fun s hs hn ↦ ?_⟩
  have hshift : ‖Gamma (s + 1)‖ ≤ ‖Gamma (s + 1 + 1)‖ := by
    simpa only [Nat.cast_one] using
      Complex.norm_Gamma_le_norm_Gamma_add_of_one_le_re (s := s + 1)
        (by simp only [Complex.add_re, Complex.one_re]; linarith) 1
  have hpart : (s + 1 + 1).re = s.re + 2 := by
    simp only [Complex.add_re, Complex.one_re]
    ring
  have hΓ : ‖Gamma s‖ ≤ Real.Gamma (s.re + 2) := by
    refine ((Complex.norm_Gamma_le_norm_Gamma_add_one hn).trans hshift).trans ?_
    simpa only [hpart] using Complex.norm_Gamma_le_Gamma_re (s := s + 1 + 1)
      (by rw [hpart]; linarith)
  have hreal : Real.Gamma (s.re + 2) ≤
      Real.exp ((s.re + 3) * Real.log (s.re + 3)) := by
    simpa only [add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using
      Real.Gamma_le_exp_mul_log (x := s.re + 2) (by linarith)
  have hlinear : s.re + 3 ≤ 4 * ‖s‖ := by
    linarith only [Complex.re_le_norm s, hn]
  have hsquare : s.re + 3 ≤ (1 + ‖s‖) ^ 2 := by
    nlinarith only [Complex.re_le_norm s, hn, sq_nonneg (‖s‖ - 1)]
  have hlog : Real.log (s.re + 3) ≤ 2 * Real.log (1 + ‖s‖) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by linarith : 0 < s.re + 3) hsquare
  have hprod : (s.re + 3) * Real.log (s.re + 3) ≤
      (4 * ‖s‖) * (2 * Real.log (1 + ‖s‖)) :=
    mul_le_mul hlinear hlog (Real.log_nonneg (by linarith)) (by positivity)
  exact (hΓ.trans hreal).trans (Real.exp_le_exp.mpr (by nlinarith only [hprod]))

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C, hC, hbound⟩ := Complex.Gamma.stirling_bound_re_ge_zero
  let A : ℝ := (3 / 2) * (Real.log 3 / Real.log 2 + 1)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨1 + C * A, by positivity, ?_⟩
  intro s hs hn
  have hs2 : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by simpa using (show (1 / 2 : ℝ) ≤ ‖s‖ / 2 by linarith)
  have hwre : 0 ≤ (s / 2 + 1).re := by simp; linarith
  have hw1 : (1 : ℝ) ≤ (s / 2 + 1).re := by simp; linarith
  have hwnorm : 1 ≤ ‖s / 2 + 1‖ := hw1.trans (Complex.re_le_norm _)
  have hshift :
      C * (‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) ≤
        C * (A * (‖s‖ * Real.log (1 + ‖s‖))) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    dsimp only [A]
    have hnorm : ‖s / 2 + 1‖ ≤ (3 / 2) * ‖s‖ :=
      (norm_add_le_of_le (by simp : ‖s / 2‖ ≤ ‖s‖ / 2)
        (by simp : ‖(1 : ℂ)‖ ≤ (1 : ℝ))).trans (by linarith)
    have hlog_shift : Real.log (1 + ‖s / 2 + 1‖) ≤ 2 * Real.log (1 + ‖s‖) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using
        (Real.log_le_log (x := 1 + ‖s / 2 + 1‖) (y := (1 + ‖s‖) ^ (2 : ℕ))
          (by positivity) (by nlinarith only [hnorm, hn, sq_nonneg ‖s‖]))
    have hcoef : (3 : ℝ) ≤ (3 / 2) * (Real.log 3 / Real.log 2 + 1) := by
      have h : (1 : ℝ) ≤ Real.log 3 / Real.log 2 :=
        (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
          (by simpa only [one_mul] using
            Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3))
      linarith
    calc
      ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
          3 * (‖s‖ * Real.log (1 + ‖s‖)) := by
        nlinarith only [mul_le_mul hnorm hlog_shift
          (Real.log_nonneg (by linarith [norm_nonneg (s / 2 + 1)])) (by positivity)]
      _ ≤ ((3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)) *
          (‖s‖ * Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (norm_nonneg s) (Real.log_nonneg (by linarith [norm_nonneg s])))
  have hlog : Real.log 2 ≤ ‖s‖ * Real.log (1 + ‖s‖) := by
    have h : Real.log 2 ≤ Real.log (1 + ‖s‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    exact h.trans (le_mul_of_one_le_left (Real.log_nonneg (by linarith)) hn)
  calc
    ‖Complex.Gamma (s / 2)‖ ≤ 2 * ‖Complex.Gamma (s / 2 + 1)‖ := by
      rw [Complex.Gamma_add_one _ (norm_pos_iff.mp (by linarith only [hs2])), norm_mul]
      nlinarith only [mul_le_mul_of_nonneg_right hs2 (norm_nonneg (Complex.Gamma (s / 2)))]
    _ ≤ 2 * Real.exp (C * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
      mul_le_mul_of_nonneg_left (hbound _ hwre hwnorm) (by norm_num)
    _ = Real.exp (Real.log 2 + C * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp ((1 + C * A) * ‖s‖ * Real.log (1 + ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      dsimp only [A] at hshift ⊢
      nlinarith

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

/-- **Stirling bound for the archimedean factor** `Γ_ℝ = π^{-s/2} · Γ(s/2)`. -/
theorem bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma.half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      (by simpa using (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs_re)
        (by norm_num : (0 : ℝ) ≤ 2)))
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

/-- Finite order bound for Γ_ℝ. -/
theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := bound_re_ge_zero
  use C + 1, 2
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  refine (hC s hs_re hs_norm).trans (Real.exp_le_exp.mpr ?_)
  have hlog : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖s‖)
  have h := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC_pos.le (norm_nonneg s))
  rw [Real.rpow_two]
  nlinarith only [h, sq_nonneg ‖s‖]

end Complex.Gammaℝ.Stirling
end
