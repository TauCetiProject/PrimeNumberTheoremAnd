/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GammaBounds



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

namespace Real.Stirling

/-- For `x ≥ 1`, `log (1 + x) ≥ log 2`. -/
lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

/-- For `x ≥ 1`, `log (1 + x) > 0`. -/
lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

/-- `√π < 2`. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

/-- For `x ≥ 1`, `log 2 ≤ x * log (1 + x)`. -/
lemma log_two_le_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ x * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_le := log_one_add_ge_log_two hx
  have hx_mul : x * Real.log 2 ≤ x * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left hlog2_le (by linarith)
  have hx_ge : Real.log 2 ≤ x * Real.log 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx hlog2_pos.le
  exact le_trans hx_ge hx_mul

/-- For `x ≥ 1`, `log 3 ≤ (log 3 / log 2) * log (1 + x)`. -/
lemma log_three_le_coef_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 3 ≤ (Real.log 3 / Real.log 2) * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 := div_nonneg hlog3_pos.le hlog2_pos.le
  have hscaled :
      (Real.log 3 / Real.log 2) * Real.log 2 ≤
        (Real.log 3 / Real.log 2) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left (log_one_add_ge_log_two hx) hcoef_nonneg
  simpa [div_mul_cancel₀ _ hlog2_ne] using hscaled

/-- Absorbs the `s ↦ s/2 + 1` shift in half-plane Stirling bounds. -/
noncomputable def half_shift_log_constant : ℝ :=
  (3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)

lemma half_shift_log_constant_pos : 0 < half_shift_log_constant := by
  have hthree : 0 < (3 / 2 : ℝ) := by norm_num
  have hcoef : 0 < Real.log 3 / Real.log 2 + 1 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 :=
      div_nonneg hlog3_pos.le hlog2_pos.le
    linarith
  simpa [half_shift_log_constant] using mul_pos hthree hcoef

end Real.Stirling

namespace Complex.Gamma

open Real

/-- For `‖s‖ ≥ 1`, `‖s + 1‖ ≤ 2 * ‖s‖`. -/
lemma norm_add_one_le_two_mul_norm {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ ≤ 2 * ‖s‖ := by
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
  nlinarith [h1, hs]

/-- For `‖s‖ ≥ 1`, `‖s/2 + 1‖ ≤ (3/2) * ‖s‖`. -/
lemma norm_div_two_add_one_le_three_halves_mul {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ ≤ (3 / 2) * ‖s‖ := by
  have h1 : ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by simpa using norm_add_le (s / 2) (1 : ℂ)
  have h1' : ‖s / 2 + 1‖ ≤ ‖s‖ / 2 + 1 := by simpa using h1
  nlinarith [h1', hs]

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s + 1‖) ≤ log 2 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s + 1‖) ≤ Real.log 2 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s + 1‖ : ℝ) := by linarith [norm_nonneg (s + 1)]
  have hle : (1 + ‖s + 1‖ : ℝ) ≤ 2 * (1 + ‖s‖) := by
    have hn : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
    nlinarith [hn, hs]
  have hlog' : Real.log (1 + ‖s + 1‖) ≤ Real.log (2 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (2 * (1 + ‖s‖)) = Real.log 2 + Real.log (1 + ‖s‖) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h2 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s/2 + 1‖) ≤ log 3 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_div_two_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log 3 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s / 2 + 1‖ : ℝ) := by linarith [norm_nonneg (s / 2 + 1)]
  have hle : (1 + ‖s / 2 + 1‖ : ℝ) ≤ 3 * (1 + ‖s‖) := by
    nlinarith [norm_div_two_add_one_le_three_halves_mul hs]
  have hlog' : Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log (3 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (3 * (1 + ‖s‖)) = Real.log 3 + Real.log (1 + ‖s‖) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h3 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, the `s ↦ s + 1` shift in the Stirling exponent is absorbed by a factor `4`. -/
lemma norm_mul_log_shift_add_one_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖) ≤ 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog2_le := Real.Stirling.log_one_add_ge_log_two hs
  have hlog_add_le : Real.log (1 + ‖s + 1‖) ≤ 2 * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_add_one_le hs, hlog2_le]
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s + 1)])
  calc
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖)
        ≤ (2 * ‖s‖) * Real.log (1 + ‖s + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_add_one_le_two_mul_norm hs) hlog_nonneg
    _ ≤ (2 * ‖s‖) * (2 * Real.log (1 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left hlog_add_le (by positivity)
    _ = 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by ring

/-- For `‖s‖ ≥ 1`, the `s ↦ s/2 + 1` shift in the half-plane Stirling exponent. -/
lemma norm_mul_log_shift_half_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
      Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s / 2 + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s / 2 + 1)])
  have hlog_w' :
      Real.log (1 + ‖s / 2 + 1‖) ≤
        (Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_div_two_add_one_le hs,
      Real.Stirling.log_three_le_coef_mul_log_one_add hs]
  calc
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
        ≤ ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_div_two_add_one_le_three_halves_mul hs) hlog_nonneg
    _ ≤ Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have hstep2 :
          ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) ≤
            ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left hlog_w' (by positivity)
      have hEq :
          ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) =
            Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
        simp [Real.Stirling.half_shift_log_constant, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans hstep2 (by simp [hEq])

/-- From `Γ(z + 1) = z Γ(z)` and `1/2 ≤ ‖z‖`, bound `‖Γ(z)‖` by `2 * ‖Γ(z + 1)‖`. -/
lemma norm_Gamma_le_two_mul_norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) (hz_lb : (1 / 2 : ℝ) ≤ ‖z‖) :
    ‖Gamma z‖ ≤ 2 * ‖Gamma (z + 1)‖ := by
  have hfunc := Gamma_add_one z hz
  have hnorm_mul : ‖Gamma (z + 1)‖ = ‖z‖ * ‖Gamma z‖ := by
    calc
      ‖Gamma (z + 1)‖ = ‖z * Gamma z‖ := by simp [hfunc]
      _ = ‖z‖ * ‖Gamma z‖ := by simp
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_lb
  have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
  have h_inv : 1 / ‖z‖ ≤ (2 : ℝ) := by
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    simpa using one_div_le_one_div_of_le hhalf_pos hz_lb
  have : ‖Gamma z‖ = ‖Gamma (z + 1)‖ / ‖z‖ := by
    calc
      ‖Gamma z‖ = (‖z‖ * ‖Gamma z‖) / ‖z‖ := by field_simp [hz_ne]
      _ = ‖Gamma (z + 1)‖ / ‖z‖ := by simp [hnorm_mul]
  rw [this, div_eq_mul_inv]
  have :
      (‖Gamma (z + 1)‖ : ℝ) * (1 / ‖z‖) ≤ ‖Gamma (z + 1)‖ * 2 :=
    mul_le_mul_of_nonneg_left h_inv (norm_nonneg _)
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

/-- `Gamma` is bounded on any compact set that does not contain non-positive integers. -/
lemma norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-- For `1/2 ≤ re w ≤ 1`, `‖Γ(w)‖ ≤ 4`. -/
lemma norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le
    (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.Stirling.sqrt_pi_lt_two]
    _ = 4 := by norm_num

/-- For any `s : ℂ`, the real part of `s' := s - ⌊Re(s)⌋` lies in `[0, 1)`. -/
lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

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
  · exact (Complex.Gamma.norm_le_one hs (by linarith)).trans
      (Real.one_le_rpow (by linarith [norm_nonneg s]) (by linarith [norm_nonneg s]))

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  let K := Real.pi + |Real.log (2 * Real.pi)| / 2 + 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + K / Real.log 2, by positivity, ?_⟩
  intro s hs hn
  by_cases hG : Complex.Gamma s = 0
  · simp only [hG, norm_zero]
    exact (Real.exp_pos _).le
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hG)).mp
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hn))
  have harg : |s.arg| ≤ Real.pi - Real.pi / 2 := by
    simpa only [sub_half] using (Complex.abs_arg_le_pi_div_two_iff.mpr hs)
  have he := TauCeti.abs_log_norm_Gamma_sub_stirling_le
    (half_pos Real.pi_pos) (by linarith [Real.pi_pos]) harg hs0
  simp only [Real.cos_pi_div_two, sub_zero, one_pow, one_mul] at he
  have hlogn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hn
  have hlogle : Real.log ‖s‖ ≤ Real.log (1 + ‖s‖) :=
    Real.log_le_log (zero_lt_one.trans_le hn) (by linarith)
  have hre : (s.re - 1 / 2) * Real.log ‖s‖ ≤ ‖s‖ * Real.log (1 + ‖s‖) :=
    (mul_le_mul_of_nonneg_right (by linarith [Complex.re_le_norm s]) hlogn).trans
      (mul_le_mul_of_nonneg_left hlogle (norm_nonneg _))
  have him : -(s.im * s.arg) ≤ ‖s‖ * Real.pi := by
    calc
      -(s.im * s.arg) ≤ |s.im * s.arg| := neg_le_abs _
      _ = |s.im| * |s.arg| := abs_mul _ _
      _ ≤ ‖s‖ * Real.pi := mul_le_mul (Complex.abs_im_le_norm s)
        (Complex.abs_arg_le_pi s) (abs_nonneg _) (norm_nonneg _)
  have herr : 2 / ‖s‖ ≤ 2 := div_le_self (by norm_num) hn
  have hconst : Real.log (2 * Real.pi) / 2 ≤ |Real.log (2 * Real.pi)| / 2 :=
    div_le_div_of_nonneg_right (le_abs_self _) (by norm_num)
  have hrough : Real.log ‖Complex.Gamma s‖ ≤
      ‖s‖ * Real.log (1 + ‖s‖) + K * ‖s‖ := by
    have hk : |Real.log (2 * Real.pi)| / 2 + 2 ≤
        (|Real.log (2 * Real.pi)| / 2 + 2) * ‖s‖ :=
      le_mul_of_one_le_right (by positivity) hn
    have hupper := (abs_le.mp he).2
    dsimp [K]
    nlinarith
  have hL : Real.log 2 ≤ Real.log (1 + ‖s‖) :=
    Real.Stirling.log_one_add_ge_log_two hn
  have hscale : K * ‖s‖ ≤ (K / Real.log 2) * (‖s‖ * Real.log (1 + ‖s‖)) := by
    have hm := (le_div_iff₀ hlog2).mpr
      (mul_le_mul_of_nonneg_left hL (mul_nonneg hK.le (norm_nonneg s)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
  nlinarith

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C, hC, hbound⟩ := Complex.Gamma.stirling_bound_re_ge_zero
  let A := Real.Stirling.half_shift_log_constant
  have hA : 0 < A := Real.Stirling.half_shift_log_constant_pos
  refine ⟨1 + C * A, by positivity, ?_⟩
  intro s hs hn
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hn))
  have hs2 : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by simpa using (show (1 / 2 : ℝ) ≤ ‖s‖ / 2 by linarith)
  have hwre : 0 ≤ (s / 2 + 1).re := by simp; linarith
  have hw1 : (1 : ℝ) ≤ (s / 2 + 1).re := by simp; linarith
  have hwnorm : 1 ≤ ‖s / 2 + 1‖ := hw1.trans (Complex.re_le_norm _)
  have hshift := mul_le_mul_of_nonneg_left
    (Complex.Gamma.norm_mul_log_shift_half_bound hn) hC.le
  have hlog := Real.Stirling.log_two_le_mul_log_one_add hn
  calc
    ‖Complex.Gamma (s / 2)‖ ≤ 2 * ‖Complex.Gamma (s / 2 + 1)‖ :=
      Complex.Gamma.norm_Gamma_le_two_mul_norm_Gamma_add_one (div_ne_zero hs0 (by norm_num)) hs2
    _ ≤ 2 * Real.exp (C * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
      mul_le_mul_of_nonneg_left (hbound _ hwre hwnorm) (by norm_num)
    _ = Real.exp (Real.log 2 + C * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp ((1 + C * A) * ‖s‖ * Real.log (1 + ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      dsimp [A] at ⊢
      nlinarith

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

/-- The norm of `π^{-s/2}` is at most `1` when `Re(s) ≥ 0`. -/
lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
  have h_re : (-s / 2).re = -s.re / 2 := by simp [Complex.neg_re]
  rw [h_re]
  have h_exp : -s.re / 2 ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

/-- The norm of `(2π)^{-w}` is at most `1` when `Re(w) ≥ 0`. -/
lemma norm_cpow_two_mul_pi_neg_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
    have : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    exact le_of_lt this
  have hnorm : ‖(2 * π : ℂ) ^ (-w)‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := 2 * Real.pi) hbase_pos (-w)
  rw [hnorm]
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr hw)

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
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
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
  have h := hC s hs_re hs_norm
  apply le_trans h
  apply Real.exp_le_exp.mpr
  -- log(1 + |s|) ≤ |s| for |s| ≥ 1, so C|s|log(1+|s|) ≤ C|s|² ≤ (C+1)|s|²
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : ‖s‖ + 1 ≤ Real.exp ‖s‖ := Real.add_one_le_exp ‖s‖
    have h2' : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by linarith
    rw [Real.log_le_iff_le_exp (by linarith [norm_nonneg s])]
    exact h2'
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ 2 := by ring
  have step3 : C * ‖s‖ ^ 2 ≤ (C + 1) * ‖s‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_combined : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log (1 + ‖s‖)
        ≤ C * ‖s‖ * ‖s‖ := step1
      _ = C * ‖s‖ ^ 2 := step2
      _ ≤ (C + 1) * ‖s‖ ^ 2 := step3
  -- Convert from ℕ exponent (^ 2) to ℝ exponent (^ (2 : ℝ))
  -- The goal is (C + 1) * ‖s‖ ^ (2 : ℝ), which equals (C + 1) * ‖s‖ ^ (2 : ℕ)
  -- This type coercion is handled by norm_cast
  have hconv : (C + 1) * ‖s‖ ^ 2 = (C + 1) * ‖s‖ ^ (2 : ℝ) := by norm_cast
  rw [← hconv]
  exact h_combined

end Complex.Gammaℝ.Stirling
end
