/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Liouville
public import TauCeti.Analysis.Convex.SimplyConnected

/-!
## Zero-free entire functions of polynomial growth are `exp` of a polynomial

This is the final “exp(poly)” step in Hadamard factorization:
if `H` is entire and has no zeros, then a polynomial-type growth bound of the form
`‖H z‖ ≤ exp (C * (1 + ‖z‖) ^ n)` forces `H = exp (P)` for a polynomial `P` with `P.natDegree ≤ n`.

## Main results

* `Complex.Hadamard.zero_free_polynomial_growth_is_exp_poly`

-/

@[expose] public section

open Complex Real Set Filter Topology Asymptotics Bornology

namespace Complex.Hadamard

/-- A zero-free entire function with polynomial growth is `exp` of a polynomial. -/
theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = Complex.exp (Polynomial.eval z P) := by
  obtain ⟨C, hCpos, hC⟩ := h_bound
  obtain ⟨k, hkd, hke⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ hH.differentiableOn
    (by simpa only [Set.mem_image, Set.mem_univ, true_and, not_exists] using h_nonzero)
  have hk : Differentiable ℂ k := differentiableOn_univ.mp hkd
  have hk_exp (z : ℂ) : H z = exp (k z) := (hke (Set.mem_univ z)).symm
  have hk_re (z : ℂ) : (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    have h := hC z
    rw [hk_exp z, norm_exp] at h
    exact Real.exp_le_exp.mp h
  let K : ℝ := C * 2 ^ n
  have hK : 0 < K := by dsimp [K]; positivity
  let L : ℂ → ℂ := fun z ↦ k z / (K : ℂ)
  have hL : Differentiable ℂ L := hk.div_const _
  have hLexp : (fun z ↦ exp (L z)) =O[cobounded ℂ]
      (fun z ↦ Real.exp (‖z‖ ^ (n : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    simp only [norm_exp, Real.norm_eq_abs, Real.abs_exp, one_mul]
    apply Real.exp_le_exp.mpr
    dsimp [L]
    rw [div_ofReal_re, Real.rpow_natCast, div_le_iff₀ hK]
    calc
      (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re z
      _ ≤ C * (2 * ‖z‖) ^ n := by gcongr; linarith
      _ = ‖z‖ ^ n * K := by dsimp [K]; ring
  have hLgrowth : L =O[cobounded ℂ] (fun z : ℂ ↦ z ^ n) := by
    have h := hL.isBigO_of_cexp_isBigO (by positivity : (0 : ℝ) ≤ n) hLexp
    simpa only [Real.rpow_natCast, ← norm_pow, isBigO_norm_right] using h
  have hkgrowth : k =O[cobounded ℂ] (fun z : ℂ ↦ z ^ n) := by
    have h := hLgrowth.const_mul_left (K : ℂ)
    have heq : (fun z ↦ (K : ℂ) * L z) = k := by
      ext z
      dsimp [L]
      field_simp [Complex.ofReal_ne_zero.mpr hK.ne']
    rwa [heq] at h
  obtain ⟨P, hP, hkP⟩ := hk.exists_eq_polynomial_eval_of_isBigO_pow hkgrowth
  exact ⟨P, hP, fun z ↦ (hk_exp z).trans (congrArg exp (congrFun hkP z))⟩

end Complex.Hadamard
