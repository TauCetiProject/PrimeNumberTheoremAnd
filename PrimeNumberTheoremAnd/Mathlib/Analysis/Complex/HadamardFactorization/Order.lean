/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Growth
public import TauCeti.Analysis.Complex.GrowthOrder
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Hadamard factorization for finite-order entire functions

Upgrades `hadamard_factorization_of_growth` to the finite-order formulation via
`EntireOfOrderAtMost` and sequence- or divisor-indexed canonical products.

The growth input is routed through a midpoint exponent `τ` with `⌊τ⌋ = ⌊ρ⌋` so genus
`⌊ρ⌋` matches Tao's Weierstrass factor degree.

This file proves the finite-order Hadamard factorization theorem, corresponding to
[tao246bComplexAnalysis], Theorem 22.  The sequence-indexed theorem below packages the same
factorization after choosing an enumeration of the nonzero divisor indices.

## Main results

* `hadamard_factorization_of_order` : `f = exp(P) · z^k · ∏' E_m(z/a)`
* `hadamard_factorization_of_order_sequence` : sequence-indexed reindexing of the zero divisor
* `hadamard_factorization_of_order_centered` : arbitrary-center form, derived by translation
* `EntireOfOrderAtMost` : order at most `ρ` in the `ε`-family sense

## References

* [tao246bComplexAnalysis], Theorem 22
* [boas1954] and [levin1980] for the classical finite-order Hadamard product theorem, including
  genus `⌊ρ⌋` for functions of order at most `ρ`
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics Bornology
open scoped Topology BigOperators

namespace Complex.Hadamard

/-- Translating the input moves the origin order to the order at the translation center. -/
lemma analyticOrderNatAt_comp_add_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w + c)) 0 = analyticOrderNatAt f c := by
  let g : ℂ → ℂ := fun w => w + c
  have hg : AnalyticAt ℂ g 0 := by fun_prop
  have hg' : deriv g 0 ≠ 0 := by
    simp [g]
  have h :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := f) (g := g) (z₀ := (0 : ℂ)) hg hg'
  have h' :
      analyticOrderAt ((fun x : ℂ => f x) ∘ g) 0 = analyticOrderAt f c := by
    simpa [g] using h
  simpa [analyticOrderNatAt, g] using! congrArg ENat.toNat h'

/-- Subtracting a constant is the corresponding special case of translation for the origin order. -/
lemma analyticOrderNatAt_comp_sub_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w - c)) 0 = analyticOrderNatAt f (-c) := by
  simpa [sub_eq_add_neg] using analyticOrderNatAt_comp_add_const f (-c)

/-- The centered Hadamard denominator is the ordinary denominator for the translated function. -/
theorem centeredHadamardDenom_eq_hadamardDenom_translate
    (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    centeredHadamardDenom m c f z =
      hadamardDenom m (fun w : ℂ => f (w + c)) (z - c) := by
  simp [centeredHadamardDenom, hadamardDenom, analyticOrderNatAt_comp_add_const]

/-- An entire function has order at most `ρ` if it satisfies the `ε`-family growth bound used in
this formalization.

For every `ε > 0`, the norm is bounded by an exponential of order `ρ + ε`. This formulation is
the convenient finite-order input for the Jensen/counting estimates used in the Hadamard
factorization pipeline. -/
def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

namespace EntireOfOrderAtMost

theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f) :
    Differentiable ℂ f :=
  h.1

theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε

/-- At nonnegative orders, the native asymptotic bound gives the global exponential bound. -/
theorem of_orderLE {ρ : ℝ} {f : ℂ → ℂ} (hρ : 0 ≤ ρ)
    (hf : Differentiable ℂ f) (h : TauCeti.OrderLE f ρ) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, fun ε hε ↦ ?_⟩
  let τ := ρ + ε
  have hτ : 0 ≤ τ := by dsimp [τ]; linarith
  let g : ℂ → ℝ := fun z ↦ Real.exp (‖z‖ ^ τ)
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop (disch := positivity)
  have hquotcont : Continuous (fun z ↦ ‖f z‖ / g z) :=
    hf.continuous.norm.div hgcont (fun z ↦ Real.exp_ne_zero _)
  have hO : (fun z ↦ ‖f z‖ / g z) =O[cocompact ℂ] (1 : ℂ → ℝ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact (div_isBoundedUnder_of_isBigO (h.isBigO (by dsimp [τ]; linarith)).norm_left).isBigO_const
      one_ne_zero
  obtain ⟨C, hC, hbound⟩ := (hquotcont.isBounded_range_iff_isBigO.mpr hO).exists_pos_norm_le
  refine ⟨C + 1, by positivity, fun z ↦ ?_⟩
  have hratio := hbound _ (Set.mem_range_self z)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hratio
  have hfz : ‖f z‖ ≤ C * g z := (div_le_iff₀ (Real.exp_pos _)).mp hratio
  have hp : ‖z‖ ^ τ ≤ (1 + ‖z‖) ^ τ :=
    Real.rpow_le_rpow (norm_nonneg _) (by linarith) hτ
  have hB : 1 ≤ (1 + ‖z‖) ^ τ := Real.one_le_rpow (by linarith [norm_nonneg z]) hτ
  calc
    ‖f z‖ ≤ C * g z := hfz
    _ ≤ Real.exp C * Real.exp ((1 + ‖z‖) ^ τ) :=
      mul_le_mul (Real.le_exp_self C) (Real.exp_le_exp.mpr hp) (by positivity) (by positivity)
    _ = Real.exp (C + (1 + ‖z‖) ^ τ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C + 1) * (1 + ‖z‖) ^ τ) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hB hC.le]

/-- The global exponential bound supplies Tau Ceti’s native order predicate at nonnegative order. -/
theorem orderLE {ρ : ℝ} {f : ℂ → ℂ} (hρ : 0 ≤ ρ)
    (h : EntireOfOrderAtMost ρ f) : TauCeti.OrderLE f ρ := by
  rw [TauCeti.orderLE_def]
  intro p hp
  let τ := (ρ + p) / 2
  have hρτ : ρ < τ := by dsimp [τ]; linarith
  have hτp : τ < p := by dsimp [τ]; linarith
  have hτ : 0 ≤ τ := hρ.trans hρτ.le
  obtain ⟨C, hC, hbound⟩ := h.exists_bound (sub_pos.mpr hρτ)
  have hbound' (z : ℂ) : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    simpa only [add_sub_cancel] using hbound z
  refine (IsBigO.of_bound 1 ?_).trans (TauCeti.isBigO_exp_mul_norm_rpow (C * 2 ^ τ) hτp)
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with z hz
  have hbase : 1 + ‖z‖ ≤ 2 * ‖z‖ := by linarith
  have hpow : (1 + ‖z‖) ^ τ ≤ 2 ^ τ * ‖z‖ ^ τ := by
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)] using
      Real.rpow_le_rpow (by positivity) hbase hτ
  simpa only [Real.norm_eq_abs, Real.abs_exp, one_mul, mul_assoc] using
    (hbound' z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hC.le))

/-- A single exponential bound of order `ρ` implies the `ε`-family bound defining
`EntireOfOrderAtMost`. -/
theorem of_norm_le_exp {ρ : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hbound : ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, ?_⟩
  rintro ε hε
  rcases hbound with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  exact Real.norm_le_exp_mul_rpow_of_exponent_le (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hC.le
    (fun z => by linarith [norm_nonneg z]) (by linarith : ρ ≤ ρ + ε) hCbound

/-- A finite-order bound gives a logarithmic growth bound at any larger exponent. -/
theorem exists_log_growth {ρ τ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hτ : ρ < τ) (hτ_nonneg : 0 ≤ τ) :
    ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
  rcases h.exists_bound (sub_pos.2 hτ) with ⟨C, hCpos, hC⟩
  have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    intro z
    simpa [sub_add_cancel] using (hC z)
  exact Real.log_growth_of_norm_le_exp_mul_rpow (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
    (fun z => by linarith [norm_nonneg z]) hnorm

/-- Finite order is invariant under translation of the input. -/
theorem comp_add_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z + c)) := by
  apply of_orderLE (f := fun z : ℂ ↦ f (z + c)) hρ
  · exact h.differentiable.comp (differentiable_id.add (differentiable_const c))
  · simpa only [one_mul] using (h.orderLE hρ).comp_mul_add 1 c

/-- Finite order is invariant under subtracting a constant from the input. -/
theorem comp_sub_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z - c)) := by
  simpa [sub_eq_add_neg] using h.comp_add_const hρ (-c)

/-- A finite-order entire function has the summability needed for the genus
`⌊ρ⌋` divisor canonical product. -/
theorem summable_norm_inv_pow_divisorZeroIndex₀ {ρ : ℝ} {f : ℂ → ℂ}
    (h : EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, _hτ_lt, hτ_nonneg, hfloorτ⟩
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    h.exists_log_growth hτ hτ_nonneg
  have hsummable :=
    summable_norm_inv_pow_divisorZeroIndex₀_of_growth
      (f := f) (ρ := τ) hτ_nonneg h.differentiable hgrowthτ
  simpa [hfloorτ] using hsummable

end EntireOfOrderAtMost

theorem hadamard_factorization_of_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  let hentire : Differentiable ℂ f := horder.differentiable
  set m : ℕ := Nat.floor ρ
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    horder.exists_log_growth hτ hτ_nonneg
  rcases hadamard_factorization_of_growth (f := f) (ρ := τ) hτ_nonneg
      hentire hnot hgrowthτ with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, hfloorτ] using hdeg
  · intro z
    simpa [m, hfloorτ] using hfac z

/-- Reindexed form of `hadamard_factorization_of_order`, for any index type equivalent to the
nonzero divisor indices. -/
theorem hadamard_factorization_of_order_reindex {ι : Type*} {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ι ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            (∏' i : ι, weierstrassFactor (Nat.floor ρ)
              (z / divisorZeroIndex₀_val (e i))) := by
  classical
  rcases hadamard_factorization_of_order (f := f) (ρ := ρ) hρ hnot horder with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [divisorCanonicalProduct_eq_tprod_of_equiv (m := Nat.floor ρ)
      (f := f) (U := Set.univ) e z] using hfac z

/-- Sequence-indexed form of `hadamard_factorization_of_order`, for an enumeration of the nonzero
divisor indices by `ℕ`.

This reindexes `divisorZeroIndex₀ f`; it is not the prescribed-zero existence theorem from
Tao's Theorem 15. -/
theorem hadamard_factorization_of_order_sequence {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ℕ ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            Complex.canonicalProduct (Nat.floor ρ)
              (fun n : ℕ => divisorZeroIndex₀_val (e n)) z := by
  classical
  rcases hadamard_factorization_of_order_reindex (f := f) (ρ := ρ) hρ hnot horder e with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [Complex.canonicalProduct_def] using hfac z

/-- Centered finite-order Hadamard factorization.  This is derived from the origin-centered theorem
by translating `f` by `c`; the product indexes zeros away from the center in centered
coordinates. -/
theorem hadamard_factorization_of_order_centered {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            divisorCanonicalProduct (Nat.floor ρ) (fun w : ℂ => f (w + c))
              (Set.univ : Set ℂ) (z - c) := by
  classical
  let g : ℂ → ℂ := fun w : ℂ => f (w + c)
  have hnot_g : ∃ w : ℂ, g w ≠ 0 := by
    rcases hnot with ⟨z, hz⟩
    refine ⟨z - c, ?_⟩
    simpa [g] using hz
  have horder_g : EntireOfOrderAtMost ρ g :=
    horder.comp_add_const hρ c
  rcases hadamard_factorization_of_order (f := g) (ρ := ρ) hρ hnot_g horder_g with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  have h := hfac (z - c)
  have horder0 : analyticOrderNatAt g 0 = analyticOrderNatAt f c := by
    simpa [g] using analyticOrderNatAt_comp_add_const f c
  simpa [g, horder0] using h

/-- Reindexed centered finite-order Hadamard factorization, for any index type equivalent to the
centered nonzero divisor indices. -/
theorem hadamard_factorization_of_order_centered_reindex {ι : Type*} {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ι ≃ divisorZeroIndex₀ (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            (∏' i : ι, weierstrassFactor (Nat.floor ρ)
              ((z - c) / divisorZeroIndex₀_val (e i))) := by
  classical
  rcases hadamard_factorization_of_order_centered
      (f := f) (ρ := ρ) hρ c hnot horder with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [divisorCanonicalProduct_eq_tprod_of_equiv (m := Nat.floor ρ)
      (f := fun w : ℂ => f (w + c)) (U := Set.univ) e (z - c)] using hfac z

/-- Sequence-indexed centered finite-order Hadamard factorization. -/
theorem hadamard_factorization_of_order_centered_sequence {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ℕ ≃ divisorZeroIndex₀ (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            Complex.canonicalProduct (Nat.floor ρ)
              (fun n : ℕ => divisorZeroIndex₀_val (e n)) (z - c) := by
  classical
  rcases hadamard_factorization_of_order_centered_reindex
      (f := f) (ρ := ρ) hρ c hnot horder e with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [Complex.canonicalProduct_def] using hfac z

end Complex.Hadamard
