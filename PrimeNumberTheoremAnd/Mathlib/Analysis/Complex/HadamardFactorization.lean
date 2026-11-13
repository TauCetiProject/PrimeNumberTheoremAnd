/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
public import TauCeti.Analysis.Complex.DivisorFactorization
public import TauCeti.Analysis.Convex.SimplyConnected
public import Mathlib.Analysis.Meromorphic.NormalForm



/-!
# The Hadamard quotient

If `f` is entire, nontrivial, and the divisor-indexed canonical product of genus `m` converges,
then there is an entire zero-free function `H` with

`f z = H z * z ^ (ord₀ f) * divisorCanonicalProduct m f univ z`.

The denominator has the same divisor as `f`. Tau Ceti's divisor-factorization theorem
therefore supplies an entire logarithm of the quotient, and `H` is its exponential.

The quotient construction here is centered at `0`.  General-center API is derived downstream by
translating the function; see `hadamard_factorization_of_order_centered`.

## Main results

* `exists_entire_nonzero_hadamardQuotient` : existence of `H`
* `hadamardDenom`, `differentiable_hadamardDenom`

Downstream: `HadamardFactorization/Summability` (Jensen counting), `Growth`, and `Order`
assemble the full factorization `hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/

@[expose] public section

namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

/-- The denominator in the Hadamard quotient construction. -/
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

/-- The denominator in the Hadamard quotient construction, centered at `c`. -/
noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)

/-- The Hadamard quotient construction, centered at `c`. -/
noncomputable def centeredHadamardQuotient (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / centeredHadamardDenom m c f z

@[simp]
theorem centeredHadamardDenom_center_eq_one {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c = 0) :
    centeredHadamardDenom m c f c = 1 := by
  simp [centeredHadamardDenom, h, sub_self, divisorCanonicalProduct_zero, pow_zero]

@[simp]
theorem centeredHadamardDenom_center_eq_zero {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c ≠ 0) : centeredHadamardDenom m c f c = 0 := by
  have hn : 0 < analyticOrderNatAt f c := by
    exact Nat.pos_of_ne_zero h
  simp [centeredHadamardDenom, sub_self, zero_pow hn.ne']

theorem differentiable_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
  intro z
  have hdiffOn :
      DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  exact (hdiffOn z (by simp)).differentiableAt (by simp)

theorem analyticAt_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  (differentiable_divisorCanonicalProduct_univ m f h_sum).analyticAt z

theorem differentiable_hadamardDenom (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (hadamardDenom m f) := by
  have hcprod : Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  simpa [hadamardDenom] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod

theorem hadamardDenom_ne_zero_at {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) {z : ℂ} (hz : f z ≠ 0) : hadamardDenom m f z ≠ 0 := by
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    fun w ↦ (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w (hf).analyticAt).not.mpr
      (Function.ne_iff.mpr hnot)
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
    exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [hadamardDenom, hord0, divisorCanonicalProduct_zero]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        exact differentiable_divisorCanonicalProduct_univ m f h_sum
      have hcprod_not_top :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (hcprod_entire).analyticAt).not.mpr
          (Function.ne_iff.mpr ⟨0, by simp [divisorCanonicalProduct_zero]⟩)
      have hcprod_cast :
          (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
        have :
            (analyticOrderNatAt
              (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne

lemma analyticOrderNatAt_divisorCanonicalProduct_zero
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 := by
  have hcprod_entire :
      Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  have hcprod_not_top :
      analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (hcprod_entire).analyticAt).not.mpr
      (Function.ne_iff.mpr ⟨0, by simp [divisorCanonicalProduct_zero]⟩)
  have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : divisorCanonicalProduct m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [divisorCanonicalProduct_zero]
  have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        0 := by
    simp [hcast, this]
  exact_mod_cast this

theorem analyticOrderNatAt_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (hadamardDenom m f) z = analyticOrderNatAt f z := by
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (differentiable_id.pow (analyticOrderNatAt f 0)).analyticAt).not.mpr
        (Function.ne_iff.mpr ⟨1, by simp⟩)
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum 0
    have hcprod0 :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
      analyticOrderNatAt_divisorCanonicalProduct_zero (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using
          (divisor_univ_eq_analyticOrderNatAt_int
            (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ))
            (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 :
        analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using! (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (differentiable_divisorCanonicalProduct_univ m f h_sum).analyticAt).not.mpr
          (Function.ne_iff.mpr ⟨0, by simp [divisorCanonicalProduct_zero]⟩)
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (differentiable_id.pow (analyticOrderNatAt f 0)).analyticAt).not.mpr
        (Function.ne_iff.mpr ⟨1, by simp⟩)
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
        (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
    have hcprod_not_top :
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (differentiable_divisorCanonicalProduct_univ m f h_sum).analyticAt).not.mpr
        (Function.ne_iff.mpr ⟨0, by simp [divisorCanonicalProduct_zero]⟩)
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]

theorem divisor_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  ext z
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (hadamardDenom m f) z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := hadamardDenom m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := f) hf_entire z)
  simp [hden, hfz, analyticOrderNatAt_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum) z]

/-- The Hadamard quotient is an entire zero-free function when the canonical product has the
required convergence.  The hypothesis `hnot` excludes the identically zero function, for which the
discrete divisor/order bookkeeping used by Hadamard factorization is not the intended API. -/
theorem exists_entire_nonzero_hadamardQuotient
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  have hden : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom m f h_sum
  obtain ⟨z₁, hz₁⟩ := hnot
  have hden₁ : hadamardDenom m f z₁ ≠ 0 :=
    hadamardDenom_ne_zero_at hf ⟨z₁, hz₁⟩ h_sum hz₁
  obtain ⟨L, hL, heq⟩ := TauCeti.exists_differentiableOn_eqOn_mul_exp_of_divisor_eq
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ
    (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hden.differentiableOn.analyticOnNhd isOpen_univ)
    ⟨z₁, Set.mem_univ _, hz₁⟩ ⟨z₁, Set.mem_univ _, hden₁⟩
    (divisor_hadamardDenom_eq m hf h_sum).symm
  refine ⟨fun z ↦ exp (L z), (differentiableOn_univ.mp hL).cexp,
    fun z ↦ exp_ne_zero _, fun z ↦ ?_⟩
  simpa only [hadamardDenom, mul_assoc, mul_comm, mul_left_comm] using heq (Set.mem_univ z)


/-!
## Boundedness on compact annuli (away from `z₀`)

On any compact set separated from `z₀`, the quotient by `(z - z₀)^k` is bounded.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_closedBall_diff_ball
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    BddAbove
      (norm ∘
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) ''
          (Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁)) := by
  set K : Set ℂ := Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁
  have hK : IsCompact K := by
    have hclosed : IsClosed (Metric.ball z₀ r₁)ᶜ := Metric.isOpen_ball.isClosed_compl
    simpa [K, Set.sdiff_eq] using (isCompact_closedBall z₀ r₂).inter_right hclosed
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hz hzz
    have hzBall : z ∈ Metric.ball z₀ r₁ := by
      simpa [hzz] using (Metric.mem_ball_self hr₁ : z₀ ∈ Metric.ball z₀ r₁)
    have hz' : z ∈ Metric.closedBall z₀ r₂ ∧ z ∉ Metric.ball z₀ r₁ := by
      simpa [K, Set.sdiff_eq] using hz
    exact hz'.2 hzBall
  have hdiff : DifferentiableOn ℂ
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
        ((Set.univ : Set ℂ) \ {z₀}) :=
    differentiableOn_divisorCanonicalProduct_div_pow_sub (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  have hcont : ContinuousOn
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) K := by
    refine (hdiff.mono ?_).continuousOn
    intro z hz
    refine ⟨by simp, ?_⟩
    exact hKz z hz
  have hKimg :
      IsCompact
        ((fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) '' K) :=
    hK.image_of_continuousOn hcont
  rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨w, hwK, rfl⟩
  exact hC _ ⟨w, hwK, rfl⟩

end Complex.Hadamard
