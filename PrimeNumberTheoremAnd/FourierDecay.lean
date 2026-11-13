module

public import Architect
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import PrimeNumberTheoremAnd.Fourier

/-!
# Fourier decay for functions of bounded variation

The Dirichlet-series and Wiener--Ikehara arguments are supplied by Mathlib and Tau Ceti.
This module retains the bounded-variation estimates used by the explicit CH2 estimates.
-/

@[expose] public section


open Real MeasureTheory FourierTransform Set

private lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

@[blueprint "prelim-decay-2"
  (title := "Preliminary decay bound II")
  (statement := /--
If $\psi:\R \to \C$ is absolutely integrable and of bounded variation, then
$$ |\hat \psi(u)| \leq \| \psi \|_{TV} / 2\pi |u| $$
for all non-zero $u \in \R$.
  -/)
  (proof := /-- By Lebesgue--Stiejtes integration by parts we have
$$ 2\pi i u \hat \psi(u) = \int _\R e(-tu) d\psi(t)$$
and the claim then follows from the triangle inequality. -/)
  (latexEnv := "lemma")
  (discussion := 562)]
theorem prelim_decay_2 (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hvar : BoundedVariationOn ψ Set.univ)
    (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn ψ Set.univ).toReal / (2 * π * ‖u‖) := by sorry

noncomputable def AbsolutelyContinuous (f : ℝ → ℂ) : Prop := (∀ᵐ x, DifferentiableAt ℝ f x) ∧
  ∀ a b : ℝ, f b - f a = ∫ t in a..b, deriv f t

@[blueprint "prelim-decay-3"
  (title := "Preliminary decay bound III")
  (statement := /--
If $\psi:\R \to \C$ is absolutely integrable, absolutely continuous, and $\psi'$ is of bounded
variation, then
$$ |\hat \psi(u)| \leq \| \psi' \|_{TV} / (2\pi |u|)^2$$
for all non-zero $u \in \R$.
  -/)
  (proof := /-- Should follow from previous lemma. -/)
  (proofUses := ["prelim-decay-2"])
  (latexEnv := "lemma")
  (discussion := 563)]
theorem prelim_decay_3 (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (habscont : AbsolutelyContinuous ψ)
    (hvar : BoundedVariationOn (deriv ψ) Set.univ) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 := by sorry

@[blueprint "decay-alt"
  (title := "Decay bound, alternate form")
  (statement := /--
If $\psi:\R \to \C$ is absolutely
integrable, absolutely continuous, and $\psi'$ is of bounded variation, then
$$ |\hat \psi(u)| \leq ( \|\psi\|_1 + \| \psi' \|_{TV} / (2\pi)^2) / (1+|u|^2)$$
for all $u \in \R$.  -/)
  (proof := /-- Should follow from previous lemmas. -/)
  (proofUses := ["prelim-decay-3"])
  (latexEnv := "lemma")
  (discussion := 564)]
theorem decay_alt (ψ : ℝ → ℂ) (hψ : Integrable ψ) (habscont : AbsolutelyContinuous ψ)
    (hvar : BoundedVariationOn (deriv ψ) Set.univ) (u : ℝ) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤
      ((∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2) /
        (1 + ‖u‖ ^ 2) := by
  rw [le_div_iff₀' <| one_add_sq_pos ‖u‖]
  by_cases hu : u = 0
  · subst hu
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      one_mul]
    calc ‖𝓕 ψ 0‖ ≤ ∫ t, ‖ψ t‖ := VectorFourier.norm_fourierIntegral_le_integral_norm ..
      _ ≤ (∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by
          have : 0 ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by positivity
          linarith
  · have bound1 : ‖𝓕 ψ u‖ ≤ ∫ t, ‖ψ t‖ := VectorFourier.norm_fourierIntegral_le_integral_norm ..
    have bound2 : ‖𝓕 ψ u‖ ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 :=
      prelim_decay_3 ψ hψ habscont hvar u hu
    have : (2 * π * ‖u‖) ^ 2 = (2 * π) ^ 2 * ‖u‖ ^ 2 := by ring
    calc (1 + ‖u‖ ^ 2) * ‖𝓕 ψ u‖
        = ‖𝓕 ψ u‖ * 1 + ‖𝓕 ψ u‖ * ‖u‖ ^ 2 := by ring
      _ ≤ (∫ t, ‖ψ t‖) * 1 +
            (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2 * ‖u‖ ^ 2 := by
          gcongr
      _ = (∫ t, ‖ψ t‖) + (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π) ^ 2 := by
          rw [mul_one, this, div_mul_eq_div_div]
          congr 1
          rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 <| norm_ne_zero_iff.mpr hu)]

