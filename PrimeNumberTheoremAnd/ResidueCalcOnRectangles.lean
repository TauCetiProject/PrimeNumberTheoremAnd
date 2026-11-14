module

public import Architect
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Contour.Residue.SimplePole
public import PrimeNumberTheoremAnd.Rectangle
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle


@[expose] public section

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂

lemma HIntegral_symm :
    HIntegral f x₁ x₂ y = -HIntegral f x₂ x₁ y := integral_symm _ _

lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]

/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
@[blueprint
  (title := "RectangleIntegral")
  (statement := /--
  A RectangleIntegral of a function $f$ is one over a rectangle
  determined by $z$ and $w$ in $\C$.
  We will sometimes denote it by $\int_{z}^{w} f$.
  (There is also a primed version, which is
  $1/(2\pi i)$ times the original.)
  -/)]
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

/- An UpperUIntegral is the integral of a function over a |\_| shape. -/
@[blueprint
  (title := "UpperUIntegral")
  (statement := /--
  An UpperUIntegral of a function $f$ comes from
  $\sigma+i\infty$ down to $\sigma+iT$, over to
  $\sigma'+iT$, and back up to $\sigma'+i\infty$. -/)]
noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' T +
    I • (∫ y : ℝ in Ici T, f (σ' + y * I)) -
    I • (∫ y : ℝ in Ici T, f (σ + y * I))

/- A LowerUIntegral is the integral of a function over a |-| shape. -/
@[blueprint
  (title := "LowerUIntegral")
  (statement := /--
  A LowerUIntegral of a function $f$ comes from
  $\sigma-i\infty$ up to $\sigma-iT$, over to
  $\sigma'-iT$, and back down to $\sigma'-i\infty$.
  -/)]
noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' (-T) -
    I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) +
    I • (∫ y : ℝ in Iic (-T), f (σ + y * I))

blueprint_comment /--
It is very convenient to define integrals along vertical lines
in the complex plane, as follows.
-/
@[blueprint
  (title := "VerticalIntegral")
  (statement := /--
  Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$,
  and let $\sigma$ be a real number. Then we define
  $$\int_{(\sigma)}f(s)ds =
    \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
  -/)]
noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

blueprint_comment /--
We also have a version with a factor of $1/(2\pi i)$. -/
noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

@[blueprint
  (title := "DiffVertRect-eq-UpperLowerUs")
  (statement := /--
  The difference of two vertical integrals and a rectangle is
  the difference of an upper and a lower U integrals.
  -/)
  (proof := /-- Follows directly from the definitions. -/)
  (proofUses := ["UpperUIntegral", "LowerUIntegral"])
  (latexEnv := "lemma")]
lemma DiffVertRect_eq_UpperLowerUs {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
    VerticalIntegral f σ' - VerticalIntegral f σ -
      RectangleIntegral f (σ - I * T) (σ' + I * T) =
    UpperUIntegral f σ σ' T - LowerUIntegral f σ σ' T := by
  rw [verticalIntegral_split_three (-T) T f_int_σ, verticalIntegral_split_three (-T) T f_int_σ']
  simp only [RectangleIntegral, UpperUIntegral, LowerUIntegral]
  simp only [sub_re, mul_re, I_re, add_re, ofReal_re, I_im, ofReal_im, sub_im, mul_im, add_im]
  ring_nf
  abel

@[blueprint
  (title := "existsDifferentiableOn-of-bddAbove")
  (statement := /--
  If $f$ is differentiable on a set $s$ except at $c\in s$,
  and $f$ is bounded above on $s\setminus\{c\}$, then there
  exists a differentiable function $g$ on $s$ such that $f$
  and $g$ agree on $s\setminus\{c\}$.
  -/)
  (proof := /--
  This is the Riemann Removable Singularity Theorem, slightly
  rephrased from what's in Mathlib. (We don't care what the
  function $g$ is, just that it's holomorphic.)
  -/)]
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      DifferentiableOn ℂ g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

@[blueprint
  (title := "DifferentiableOn.vanishesOnRectangle")
  (statement := /--
  If $f$ is holomorphic on a rectangle $z$ and $w$, then the
  integral of $f$ over the rectangle with corners $z$ and $w$
  is $0$.
  -/)
  (proof := /-- This is in a Mathlib PR. -/)]
theorem DifferentiableOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : DifferentiableOn ℂ f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, sub_neg_eq_add, smul_neg, sub_neg_eq_add,
    ← sub_eq_add_neg, neg_add_eq_sub, sub_add_eq_add_sub]

theorem rectangleIntegral_symm_re (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = -RectangleIntegral f z w := by
  simp only [RectangleIntegral, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add, neg_sub, ← sub_eq_zero, sub_zero]
  rw [HIntegral_symm (y := z.im), HIntegral_symm (y := w.im)]
  abel

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem DifferentiableOn.rectangleBorderIntegrable'
    (hf : DifferentiableOn ℂ f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem DifferentiableOn.rectangleBorderIntegrable (hf : DifferentiableOn ℂ f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

/-- Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function
`f : ℂ → ℂ` so that both `(t : ℝ) ↦ f(t + y₀ * I)` and
`(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`. -/
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel

lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module

lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

set_option linter.style.multiGoal false in
lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : DifferentiableOn ℂ f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  linear_combination (norm := abel) h₁ + h₂ + h₃ + h₄ + h₅ + h₆ + h₇ + h₈

blueprint_comment /--
The next lemma allows to zoom a big rectangle down to a small
square, centered at a pole.
-/
/-- Given `f` holomorphic on a rectangle `z` and `w` except at
a point `p`, the integral of `f` over the rectangle with
corners `z` and `w` is the same as the integral of `f` over a
small square centered at `p`. -/
@[blueprint
  (title := "RectanglePullToNhdOfPole")
  (statement := /--
  If $f$ is holomorphic on a rectangle $z$ and $w$ except at
  a point $p$, then the integral of $f$ over the rectangle
  with corners $z$ and $w$ is the same as the integral of $f$
  over a small square centered at $p$.
  -/)
  (proof := /--
  Chop the big rectangle with two vertical cuts and two
  horizontal cuts into smaller rectangles, the middle one
  being the desired square. The integral over each of the
  outer rectangles vanishes, since $f$ is holomorphic there.
  (The constant $c$ being ``small enough'' here just means
  that the inner square is strictly contained in the big
  rectangle.)
  -/)
  (latexEnv := "lemma")]
lemma RectanglePullToNhdOfPole [CompleteSpace E] {z w p : ℂ}
    (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) (fHolo : DifferentiableOn ℂ f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one, SmallSquareInRectangle hp]
  intro c ⟨cpos, _⟩ hc
  simp_rw [mul_comm I]
  exact RectanglePullToNhdOfPole' (by simp_all [cpos.le])
    (square_mem_nhds p (ne_of_gt cpos)) hc fHolo

lemma RectanglePullToNhdOfPole'' [CompleteSpace E] {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : DifferentiableOn ℂ f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral' f z w = RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [RectanglePullToNhdOfPole zRe_le_wRe zIm_le_wIm pInRectInterior fHolo] with c h
  simp_rw [RectangleIntegral', h]

-- The local totalized four-edge integral agrees with the native closed-rectangle residue
-- calculation under the stated differentiability hypotheses. No extension outside the rectangle
-- or normalization of the original representative at its singularities is needed.
private lemma rectangleIntegral'_eq_native_sum_residue
    {f : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hS : ∀ p ∈ S, p ∈ interior (Rectangle z w))
    (hf : DifferentiableOn ℂ f (Rectangle z w \ (S : Set ℂ)))
    (hmero : ∀ p ∈ S, MeromorphicAt f p) :
    RectangleIntegral' f z w = ∑ p ∈ S, TauCeti.Contour.residue f p := by
  let D := TauCeti.Contour.PolarPartDecomposition.ofMeromorphic hf hmero
  have hoff : ∀ x ∈ frontier (Rectangle z w), x ∉ (S : Set ℂ) := by
    intro x hx hxS
    exact disjoint_left.1 disjoint_interior_frontier (hS x hxS) hx
  have hcont : ContinuousOn f (frontier (Rectangle z w)) :=
    hf.continuousOn.mono fun x hx ↦
      ⟨(isClosed_rectangle z w).frontier_subset hx, hoff x hx⟩
  have h := D.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum
    (isPiecewiseC1On_rectBoundary z w) (fun _ _ ↦ rectBoundary_mem_rectangle _)
    (by simp) (fun _ _ ↦ hoff _ (rectBoundary_mem_frontier _))
  rw [integral_rectBoundary hcont,
    integral_rectBoundary (D.analyticRemainder_differentiableOn.continuousOn.mono
      (isClosed_rectangle z w).frontier_subset),
    integral_boundary_rect_eq_zero_of_differentiableOn
      D.analyticRemainder z w D.analyticRemainder_differentiableOn, zero_add] at h
  rw [Finset.sum_congr rfl (fun p hp ↦ by
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_one (by
      simpa only [interior_rectangle hre him] using hS p hp), one_mul])] at h
  have hraw : RectangleIntegral f z w =
      2 * (π : ℂ) * I * ∑ p ∈ S, TauCeti.Contour.residue f p := h
  rw [RectangleIntegral', hraw, smul_eq_mul, one_div, ← mul_assoc,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y - I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  simp [RectangleIntegral, HIntegral, VIntegral, smul_add, smul_sub, smul_smul, mul_comm]

theorem RectangleIntegral.const_mul' (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral' (fun s => c • f s) z w = c • RectangleIntegral' f z w := by
  simp [RectangleIntegral', RectangleIntegral.const_smul, smul_smul]
  ring_nf

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = arctan (x₂ / y) - arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option backward.isDefEq.respectTransparency false in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (arctan (x₂ / y) - arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (arctan (y₂ / -x) - arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := fun h ↦ hx (by simpa using congrArg re h)
    have e2 : y + I * ↑(-x) ≠ 0 := fun h ↦ hx (by simpa using congrArg im h)
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  have hS : ∀ q ∈ ({p} : Finset ℂ), q ∈ interior (Rectangle z w) := by
    simpa only [Finset.mem_singleton, forall_eq] using
      mem_interior_iff_mem_nhds.mpr pInRectInterior
  have hf : DifferentiableOn ℂ (fun s : ℂ ↦ c / (s - p)) (Rectangle z w \ {p}) :=
    (differentiableOn_const c).div (differentiableOn_id.sub_const p)
      (fun s hs ↦ sub_ne_zero.mpr hs.2)
  have hmero (q : ℂ) : MeromorphicAt (fun s : ℂ ↦ c / (s - p)) q :=
    analyticAt_const.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hres : TauCeti.Contour.residue (fun s : ℂ ↦ c / (s - p)) p = c := by
    simpa only [Nat.zero_add, pow_one, ↓reduceIte] using
      TauCeti.Contour.residue_const_div_sub_pow c p 0
  have h := rectangleIntegral'_eq_native_sum_residue (f := fun s : ℂ ↦ c / (s - p))
    (S := {p}) zRe_le_wRe zIm_le_wIm hS (by simpa using hf) (fun q _ ↦ hmero q)
  simpa only [Finset.sum_singleton, hres] using h

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  have hp : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le (h1.trans h3).le,
      uIoo_of_le (h2.trans h4).le]
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  have h := ResidueTheoremInRectangle (c := c) (h1.trans h3).le (h2.trans h4).le hp
  simp only [RectangleIntegral', smul_eq_mul, sub_zero, one_div] at h
  calc
    RectangleIntegral (fun s ↦ c / s) z w = (2 * π * I : ℂ) * c := by
      simpa only [mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero] using
        congrArg (fun a : ℂ ↦ (2 * π * I : ℂ) * a) h
    _ = 2 * I * π * c := by ring

@[blueprint
  (title := "ResidueTheoremAtOrigin")
  (statement := /--
  The rectangle (square) integral of $f(s) = 1/s$ with
  corners $-1-i$ and $1+i$ is equal to $2\pi i$.
  -/)
  (proof := /--
  This is a special case of the more general result above. -/)
  (latexEnv := "lemma")]
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  rw [RectangleIntegral', ResidueTheoremAtOrigin']
  all_goals simp [field]

@[blueprint
  (title := "ResidueTheoremOnRectangleWithSimplePole")
  (statement := /--
  Suppose that $f$ is a holomorphic function on a rectangle,
  except for a simple pole at $p$.
  By the latter, we mean that there is a function $g$
  holomorphic on the rectangle such that,
  $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of
  $f$ over the rectangle is $A$.
  -/)
  (proof := /--
  Replace $f$ with $g + A/(s-p)$ in the integral.
  The integral of $g$ vanishes by
  Lemma \ref{DifferentiableOn.vanishesOnRectangle}.
  The canonical polar-part residue formula evaluates $A/(s-p)$: the native rectangle
  boundary has winding number one about its interior point $p$, and its residue is $A$.
  -/)
  (latexEnv := "lemma")]
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : DifferentiableOn ℂ g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : DifferentiableOn ℂ (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    DifferentiableOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)

theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : DifferentiableOn ℂ f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  have hpint : p ∈ interior (Rectangle z w) := mem_interior_iff_mem_nhds.mpr pInRectInterior
  have hdiff : ∀ᶠ s in 𝓝[≠] p, DifferentiableAt ℂ f s := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_interior.mem_nhds hpint),
      self_mem_nhdsWithin] with s hs hsp
    refine (fHolo s ⟨interior_subset hs, hsp⟩).differentiableAt ?_
    filter_upwards [isOpen_interior.mem_nhds hs,
      isClosed_singleton.isOpen_compl.mem_nhds hsp] with t ht htp
    exact ⟨interior_subset ht, htp⟩
  have hsmall : (fun s : ℂ ↦ s - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).mpr (tendsto_sub_nhds_zero_iff.mpr
      (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hzero : Tendsto
      (fun s : ℂ ↦ (s - p) * (f s - A / (s - p))) (𝓝[≠] p) (𝓝 0) := by
    apply (isLittleO_one_iff ℂ).mp
    simpa only [Pi.mul_apply, Pi.one_apply, one_mul, Pi.sub_apply] using
      hsmall.mul_isBigO near_p
  have hlim : Tendsto (fun s : ℂ ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A) := by
    have heq : (fun s : ℂ ↦ (s - p) * f s) =ᶠ[𝓝[≠] p]
        fun s ↦ (s - p) * (f s - A / (s - p)) + A := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsp : s - p ≠ 0 := sub_ne_zero.mpr hs
      field_simp
      ring
    simpa only [zero_add] using (hzero.add_const A).congr' heq.symm
  have hmero := TauCeti.Contour.meromorphicAt_of_tendsto_sub_mul hdiff hlim
  have hres : TauCeti.Contour.residue f p = A :=
    TauCeti.Contour.residue_eq_of_tendsto_sub_mul hmero hlim
  have heq := rectangleIntegral'_eq_native_sum_residue (S := {p})
    zRe_le_wRe zIm_le_wIm (by simpa using hpint) (by simpa using fHolo)
    (by simpa using hmero)
  simpa only [Finset.sum_singleton, hres] using heq

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

/-- Every pole of `f` in `s` is at most simple: the meromorphic order is `≥ -1` everywhere on `s`
(no poles of order `≤ -2`).

For meromorphic germs, the limit defining `residue` below agrees with the native residue under
this condition. The native polar-part constructor supports higher-order poles, but the rectangle
formula below needs the at-most-simple-pole condition to identify its coefficients.

It holds in the intended applications, such as logarithmic derivatives. -/
def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

/-- **Placeholder definition — valid only for simple poles.** The residue of `f` at `z₀`, defined
as the simple-pole limit `lim_{z → z₀} (z - z₀) · f z` (matching the convention of
`Phi_circ.residue` / `Phi_star.residue`). At a point of analyticity this is `0` and at a simple
pole it is the usual residue, but at a higher-order or essential singularity the limit diverges
and this returns a junk value.

The native `TauCeti.Contour.residue` is the general meromorphic residue. The limit defining
`residue` agrees with it under the meromorphic, at-most-simple-pole hypotheses used below.
The two definitions can disagree outside the stated hypotheses. The rectangle formula below
uses their agreement only under those hypotheses. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

/-- The sum of residues of `f` over a region `S`, as a `tsum` over `S`. Points of analyticity
contribute `0`, so this is effectively the sum over the poles of `f` in `S`; when finitely many
poles lie in `S` the `tsum` equals the finite sum of their residues, regardless of `|S|`. (With
infinitely many poles, summability must be assumed for the value to be meaningful.) -/
noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z

lemma residue_eq_of_tendsto {f : ℂ → ℂ} {p c : ℂ}
    (h : Filter.Tendsto (fun z ↦ (z - p) * f z) (nhdsWithin p {p}ᶜ) (nhds c)) :
    residue f p = c := by
  unfold residue
  exact h.limUnder_eq

lemma residue_analyticAt_eq_zero {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 := by
  apply residue_eq_of_tendsto
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - p) (nhdsWithin p {p}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hf' : Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) :=
    hf.continuousAt.continuousWithinAt.tendsto
  simpa using hsub.mul hf'

lemma simplePole_sub_residue_isBigO_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (-1 : ℤ)) :
    (f - (fun z ↦ residue f p / (z - p))) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hres : residue f p = g p :=
    residue_eq_of_tendsto (hg_analytic.continuousAt.continuousWithinAt.tendsto.congr'
      (show (fun z ↦ (z - p) * f z) =ᶠ[nhdsWithin p {p}ᶜ] g from by
        filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
        simp [hz, sub_ne_zero.mpr hz_ne]).symm)
  have hdslope : (fun z ↦ (z - p)⁻¹ * (g z - g p)) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
    have hcont : ContinuousAt (dslope g p) p :=
      continuousAt_dslope_same.2 hg_analytic.differentiableAt
    have hbig : dslope g p =O[nhds p] (1 : ℂ → ℂ) :=
      hcont.norm.isBoundedUnder_le.isBigO_one ℂ
    have hbig_ne : dslope g p =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) :=
      IsBigO.mono hbig inf_le_left
    simpa [slope] using! hbig_ne.congr' (dslope_eventuallyEq_slope_nhdsNE (f := g) (a := p)) .rfl
  refine hdslope.congr' ?_ .rfl
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
  simp [hz, hres, div_eq_mul_inv, sub_eq_add_neg]; ring

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)
private lemma intervalIntegral_congr_ae_of_codiscreteWithin_along_path
    {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    ∫ x in a..b, f (p x) = ∫ x in a..b, g (p x) := by
  refine intervalIntegral.integral_congr_ae_restrict (μ := volume) ?_
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (p x) = g (p x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hp_an.preimage_mem_codiscreteWithin hp_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hp_maps hx) heq))

-- Non-constancy of horizontal paths `x ↦ x + h * I`.
private lemma horizontalPath_not_eventuallyConst (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * Complex.I)
  have hconst : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

-- Non-constancy of vertical paths `y ↦ r + y * I`.
lemma verticalPath_not_eventuallyConst (r : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) Complex.I x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I).const_add (r : ℂ)
  have hconst : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact Complex.I_ne_zero (hpath.unique hconst)

-- Helper for horizontal integral congruence on codiscrete set
private lemma HIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {a b c : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ x ∈ Set.uIcc a b, (↑x + ↑c * Complex.I) ∈ R) :
    HIntegral f a b c = HIntegral g a b c := by
  unfold HIntegral
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
    (fun x _ ↦ horizontalPath_not_eventuallyConst c x) hmaps

-- Helper for vertical integral congruence on codiscrete set
private lemma VIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {c a b : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ y ∈ Set.uIcc a b, (↑c + ↑y * Complex.I) ∈ R) :
    VIntegral f c a b = VIntegral g c a b := by
  unfold VIntegral; simp only [smul_eq_mul]; congr 1
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun x _ ↦ verticalPath_not_eventuallyConst c x) hmaps

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.
private lemma rectangleIntegral'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_left_im z w)
  have htop := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_right_im z w)
  have hright := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_right_re z w)
  have hleft := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_left_re z w)
  unfold RectangleIntegral'; congr 1; unfold RectangleIntegral
  rw [hbot, htop, hright, hleft]

/-- The Residue Theorem on a rectangle for functions with simple poles. -/
lemma RectangleIntegral'_eq_sumResiduesIn {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' f z w = sumResiduesIn f (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}) := by
  classical
  let R : Set ℂ := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let S := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  have hmem (p : ℂ) : p ∈ S ↔ p ∈ poles := f_poles_finite.mem_toFinset
  have hborder : RectangleBorder z w = frontier R := by
    ext p
    simp only [R, RectangleBorder, frontier_rectangle, mem_union, mem_reProdIm,
      mem_insert_iff, mem_singleton_iff]
    tauto
  have hS (p : ℂ) (hp : p ∈ S) : p ∈ interior R := by
    have hpR := (hmem p).mp hp
    rw [← self_sdiff_frontier]
    exact ⟨hpR.1, fun hfr ↦ Set.disjoint_right.mp f_no_poles_boundary hpR.2
      (hborder.symm ▸ hfr)⟩
  have hnf : MeromorphicNFOn fNF R := meromorphicNFOn_toMeromorphicNFOn f R
  have hmero : MeromorphicOn fNF R := hnf.meromorphicOn
  have hord (p : ℂ) (hp : p ∈ R) : meromorphicOrderAt fNF p = meromorphicOrderAt f p :=
    meromorphicOrderAt_toMeromorphicNFOn f_mero hp
  have hdiff : DifferentiableOn ℂ fNF (R \ (S : Set ℂ)) := by
    intro p hp
    apply ((hnf hp.1).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_).differentiableAt.differentiableWithinAt
    rw [hord p hp.1]
    exact le_of_not_gt fun hneg ↦ hp.2 ((hmem p).mpr ⟨hp.1, hneg⟩)
  have hscalar := rectangleIntegral'_eq_native_sum_residue zRe_le_wRe zIm_le_wIm
    hS hdiff (fun p hp ↦ hmero p ((hmem p).mp hp).1)
  have hres (p : ℂ) (hp : p ∈ S) : TauCeti.Contour.residue fNF p = residue f p := by
    have hpR := ((hmem p).mp hp).1
    rw [TauCeti.Contour.residue_congr_nhdsNE
      (f_mero.toMeromorphicNFOn_eq_self_on_nhdsNE hpR)]
    exact ((TauCeti.Contour.tendsto_sub_mul_nhds_residue (f_mero p hpR)
      (f_simple_poles p hpR)).limUnder_eq).symm
  rw [rectangleIntegral'_toMeromorphicNFOn_eq f_mero, hscalar,
    Finset.sum_congr rfl hres]
  have hset : poles = (S : Set ℂ) := f_poles_finite.coe_toFinset.symm
  change S.sum (residue f) = ∑' p : poles, residue f p
  rw [hset, tsum_fintype, ← Finset.sum_coe_sort S]
  rfl

lemma residue_eq_zero_of_not_pole_of_meromorphicAt {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 := by
  apply residue_eq_of_tendsto
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hs_mero hs_not_pole
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - s) (nhdsWithin s {s}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa using hsub.mul hc

lemma sumResiduesIn_inter_eq_of_set_eq {F : ℂ → ℂ} {Rn S2 P : Set ℂ}
    (h_set_eq : Rn ∩ P = S2 ∩ P)
    (h_residue_zero : ∀ s ∈ S2, s ∉ P → residue F s = 0) :
    sumResiduesIn F (Rn ∩ P) = sumResiduesIn F S2 := by
  rw [sumResiduesIn, sumResiduesIn, tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro s
  by_cases hs_S2 : s ∈ S2
  · by_cases hs_pole : s ∈ P
    · have hs_rect_pole : s ∈ Rn ∩ P := h_set_eq.symm ▸ ⟨hs_S2, hs_pole⟩
      simp [hs_S2, hs_rect_pole]
    · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_pole hs.2
      have hres0 : residue F s = 0 := h_residue_zero s hs_S2 hs_pole
      simp [hs_S2, hs_not_rect_pole, hres0]
  · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_S2 (h_set_eq ▸ hs).1
    simp [hs_S2, hs_not_rect_pole]
