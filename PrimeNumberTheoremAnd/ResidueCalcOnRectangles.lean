module

public import Architect
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Contour.Residue.SimplePole
public import PrimeNumberTheoremAnd.Rectangle
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.Analysis.Contour.Cauchy.Rectangle


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

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂

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

attribute [blueprint
  "existsDifferentiableOn_of_bddAbove"
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
  Complex.differentiableOn_update_limUnder_of_bddAbove

attribute [blueprint
  "DifferentiableOn.vanishesOnRectangle"
  (uses := ["RectangleIntegral"])
  (title := "DifferentiableOn.vanishesOnRectangle")
  (statement := /--
  If $f$ is holomorphic on a rectangle $z$ and $w$, then the
  integral of $f$ over the rectangle with corners $z$ and $w$
  is $0$.
  -/)
  (proof := /-- This is in a Mathlib PR. -/)]
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn

attribute [blueprint
  "ResidueTheoremOnRectangleWithSimplePole"
  (uses := ["RectangleIntegral"])
  (title := "ResidueTheoremOnRectangleWithSimplePole")
  (statement := /--
  Let $\sigma_1\le\sigma_2$, $t_1\le t_2$, and let $P$ be a finite set of points in the open
  rectangle $(\sigma_1,\sigma_2)\times(t_1,t_2)$. Suppose that $f$ is continuous on the closed
  rectangle minus $P$, holomorphic on the open rectangle minus $P$, and meromorphic at each point
  of $P$. Then the integral of $f$ over the boundary of the rectangle is
  $2\pi i\sum_{p\in P}\operatorname{Res}_{s=p}f(s)$.
  In particular, if $f$ is holomorphic on a rectangle except for a simple pole at $p$, that is,
  $f = g + A/(s-p)$ with $g$ holomorphic on the rectangle and $A\in\C$, then the integral of
  $f$ over the rectangle is $2\pi i A$.
  -/)
  (proof := /--
  Excise a small disc around each pole. The integral over the boundary of the rectangle with the
  discs removed vanishes by Cauchy's theorem, and the integral over a small circle around $p$ is
  $2\pi i\operatorname{Res}_{s=p}f(s)$, computed from the Laurent expansion of $f$ at $p$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.Contour.rectangle_boundary_integral_eq_residues

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
  rw [interior_rectangle hre him] at hS
  have h := TauCeti.Contour.rectangle_boundary_integral_eq_residues hre him hS
    (by simpa [Rectangle, uIcc_of_le hre, uIcc_of_le him] using hf.continuousOn)
    (hf.mono (sdiff_subset_sdiff_left (interior_rectangle hre him ▸ interior_subset))) hmero
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, h]
  field_simp

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
lemma rectangleIntegral'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin
    (c := z.im) (a := z.re) (b := w.re) h_eq (by
      intro x hx
      constructor
      · simpa using hx
      · simp)
  have htop := HIntegral_congr_codiscreteWithin
    (c := w.im) (a := z.re) (b := w.re) h_eq (by
      intro x hx
      constructor
      · simpa using hx
      · simp)
  have hright := VIntegral_congr_codiscreteWithin
    (c := w.re) (a := z.im) (b := w.im) h_eq (by
      intro y hy
      constructor
      · simp
      · simpa using hy)
  have hleft := VIntegral_congr_codiscreteWithin
    (c := z.re) (a := z.im) (b := w.im) h_eq (by
      intro y hy
      constructor
      · simp
      · simpa using hy)
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
