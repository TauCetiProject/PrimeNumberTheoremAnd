module

public import Architect
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.WeakPNT
public import PrimeNumberTheoremAnd.Defs
public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.SpecialFunctions.LogIntegral
public import TauCeti.NumberTheory.PrimeCounting
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics



@[expose] public section


open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact notMem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

@[blueprint
  (title := "finsum-range-eq-sum-range")
  (statement := /--
   For any arithmetic function $f$ and real number $x$, one has
  $$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
  and
  $$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
  -/)
  (proof := /-- Straightforward. -/)
  (latexEnv := "lemma")]
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero


blueprint_comment /--
\label{WeakPNT}
The Chebyshev function satisfies $\psi(x) \sim x$.
This is Mathlib's `Chebyshev.isEquivalent_psi_id`.
-/

blueprint_comment /--
\label{chebyshev-asymptotic}
One has $\sum_{p \leq x} \log p = x + o(x)$.
This is Mathlib's `Chebyshev.isEquivalent_theta_id`.
-/

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  have hReal :
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ~[atTop]
        fun x ↦ x := by
    have h x : ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ) = θ x := by
      rw [Chebyshev.theta_eq_sum_Icc]
      have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
        (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr (Nat.le_floor hpx)
      calc ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)
          = ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), log (p : ℝ) :=
            finsum_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
        _ = ∑ p ∈ hfin.toFinset, log (p : ℝ) := finsum_mem_eq_finite_toFinset_sum _ hfin
        _ = _ := sum_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
            mem_filter, mem_Icc, and_congr_left_iff]; exact fun hp ↦
            ⟨fun hpx ↦ ⟨Nat.zero_le _, Nat.le_floor hpx⟩, fun ⟨_, hpn⟩ ↦
              (le_or_gt 0 x).elim
                (fun hx ↦ (Nat.floor_le hx).trans' (Nat.cast_le.mpr hpn)) fun hx ↦
                absurd (Nat.le_zero.mp (Nat.floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
                  hp.ne_zero⟩) (fun _ _ ↦ rfl)
    have heq :
        (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) =ᶠ[atTop] θ :=
      Filter.Eventually.of_forall h
    exact Chebyshev.isEquivalent_theta_id.congr_left heq.symm
  simp only [IsEquivalent,
    show (fun n : ℕ ↦ ∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : p.Prime), log (p : ℝ)) =
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ∘ Nat.cast
    from funext fun _ ↦ finsum_congr fun _ ↦ by simp]
  exact hReal.isLittleO.comp_tendsto tendsto_natCast_atTop_atTop

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := Chebyshev.isEquivalent_theta_id
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine Chebyshev.integrableOn_theta_div_id_mul_log_sq x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x


@[blueprint
  (title := "primorial-bounds")
  (statement := /--
  We have
    $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
  -/)
  (proof := /-- Exponentiate Theorem \ref{chebyshev-asymptotic}. -/)
  (latexEnv := "corollary")]
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  use (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p - x)
  constructor
  · exact Asymptotics.IsEquivalent.isLittleO Chebyshev.isEquivalent_theta_id
  intro x
  simp only [cast_prod, add_sub_cancel, exp_sum]
  apply Finset.prod_congr rfl
  intros x hx
  rw[Real.exp_log]
  rw[Finset.mem_filter] at hx
  norm_cast
  exact Nat.Prime.pos hx.right

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), p = exp (x + E x) := by
  obtain ⟨E, hE, hprod⟩ := primorial_bounds
  refine ⟨E, hE, fun x ↦ ?_⟩
  have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
    (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr <| le_floor hpx
  have heq : ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p =
      ∏ p ∈ (Iic ⌊x⌋₊).filter Prime, p := by
    calc ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p
        = ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), p :=
      finprod_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
      _ = ∏ p ∈ hfin.toFinset, p := finprod_mem_eq_finite_toFinset_prod _ hfin
      _ = _ := prod_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
          mem_filter, mem_Iic, and_congr_left_iff]; exact fun hp ↦
          ⟨le_floor, fun hpn ↦ (le_or_gt 0 x).elim
          (fun hx ↦ (Nat.floor_le hx).trans' (cast_le.mpr hpn)) fun hx ↦
          absurd (le_zero.mp (floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
          hp.ne_zero⟩) (fun _ _ ↦ rfl)
  simp only [heq, hprod]

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  have ha1 : 1 < a := lt_of_lt_of_le one_lt_two ha
  have hb1 : 1 < b := ha1.trans_le hb
  have h1 : IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹) volume a b := by
    simpa only [pow_one] using TauCeti.Real.intervalIntegrable_inv_log_pow 1 ha1 hb1
  have h2 := TauCeti.Real.intervalIntegrable_inv_log_pow 2 ha1 hb1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ TauCeti.Real.hasDerivAt_div_log
      (ha1.trans_le ((Set.uIcc_of_le hb ▸ ht).1))) (h1.sub h2)
  rw [intervalIntegral.integral_sub h1 h2] at hFTC
  simp only [div_eq_mul_inv] at hFTC
  linarith only [hFTC]

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, ite_eq_left hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.le,
    ← TauCeti.Real.logIntegral_def]
  exact (div_pos (sub_pos.mpr hx) (log_pos (one_lt_two.trans hx))).trans_le
    (TauCeti.Real.le_logIntegral hx.le)

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  have hpi := Nat.isEquivalent_primeCounting
  have hli : (fun x : ℝ ↦ ∫ t in Set.Icc 2 x, 1 / log t) ~[atTop]
      (fun x : ℝ ↦ x / log x) := by
    refine TauCeti.Real.logIntegral_isEquivalent_div_log.congr_left ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [TauCeti.Real.logIntegral_def, intervalIntegral.integral_of_le hx,
      integral_Icc_eq_integral_Ioc]
    simp only [one_div]
  have hratio := (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    simpa only [one_div] using (integral_log_inv_pos x hx).ne')).mp (hpi.trans hli.symm)
  exact (isLittleO_one_iff ℝ).mpr (by simpa only [sub_self, Pi.div_apply] using hratio.sub_const (1 : ℝ))

@[blueprint
  (title := "pi-asymp")
  (statement := /--
  There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.
  -/)
  (proof := /--
  We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev-asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
  -/)]
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  have := Chebyshev.integral_one_div_log_sq_isBigO
  rw [isBigO_iff] at this
  obtain ⟨c, hc⟩ := this
  use c
  filter_upwards [hc, eventually_ge_atTop 2] with x hc hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  apply le_trans (by apply le_norm_self)
  nth_rewrite 2 [norm_of_nonneg (by positivity)] at hc
  exact hc

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨qlog, hqlog, heq⟩ := TauCeti.Real.logIntegral_isEquivalent_div_log.exists_eq_mul
  refine ⟨fun x ↦ qlog x - 1, (isLittleO_one_iff ℝ).mpr ?_, ?_⟩
  · simpa only [sub_self] using hqlog.sub_const (1 : ℝ)
  · filter_upwards [heq, eventually_ge_atTop (2 : ℝ)] with x heq hx
    rw [show 1 + (qlog x - 1) = qlog x by ring, mul_div_assoc]
    simpa only [TauCeti.Real.logIntegral_def, intervalIntegral.integral_of_le hx,
      integral_Icc_eq_integral_Ioc, Pi.mul_apply, one_div] using heq

@[blueprint
  (title := "pi-alt")
  (statement := /--
    One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.
  -/)
  (proof := /--
  An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
  -/)
  (latexEnv := "corollary")]
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  refine ⟨fun x ↦ (log x / x) * ⌊x⌋₊.primeCounting - 1, ?_, ?_⟩
  · have hratio := (isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact (div_pos (zero_lt_one.trans hx) (log_pos hx)).ne')).mp
        Nat.isEquivalent_primeCounting
    refine (isLittleO_one_iff ℝ).mpr ?_
    convert hratio.sub_const (1 : ℝ) using 1 <;>
      simp only [sub_self, Pi.div_apply, div_div_eq_mul_div, mul_div_assoc, mul_comm]
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

lemma pi_nth_prime_asymp :
    (fun n ↦ (Nat.nth Nat.Prime n) / (log (Nat.nth Nat.Prime n))) ~[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
  trans (fun (n : ℕ) ↦ ( n + 1 : ℝ))
  · have : Tendsto (fun n ↦ ((Nat.nth Nat.Prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr
        ((nth_strictMono infinite_setOfPred_prime).tendsto_atTop)
    convert! Nat.isEquivalent_primeCounting.comp_tendsto this |>.symm
    simp only [Function.comp_apply, floor_natCast]
    rw [Nat.primeCounting_nth_prime]
    norm_cast
  · apply IsEquivalent.add_isLittleO (by rfl)
    exact isLittleO_const_id_atTop (1 : ℝ) |>.natCast_atTop

lemma log_nth_prime_asymp : (fun n ↦ log (Nat.nth Nat.Prime n)) ~[atTop] (fun n ↦ log n) := by
  have := pi_nth_prime_asymp.log tendsto_natCast_atTop_atTop
  · apply IsEquivalent.trans _ this
    apply IsEquivalent.congr_right (v := (fun n ↦ log (Nat.nth Nat.Prime n) - log (log (Nat.nth Nat.Prime n))))
    swap
    · filter_upwards with n
      rw [log_div]
      · exact_mod_cast prime_nth_prime n |>.ne_zero
      · apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
        <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
    symm
    apply IsEquivalent.sub_isLittleO (by rfl)
    apply IsLittleO.comp_tendsto isLittleO_log_id_atTop
    have : Tendsto (fun n ↦ ((Nat.nth Nat.Prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr
        ((nth_strictMono infinite_setOfPred_prime).tendsto_atTop)
    apply tendsto_log_atTop.comp this

lemma nth_prime_asymp : (fun n ↦ ((Nat.nth Nat.Prime n) : ℝ)) ~[atTop] (fun n ↦ n * log n) := by
  have := pi_nth_prime_asymp.mul log_nth_prime_asymp
  convert! this using 1
  ext n
  simp only [Pi.mul_apply]
  have : log (Nat.nth Nat.Prime n) ≠ 0 :=by
    apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
      <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
  field

@[blueprint
  (title := "pn-asymptotic")
  (statement := /--
   One has
    $$ p_n = (1+o(1)) n \log n$$
  as $n \to \infty$.
  -/)
  (proof := /--
    Use Corollary \ref{pi_alt} to show that $n=\pi(p_n)\sim p_n/\log p_n$
    Taking logs gives $\log n \sim \log p_n - \log\log p_n \sim \log p_n$.
    Multiplying these gives $p_n\sim n\log n$ from which the result follows.
  -/)
  (latexEnv := "proposition")]
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (Nat.nth Nat.Prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  apply isLittleO_of_tendsto
  · simp
  simp only [div_one]
  unfold c
  have := isEquivalent_iff_tendsto_one ?_|>.mp nth_prime_asymp
  swap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp
    norm_cast
    grind
  convert! this.add_const (-1 : ℝ) using 2
  norm_num


@[blueprint
  (title := "pn-pn-plus-one")
  (statement := /--
  We have $p_{n+1} - p_n = o(p_n)$
    as $n \to \infty$.
  -/)
  (proof := /-- Easy consequence of preceding proposition. -/)
  (latexEnv := "corollary")]
theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  have hne (n : ℕ) : (Nat.nth Nat.Prime n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.prime_nth_prime n).ne_zero
  have hratio := (isEquivalent_iff_tendsto_one (Eventually.of_forall hne)).mp
    Nat.isEquivalent_nth_prime_succ
  refine ⟨fun n ↦ ((Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n) /
    Nat.nth Nat.Prime n, (isLittleO_one_iff ℝ).mpr ?_, ?_⟩
  · have hzero := hratio.sub_const (1 : ℝ)
    simp only [sub_self] at hzero
    apply hzero.congr
    intro n
    simp only [Pi.div_apply, sub_div, div_self (hne n)]
  · intro n
    exact (div_mul_cancel₀ _ (hne n)).symm

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
  filter_upwards [hf.eventually (gt_mem_nhds hδ)] with x hx
  linarith only [hx]


lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  have hscale : Tendsto (fun x : ℝ ↦ (1 + ε) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  filter_upwards [(hf.comp hscale).eventually (lt_mem_nhds (neg_lt_zero.mpr hδ))]
    with x hx
  simp only [Function.comp_apply] at hx
  linarith only [hx]


lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  filter_upwards [bound_f_first_term hε f hf δ hδ, eventually_ge_atTop (1 : ℝ)] with x hx h1
  apply mul_lt_mul_of_pos_right hx
  exact div_pos (by positivity)
    (log_pos (one_lt_mul_of_lt_of_le (by linarith) h1))


lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
  filter_upwards [bound_f_second_term f hf δ hδ, eventually_ge_atTop (2 : ℝ)] with x hx h2
  exact mul_lt_mul_of_pos_right hx
    (div_pos (by linarith) (log_pos (by linarith)))


lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  let c := 1 + ε
  have hc : 0 < c := by dsimp [c]; linarith
  have hlognorm : Tendsto (norm ∘ log) atTop atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp tendsto_log_atTop
  have hlog : (fun x : ℝ ↦ log (c * x)) ~[atTop] log := by
    refine (IsEquivalent.refl.const_add_of_norm_tendsto_atTop (c := log c) hlognorm).congr_left ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (log_mul hc.ne' hx.ne').symm
  have hscale : (fun x : ℝ ↦ c * x / log (c * x)) ~[atTop]
      (fun x : ℝ ↦ c * (x / log x)) := by
    convert ((IsEquivalent.refl : (fun x : ℝ ↦ c * x) ~[atTop] (fun x : ℝ ↦ c * x)).div hlog) using 1
    ext x
    simp only [Pi.div_apply, mul_div_assoc]
  have hpi := (Nat.isEquivalent_primeCounting.comp_tendsto (tendsto_id.const_mul_atTop hc)).trans hscale
  have hden : ∀ᶠ x : ℝ in atTop, x / log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (div_pos (by linarith) (log_pos hx)).ne'
  have herror : (fun x : ℝ ↦ (Nat.primeCounting ⌊c * x⌋₊ : ℝ) - c * (x / log x)) =o[atTop]
      (fun x : ℝ ↦ x / log x) := by
    exact hpi.isLittleO.trans_isBigO (isBigO_const_mul_self c _ _)
  have hscaled := (isLittleO_sub_mul_iff_tendsto_div hden).mp herror
  have hbase := (isEquivalent_iff_tendsto_one hden).mp Nat.isEquivalent_primeCounting
  have hratio : Tendsto (fun x : ℝ ↦ ((Nat.primeCounting ⌊c * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) / (x / log x)) atTop (nhds ε) := by
    simpa only [Pi.div_apply, sub_div, show c - 1 = ε by dsimp [c]; ring] using hscaled.sub hbase
  apply (hratio.pos_mul_atTop hε TauCeti.Real.tendsto_div_log_atTop).congr'
  filter_upwards [hden] with x hx
  dsimp only [c]
  exact div_mul_cancel₀ _ hx

@[blueprint
  (title := "prime-between")
  (statement := /-- For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for
  all sufficiently large $x$. -/)
  (proof := /-- Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity
  as $x \to \infty$. -/)
  (latexEnv := "corollary")]
theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  filter_upwards [Nat.eventually_exists_prime_mem_Ioc (show 0 < ε / 2 by linarith),
    eventually_gt_atTop (0 : ℝ)] with x ⟨p, hp, hxp, hpx⟩ hx
  exact ⟨p, hp, hxp, hpx.trans_lt (by nlinarith)⟩


@[blueprint
  "mun"
  (statement := /-- We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$. -/)
  (proof := /--
  From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
    $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
    $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
    and the claim follows.
  -/)
  (latexEnv := "proposition")]
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
      μ d * Int.fract (N / d : ℚ) := calc
    (1 : ℚ) = ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, μ d := by
      have (x : ℕ) (hx : x ∈ Ioc 0 N) : ∑ d ∈ divisors x, μ d = if x = 1 then 1 else 0 := by
        rw [mem_Ioc] at hx
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
      rw [sum_congr rfl this]
      simp [hN.ne']
    _ = ∑ d ∈ range (N + 1), μ d * (N / d : ℕ) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (add_one_pos _),
        sum_insert (by simp), Ico_add_one_add_one_eq_Ioc]
      simp
    _ = ∑ d ∈ range (N + 1), (μ d : ℚ) * ⌊(N / d : ℚ)⌋ := by
      simp_rw [Rat.floor_natCast_div_natCast]
      simp [← Int.natCast_ediv]
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
        μ d * Int.fract (N / d : ℚ) := by
      simp_rw [sum_mul, ← sum_sub_distrib, mul_comm_div, ← mul_sub, Int.self_sub_fract]
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d ∈ range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by simp), sum_insert (by simp),
      ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add,
      Finset.Ico_add_one_right_eq_Icc, zero_add]
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← insert_right_Ico hN, sum_insert (by simp), div_self (by simp; grind), Int.fract_one,
      mul_zero, zero_add]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      refine mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      exact abs_moebius_le_one
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    simp [cast_sub (one_le_iff_ne_zero.mpr hN.ne')]

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff₀, div_le_iff₀, cast_pos.mpr hN]
  <;> linarith [h_bound.left]



lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  norm_cast
  convert ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum μ ⌊x⌋₊ |>.symm using 1
  · rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp)]
    simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, div_zero, Int.floor_zero, mul_zero,
      zero_add, Int.natCast_ediv]
    refine sum_congr rfl fun n hn ↦ ?_
    congr
    norm_cast
    rw [← floor_div_natCast, Int.natCast_floor_eq_floor]
    positivity
  · simpa [moebius_mul_coe_zeta, ArithmeticFunction.one_apply]


lemma ArithmeticFunction.moebius_pmul_log_mul_zeta :
    (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log * ArithmeticFunction.zeta = -Λ := by
  ext n
  rw [coe_mul_zeta_apply]
  simp_rw [pmul_apply, intCoe_apply]
  rw [sum_moebius_mul_log_eq]
  rfl

lemma ArithmeticFunction.moebius_pmul_log_eq_moebius_mul_neg_vonMangoldt :
    (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log = μ * -Λ := by
  rw [← moebius_pmul_log_mul_zeta, mul_comm, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Chebyshev.psi (x/k) := by
  rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp), ← add_sum_Ioc_eq_sum_Icc (by simp)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero, log_zero, mul_zero,
    zero_add, div_zero, zero_mul]
  simp_rw [← log_apply, ← intCoe_apply, ← pmul_apply,
    moebius_pmul_log_eq_moebius_mul_neg_vonMangoldt]
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [neg_apply, sum_neg_distrib]
  ring_nf
  congr 2
  congr
  rw [← floor_div_natCast]
  rfl

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Chebyshev.psi (x/k)) := by
  have h_log_identity : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k) = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    rw [Finset.sum_mul _ _ _]
    rw [← Finset.sum_sub_distrib] ; refine Finset.sum_congr rfl fun i hi => ?_ ; by_cases hi' : i = 0 <;> simp +decide [*, Real.log_div, ne_of_gt (zero_lt_one.trans_le hx)] ; ring
  generalize_proofs at *
  have h_log_identity' : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k = -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Chebyshev.psi (x / k) := by
    convert sum_mu_Lambda x using 1
  have h_psi_identity :
      (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Chebyshev.psi (x / k)) =
        -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    simpa [neg_neg] using (congrArg Neg.neg h_log_identity').symm
  unfold M
  symm
  calc
    (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Chebyshev.psi (x / k))) =
        (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Chebyshev.psi (x / k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Chebyshev.psi (x / k) := by
          simp [h_log_identity]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          (-∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) := by
          simp [h_psi_identity]
    _ = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x := by ring

noncomputable def R (x : ℝ) : ℝ := Chebyshev.psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  have h_pnt : (fun x => Chebyshev.psi x - x) =o[atTop] (fun x => x) := by
    have h_psi : (fun x => Chebyshev.psi x) ~[atTop] (fun x => x) := by
      exact Chebyshev.isEquivalent_psi_id
    exact h_psi
  convert! h_pnt using 1

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  have h_abs : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
    intros x hx
    have h_sum : ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) / n = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n := by
      rw [Finset.range_eq_Ico] ; rfl
    have := sum_mobius_div_self_le (⌊x⌋₊ + 1) ; simp_all +decide [Finset.sum_range_succ']
    norm_cast at *
  rw [Asymptotics.isBigO_iff]
  use 1; filter_upwards [Filter.eventually_ge_atTop 1] with x hx; simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm]
  simpa only [← Finset.mul_sum _ _ _, abs_mul] using mul_le_of_le_one_right (abs_nonneg x) (h_abs x hx)

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  have h_sum_log : ∀ x : ℝ, 1 ≤ x → |∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k)| ≤ 2 * x := by
    have h_sum_log_le_x : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) ≤ x := by
      intro x hx
      have h_sum_log : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (k : ℝ)) ≤ Real.log (x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊) := by
        rw [← Real.log_prod]
        · norm_num [Finset.prod_div_distrib]
          erw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
        · exact fun n hn => div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr <| by linarith [Finset.mem_Icc.mp hn])
      have h_exp_bound : x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊ ≤ Real.exp x := by
        exact Real.pow_div_factorial_le_exp x (zero_le_one.trans hx) _
      exact h_sum_log.trans (Real.log_le_iff_le_exp (by positivity) |>.2 h_exp_bound)
    intros x hx
    have h_sum_eq : ∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) := by
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
    rw [abs_of_nonneg] <;> linarith [h_sum_log_le_x x hx, show 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| by linarith [Finset.mem_Icc.mp ‹_›]] ; linarith [Nat.floor_le <| show 0 ≤ x by linarith, show (↑‹ℕ› : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp ‹_› |>.2]]
  rw [Asymptotics.isBigO_iff]
  exact ⟨2, Filter.eventually_atTop.mpr ⟨1, fun x hx => le_trans (h_sum_log x hx) (by norm_num [abs_of_nonneg (by linarith : 0 ≤ x)])⟩⟩

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  have hR_bounded : BddAbove (Set.image (fun y => |R y|) (Set.Icc 0 K)) := by
    have hR_bounded : ∀ y ∈ Set.Icc 0 K, |R y| ≤ ∑ p ∈ Iic ⌊K⌋₊, log p + K := by
      intro y hy
      simp only [R, Chebyshev.psi_eq_sum_Icc]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · refine le_trans (sub_le_self _ hy.1) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr <| Nat.floor_mono hy.2) fun ?_ ?_ ?_ => ?_) ?_
        · exact vonMangoldt_nonneg
        · refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hK
          exact vonMangoldt_le_log
      · refine le_trans ?_ (le_add_of_nonneg_left ?_)
        · exact le_trans (sub_le_self _ <| Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) hy.2
        · exact Finset.sum_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact ⟨_, Set.forall_mem_image.2 hR_bounded⟩
  exact ⟨hR_bounded.choose, fun y hy => hR_bounded.choose_spec <| Set.mem_image_of_mem _ hy⟩

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
    have h_sum_bound : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) + C * ⌊x⌋₊ := by
      have h_sum_bound : ∀ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x / k + C := by
        exact fun k hk => by simpa only [mul_div_assoc] using! h (x / k) (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), show (k : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp hk |>.2])
      convert! Finset.sum_le_sum h_sum_bound using 1 ; norm_num [div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_comm]
    have h_harmonic : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
      intro n _hn
      have h := harmonic_le_one_add_log n
      simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div, add_comm, add_left_comm, add_assoc] using h
    have h_harmonic_x :
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) ≤ Real.log x + 1 := by
      refine (h_harmonic _ <| Nat.floor_pos.mpr hx).trans ?_
      have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        refine Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr hx) ?_
        exact Nat.floor_le (by positivity)
      simpa using add_le_add_right hlog 1
    have h_term1 : ε * x * (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ))) ≤ ε * x * (Real.log x + 1) := by
      refine mul_le_mul_of_nonneg_left h_harmonic_x ?_
      exact mul_nonneg hε (by positivity)
    have h_term2 : C * (⌊x⌋₊ : ℝ) ≤ C * x := by
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact Nat.floor_le (by positivity)
    exact h_sum_bound.trans (add_le_add h_term1 h_term2)

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  have h_eps : ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ ε * x * Real.log x := by
    intro ε hε_pos
    obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y ≥ A, |R y| ≤ (ε / 2) * y := by
      have := R_isLittleO
      rw [Asymptotics.isLittleO_iff] at this
      norm_num at *
      exact Exists.elim (this (half_pos hε_pos)) fun A hA => ⟨Max.max A 1, by positivity, fun y hy => by simpa only [abs_of_nonneg (by linarith [le_max_right A 1] : 0 ≤ y)] using hA y (le_trans (le_max_left A 1) hy)⟩
    obtain ⟨C_A, hC_A⟩ : ∃ C_A : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ C_A := by
      exact ⟨_, fun y hy => R_locally_bounded A hA.1.le |> Classical.choose_spec |> fun h => h y hy⟩
    have h_sum_bound : ∀ x ≥ max A 2, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ (ε / 2) * x * (Real.log x + 1) + C_A * x := by
      intros x hx
      have h_sum_bound : ∀ y ≥ 1, |R y| ≤ (ε / 2) * y + C_A := by
        intros y hy
        by_cases hyA : y ≥ A
        · exact le_add_of_le_of_nonneg (hA.right y hyA) (by
          exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩))
        · exact le_add_of_nonneg_of_le (by
          positivity) (hC_A y ⟨by
          linarith, by
            linarith⟩)
      have := sum_bounded_of_linear_bound (show 0 ≤ ε / 2 by positivity) (show 0 ≤ C_A by exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩)) (fun y hy => h_sum_bound y hy) x (by linarith [le_max_right A 2]) ; aesop
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, (ε / 2) * (Real.log x + 1) + C_A ≤ ε * Real.log x := by
      exact ⟨Real.exp (2 * (C_A / ε + 1)), fun x hx => by nlinarith [Real.log_exp (2 * (C_A / ε + 1)), Real.log_le_log (by positivity) hx, mul_div_cancel₀ C_A hε_pos.ne']⟩
    exact ⟨Max.max x₀ (Max.max A 2), fun x hx => le_trans (h_sum_bound x (le_trans (le_max_right _ _) hx)) (by nlinarith [hx₀ x (le_trans (le_max_left _ _) hx), le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2, Real.log_nonneg (show x ≥ 1 by linarith [le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2])])⟩
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h_sum_eq : ∀ x : ℝ, x ≥ 1 → (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x / k)|) = (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) := by
      intro x hx
      have h0 : (0 : ℕ) ∈ Finset.Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
      have hI : (Finset.Iic ⌊x⌋₊).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
        ext n
        simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
      rw [← Finset.sum_erase_add (Finset.Iic ⌊x⌋₊) (fun k => |R (x / k)|) h0]
      simp [hI, R, Chebyshev.psi_eq_sum_Icc]
    rw [Metric.tendsto_nhds]
    simp +zetaDelta only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_eq_abs, norm_mul,
    eventually_atTop] at *
    intro ε hε; obtain ⟨x₀, hx₀⟩ := h_eps (ε / 2) (half_pos hε) ; use Max.max x₀ 2; intro x hx; rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), abs_of_nonneg (by linarith [le_max_right x₀ 2]), abs_of_nonneg (Real.log_nonneg (by linarith [le_max_right x₀ 2]))] ; rw [div_lt_iff₀] <;> nlinarith [hx₀ x (le_trans (le_max_left x₀ 2) hx), Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x), mul_pos (by linarith [le_max_right x₀ 2] : 0 < x) (Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x)), h_sum_eq x (by linarith [le_max_right x₀ 2])]
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' (by nlinarith [Real.log_pos hx])

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → |R y| ≤ ε * y := by
    have := R_isLittleO.def hε
    rw [Filter.eventually_atTop] at this; rcases this with ⟨A, hA⟩ ; exact ⟨Max.max A 1, by positivity, fun y hy => by simpa [abs_of_nonneg (show 0 ≤ y by linarith [le_max_right A 1])] using hA y (le_trans (le_max_left A 1) hy)⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ CA := by
    exact R_locally_bounded A hA.1.le |> fun ⟨CA, hCA⟩ => ⟨CA, fun y hy => hCA y hy⟩
  exact ⟨Max.max CA 0, by positivity, fun y hy => if hy' : y ≤ A then le_trans (hCA y ⟨by linarith, by linarith⟩) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith]) else le_trans (hA.2 y (by linarith)) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith])⟩

lemma M_isLittleO : M =o[atTop] id := by
  have h_identity : ∀ x ≥ 1, M x * Real.log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Chebyshev.psi (x / k)) := by
    exact fun x a => M_log_identity x a
  have h_term1 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) =O[atTop] id := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k) := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * Real.log (x / k)| ≤ Real.log (x / k) := by
        intros k hk
        have h_abs : |(μ k : ℝ)| ≤ 1 := by
          norm_num [ArithmeticFunction.moebius]
          split_ifs <;> norm_num
        by_cases hk0 : k = 0
        · rw [hk0] ; norm_num [ArithmeticFunction.map_zero, Nat.cast_zero, Real.log_zero, div_zero, abs_zero]
        · have hx_pos : 0 < x := by positivity
          have hk_pos : 0 < (k : ℝ) := by positivity
          rw [Real.log_div hx_pos.ne' hk_pos.ne']
          simp only [abs_mul, ge_iff_le]
          simp_all only [ge_iff_le, mem_Iic]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) h_abs) (by rw [abs_of_nonneg] ; exact sub_nonneg_of_le <| Real.log_le_log hk_pos (Nat.cast_le.mpr hk |>.trans (Nat.floor_le hx_pos.le)))
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_log : (fun x => ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k)) =O[atTop] id := by
      convert sum_log_div_isBigO using 1
    rw [Asymptotics.isBigO_iff] at *
    exact ⟨h_sum_log.choose, by filter_upwards [h_sum_log.choose_spec, Filter.eventually_ge_atTop 1] with x hx₁ hx₂ using le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)⟩
  have h_term2 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
    convert sum_mobius_div_isBigO using 1
  have h_term3 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) =o[atTop] (fun x => x * Real.log x) := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)| := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * R (x / k)| ≤ |R (x / k)| := by
        norm_num [abs_mul]
        intro k hk; exact mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_abs_R : (fun x => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * Real.log x) := by
      exact sum_abs_R_isLittleO
    rw [Asymptotics.isLittleO_iff] at *
    intro c hc; filter_upwards [h_sum_abs_R hc, Filter.eventually_ge_atTop 1] with x hx₁ hx₂; exact le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)
  have h_combined : (fun x => M x * Real.log x) =o[atTop] (fun x => x * Real.log x) := by
    have h_combined : (fun x => M x * Real.log x) = (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) := by
      ext x; by_cases hx : 1 ≤ x <;> simp_all +decide only [ge_iff_le, mul_sub, sum_sub_distrib, not_le, Pi.sub_apply]
      · simp +decide [sub_sub, mul_sub, Finset.sum_sub_distrib, R]
      · unfold M R; norm_num [Nat.floor_eq_zero.mpr hx]
    rw [h_combined]
    refine Asymptotics.IsLittleO.sub ?_ h_term3
    refine Asymptotics.IsLittleO.sub ?_ ?_
    · refine h_term1.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> norm_num at hx⟩
    · refine h_term2.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> linarith⟩
  rw [Asymptotics.isLittleO_iff_tendsto'] at *
  · refine h_combined.congr' (by filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by rw [mul_div_mul_right _ _ (ne_of_gt <| Real.log_pos hx)] ; rfl)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos (by positivity) <| Real.log_pos hx
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using by nlinarith [Real.log_pos hx]
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'


@[blueprint
  "mu-pnt"
  (title := "M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n) = o(x)$. -/)
  (proof := /--
  From the Dirichlet convolution identity
    $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
  and summing we obtain
  $$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
  For any $\eps>0$, we have from the prime number theorem that
  $$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
  (divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
  We conclude that
  $$ \sum_{n \leq x} \mu(n) \log n
    = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
  Applying \eqref{mun} we conclude that
  $$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
  and hence
  $$ \sum_{n \leq x} \mu(n) \log x
    = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
  From Stirling's formula one has
  $$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
  thus
  $$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
  and thus
  $$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
  Sending $\eps \to 0$ we obtain the claim.
  -/)
  (proofUses := ["WeakPNT", "mun"])
  (latexEnv := "proposition")]
theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by
  have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
    have h_bound : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
      have h_sum : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
          convert! M_isLittleO using 1
        simpa only [Finset.range_eq_Ico] using! h_moebius_sum
      have h_mu_floor : (fun x : ℝ => (μ ⌊x⌋₊ : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
        · refine squeeze_zero_norm (a := fun x : ℝ => 1 / |x|) ?_ ?_
          · intro x; norm_num [abs_div]
            exact mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)
          · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
        · exact ⟨1, by intros; linarith⟩
      simpa [Finset.sum_range_succ] using h_sum.sub h_mu_floor
    convert h_bound using 1
  rw [Asymptotics.isLittleO_iff] at *
  simp_all +decide [Norm.norm]


private lemma sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (liouville d : ℝ) = if IsSquare n then 1 else 0 := by
  let L : ArithmeticFunction ℝ := liouville
  have hL : L.IsMultiplicative := isMultiplicative_liouville.intCast
  have hprime (p k : ℕ) (hp : p.Prime) :
      (L * (zeta : ArithmeticFunction ℝ)) (p ^ k) = if Even k then 1 else 0 := by
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp]
    simp only [L, intCoe_apply, liouville_apply (pow_ne_zero _ hp.ne_zero),
      cardFactors_apply_prime_pow hp, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [neg_one_geom_sum]
    simp only [Nat.even_add_one, ite_not]
  change (∑ d ∈ n.divisors, L d) = _
  rw [← coe_mul_zeta_apply (f := L),
    (hL.mul isMultiplicative_zeta.natCast).multiplicative_factorization (L * (zeta : ArithmeticFunction ℝ)) hn]
  have hf : n.factorization.prod (fun p k ↦ (L * (zeta : ArithmeticFunction ℝ)) (p ^ k)) =
      ∏ p ∈ n.primeFactors, if Even (n.factorization p) then (1 : ℝ) else 0 := by
    apply Finset.prod_congr rfl
    intro p hp
    exact hprime p _ (Nat.prime_of_mem_primeFactors hp)
  rw [hf, Finset.prod_boole]
  congr 1
  rw [Nat.isSquare_iff_even_factorization]
  apply propext
  constructor
  · intro h p hp
    by_cases hmem : p ∈ n.primeFactors
    · exact h p hmem
    · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp
        (show p ∉ n.factorization.support from hmem)
      simp only [hz, Even.zero]
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp)

lemma lambda_eq_sum_sq_dvd_mu (n : ℕ) (hn : n ≠ 0) :
    ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
  have hinv := (sum_eq_iff_sum_mul_moebius_eq
    (f := fun k ↦ (liouville k : ℝ))
    (g := fun k ↦ if IsSquare k then (1 : ℝ) else 0)).mp
      (fun k hk ↦ sum_divisors_liouville hk.ne') n (Nat.pos_of_ne_zero hn)
  rw [Nat.sum_divisorsAntidiagonal' (fun a b ↦ (μ a : ℝ) *
    (if IsSquare b then 1 else 0))] at hinv
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at hinv
  have hL : (liouville n : ℝ) = (-1 : ℝ) ^ Ω n := by
    rw [liouville_apply hn]
    norm_cast
  rw [← hL, ← hinv]
  symm
  have hsq {q : ℕ} (hq : IsSquare q) : (Nat.sqrt q) ^ 2 = q := by
    rcases hq with ⟨d, rfl⟩
    simp [Nat.sqrt_eq, pow_two]
  apply Finset.sum_nbij' (fun d ↦ d ^ 2) Nat.sqrt
  · intro d hd
    rw [mem_filter, mem_Icc] at hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd.2, hn⟩, ⟨d, by ring⟩⟩
  · intro q hq
    obtain ⟨hqdiv, hq⟩ := mem_filter.mp hq
    have hqpos : 0 < q := Nat.pos_of_mem_divisors hqdiv
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.sqrt_pos.mpr hqpos),
      (Nat.sqrt_le_self q).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
        (Nat.dvd_of_mem_divisors hqdiv))⟩, ?_⟩
    rw [hsq hq]
    exact Nat.dvd_of_mem_divisors hqdiv
  · intro d _
    exact Nat.sqrt_eq' d
  · intro q hq
    exact hsq (mem_filter.mp hq).2
  · intro d _
    rfl

lemma sum_lambda_eq_sum_mu_div_sq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((-1 : ℝ) ^ (Ω n)) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ) := by
      have h_sum_rewrite : ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
        have h_sum_rewrite : ∀ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
          intro n hn
          have h_lambda_eq : ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
            convert lambda_eq_sum_sq_dvd_mu n ( by linarith [ Finset.mem_Icc.mp hn ] ) using 1;
          rw [ h_lambda_eq, Finset.sum_subset ];
          · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_Icc.mp hn |>.2 ] ⟩, Finset.mem_filter.mp hx |>.2 ⟩;
          · simp +zetaDelta only [mem_Icc, mem_filter, not_and, and_imp, Int.cast_eq_zero] at *
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃;
        exact Finset.sum_congr rfl h_sum_rewrite;
      rw [ h_sum_rewrite, Finset.sum_sigma' ];
      have h_reindex : ∑ x ∈ (Finset.Icc 1 N).sigma fun (n : ℕ) => {d ∈ Finset.Icc 1 N | d ^ 2 ∣ n}, (μ (x.fst / x.snd ^ 2) : ℝ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d ^ 2), (μ k : ℝ) := by
        rw [ Finset.sum_sigma' ];
        apply Finset.sum_bij (fun x _ => ⟨x.snd, x.fst / x.snd ^ 2⟩);
        · simp only [mem_sigma, mem_filter, mem_Icc, and_imp]
          exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ ⟨hx₃, Nat.le_sqrt'.mpr ((Nat.le_of_dvd (by omega) hx₅).trans hx₂)⟩, Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hx₅ ) ( by positivity ), Nat.div_le_div_right hx₂ ⟩;
        · simp +contextual [ Finset.mem_sigma, Finset.mem_filter ];
          aesop;
        · simp +zetaDelta only [mem_sigma, mem_Icc, mem_filter, exists_prop, Sigma.exists, and_imp] at *
          exact fun b hb₁ hb₂ hb₃ hb₄ => ⟨ b.fst ^ 2 * b.snd, b.fst, ⟨ ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, by norm_num ⟩, by simp +decide [ Nat.mul_div_cancel_left _ ( by nlinarith : 0 < b.fst ^ 2 ) ] ⟩;
        · aesop;
      convert h_reindex using 1



private lemma M_eq_sum_Icc (x : ℝ) :
    M x = ∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) := by
  symm
  apply Finset.sum_subset Finset.Icc_subset_Iic_self
  intro k hk hk'
  have : k = 0 := by simp only [mem_Iic, mem_Icc, not_and] at hk hk'; omega
  simp [this]

private lemma abs_M_le_self {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ x := by
  rw [M_eq_sum_Icc]
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, |(μ k : ℝ)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _k ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) :=
      Finset.sum_le_sum (fun k _ ↦ by exact_mod_cast abs_moebius_le_one (n := k))
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

lemma sum_mu_div_sq_isLittleO : (fun N : ℕ ↦ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  let F (N d : ℕ) : ℝ := M ((N : ℝ) / d ^ 2) / N
  have hlim (d : ℕ) : Tendsto (fun N ↦ F N d) atTop (nhds 0) := by
    by_cases hd : d = 0
    · simp [F, hd, M]
    have hdpos : 0 < (d : ℝ) ^ 2 := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) _
    have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) / d ^ 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const hdpos
    have hm := ((isLittleO_iff_tendsto' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
      exact (hx.ne' hzero).elim)).mp M_isLittleO).comp ht
    change Tendsto (fun N : ℕ ↦ M ((N : ℝ) / d ^ 2) / ((N : ℝ) / d ^ 2))
      atTop (nhds 0) at hm
    have hc := hm.div_const ((d : ℝ) ^ 2)
    simpa only [F, Function.comp_apply, zero_div, div_div, div_mul_cancel₀ _ (ne_of_gt hdpos)] using! hc
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ d, ‖F N d‖ ≤ (1 : ℝ) / d ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN d
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    simp only [F, norm_eq_abs, abs_div, abs_of_pos hNpos]
    calc
      _ ≤ ((N : ℝ) / d ^ 2) / N :=
        div_le_div_of_nonneg_right (abs_M_le_self (by positivity)) hNpos.le
      _ = 1 / (d : ℝ) ^ 2 := by rw [div_right_comm, div_self hNpos.ne']
  have hs := tendsto_tsum_of_dominated_convergence
    (show Summable (fun d : ℕ ↦ (1 : ℝ) / d ^ 2) by simp) hlim hbound
  simp only [tsum_zero] at hs
  have heq (N : ℕ) : (∑' d, F N d) =
      (∑ d ∈ Icc 1 (Nat.sqrt N), ∑ k ∈ Icc 1 (N / d ^ 2), (μ k : ℝ)) / N := by
    rw [tsum_eq_sum (s := Icc 1 (Nat.sqrt N))]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      dsimp [F]
      congr 1
      rw [M_eq_sum_Icc, ← Nat.cast_pow, Nat.floor_div_natCast, Nat.floor_natCast]
    · intro d hd
      have hquot : N / d ^ 2 = 0 := by
        by_cases hd0 : d = 0
        · simp [hd0]
        apply Nat.div_eq_of_lt
        have : Nat.sqrt N < d := by simp only [mem_Icc, not_and] at hd; omega
        exact Nat.sqrt_lt'.mp this
      simp only [F, M, ← Nat.cast_pow, Nat.floor_div_natCast, Nat.floor_natCast, hquot]
      simp
  rw [isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN hzero
    exact (Nat.ne_of_gt hN (Nat.cast_eq_zero.mp hzero)).elim)]
  simpa only [heq] using hs


@[blueprint
  "lambda-pnt"
  (statement := /-- We have $\sum_{n \leq x} \lambda(n) = o(x)$. -/)
  (proof := /--
  From the identity
    $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
  and summing, we have
  $$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
  For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
  $$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
  and hence on summing in $d$
  $$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
  Sending $\eps \to 0$ we obtain the claim.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      have h_lambda_pnt : (fun N : ℕ => ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
        exact sum_mu_div_sq_isLittleO
      convert h_lambda_pnt using 2;
      convert sum_lambda_eq_sum_mu_div_sq _;
      exact Eq.symm cardFactors_eq_sum_factorization
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
      · convert h_lambda_pnt.add ( show Filter.Tendsto ( fun x : ℕ => ( 1 : ℝ ) / x ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> norm_num [ Finset.sum_Ico_eq_sum_range ];
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring_nf;
      · exact ⟨ 1, by aesop ⟩;
      · exact ⟨ 1, by aesop ⟩;
    simp_all +decide only [Finset.sum_range_succ]
    have := h_lambda_pnt.sub ( show ( fun N : ℕ => ( -1 : ℝ ) ^ N.factorization.sum fun p k => k ) =o[Filter.atTop] fun N : ℕ => ( N : ℝ ) from ?_ );
    · aesop;
    · rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
      · exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using tendsto_inv_atTop_nhds_zero_nat );
      · exact ⟨ 1, fun n hn => by positivity ⟩;
  have h_floor : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun x : ℝ => (⌊x⌋₊ : ℝ)) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
    · exact h_lambda_pnt.comp <| tendsto_nat_floor_atTop;
    · exact ⟨ 1, by aesop ⟩;
    · exact ⟨ 1, by intros; linarith ⟩;
  rw [ Asymptotics.isLittleO_iff ] at *;
  intro c hc
  filter_upwards [h_floor (half_pos hc), Filter.eventually_gt_atTop 1] with x hx₁ hx₂
  refine le_trans ?_ (le_trans hx₁ ?_)
  · norm_num [ Norm.norm ];
    convert le_rfl using 2;
    congr! 2;
    exact Eq.symm cardFactors_eq_sum_factorization
  · norm_num [ abs_of_nonneg, Nat.floor_le, hx₂.le ];
    rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ]


lemma sum_mobius_floor (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1 := by
  classical
  have h := sum_mobius_mul_floor x hx
  have h0 : (0 : ℕ) ∈ Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
  have hI : (Iic ⌊x⌋₊).erase 0 = Icc 1 ⌊x⌋₊ := by
    ext n
    simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
  rw [← Finset.sum_erase_add (Iic ⌊x⌋₊) (fun n => (μ n : ℝ) * (⌊x / n⌋ : ℝ)) h0] at h
  simpa [hI] using h

lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
      have h_group : ∀ x : ℝ, x ≥ 1 → ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, k * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) := by
        intro x hx
        have h_group : ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ) * k := by
          have h_group : Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊ = Finset.biUnion (Finset.Ico 1 K) (fun k => Finset.Ioc (⌊x / (k + 1 : ℝ)⌋₊) (⌊x / (k : ℝ)⌋₊)) := by
            ext n
            simp only [mem_Ioc, mem_biUnion, mem_Ico]
            constructor
            · intro hn
              refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
              all_goals generalize_proofs at *
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
                exact ⟨by rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)] ; nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by rw [Nat.floor_lt (by positivity)] at *; rw [div_lt_iff₀ (by positivity)] at *; norm_num at *; linarith⟩
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [Nat.lt_floor_add_one (x / n)]
                nlinarith [Nat.lt_floor_add_one (x / n), show (n : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
              · refine Nat.le_floor ?_
                rw [le_div_iff₀] <;> norm_num
                · exact le_trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
                · exact Nat.floor_pos.mpr (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2, div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
            · field_simp
              rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
              refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
              · gcongr ; norm_cast
              · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
          rw [h_group, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
            simp +zetaDelta only [ge_iff_le, mem_Ico, mem_Ioc, mul_eq_mul_left_iff, Int.cast_eq_zero] at *
            rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at *
            exact Or.inl <| mod_cast Int.floor_eq_iff.mpr ⟨by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)], by rw [div_lt_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)]⟩
          · intros k hk l hl hkl; simp_all +decide [Finset.disjoint_left]
            field_simp
            intro a ha₁ ha₂ ha₃; contrapose! hkl
            rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
            rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith }) (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith })
        simpa only [mul_comm, Finset.mul_sum _ _ _] using h_group
      have h_M_x_over_k : ∀ k : ℕ, 1 ≤ k → k < K → (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
        have h_M : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) =o[atTop]
            (fun x : ℝ ↦ x) := by
          simpa using! M_isLittleO.congr' (Filter.Eventually.of_forall M_eq_sum_Icc) .rfl
        intros k hk_pos hk_lt_K
        have h_M_x_over_k : (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) = (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) - (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k + 1 : ℝ)⌋₊, (μ n : ℝ)) := by
          ext x
          simp only [Pi.sub_apply]
          rw [eq_sub_iff_add_eq']
          simp only [show Finset.Icc (1 : ℕ) (⌊x / (↑k + 1)⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / (↑k + 1)⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / (↑k + 1)⌋₊)),
            show Finset.Icc (1 : ℕ) (⌊x / ↑k⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / ↑k⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / ↑k⌋₊))]
          rw [Finset.sum_Ioc_consecutive] <;> norm_num

          by_cases hx : 0 ≤ x <;> simp_all +decide only [ge_iff_le, floor_div_natCast, not_le]
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            exact Nat.le_floor <| by push_cast; nlinarith [Nat.floor_le (show 0 ≤ x / (k + 1) by positivity), Nat.lt_floor_add_one (x / (k + 1)), mul_div_cancel₀ x (by positivity : (k + 1 : ℝ) ≠ 0)]
          · rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le (by positivity)), Nat.floor_of_nonpos hx.le] ; norm_num
        rw [h_M_x_over_k]
        refine Asymptotics.IsLittleO.sub ?_ ?_
        · field_simp
          refine h_M.comp_tendsto (Filter.tendsto_id.atTop_mul_const (by positivity)) |> fun h => h.trans_isBigO ?_
          exact Asymptotics.isBigO_iff.mpr ⟨(k : ℝ) ⁻¹, Filter.eventually_atTop.mpr ⟨1, fun x hx => by simp +decide ; ring_nf; norm_num [show k ≠ 0 by linarith]⟩⟩
        · have := h_M.comp_tendsto (show Filter.Tendsto (fun x : ℝ => x / (k + 1)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_div_const (by positivity))
          rw [Asymptotics.isLittleO_iff] at *
          intro c hc; filter_upwards [this (show 0 < c * (k + 1) by positivity), Filter.eventually_gt_atTop 0] with x hx₁ hx₂; simp_all +decide only [ge_iff_le, norm_eq_abs, eventually_atTop, Function.comp_apply, norm_div, cast_nonneg,
    zero_le_one, add_nonneg, abs_of_nonneg]
          exact hx₁.trans (by rw [mul_assoc, mul_div_cancel₀ _ (by positivity)])
      have h_sum_o_x : (fun x : ℝ => ∑ k ∈ Finset.Ico 1 K, (k : ℝ) * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ))) =o[atTop] (fun x => x) := by
        exact Asymptotics.IsLittleO.fun_sum (s := Finset.Ico 1 K) fun k hk ↦
          (h_M_x_over_k k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2).const_mul_left
            (k : ℝ)
      exact h_sum_o_x.congr'
        (by filter_upwards [Filter.eventually_ge_atTop 1] with x hx using by rw [h_group x hx])
        (by norm_num)


lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
    have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = (∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) + (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) := by
      erw [Finset.sum_Ioc_consecutive] <;> norm_num
      · rfl
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast hK
    have h_floor : ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋) := by
      rw [Finset.mul_sum _ _ _] ; rw [← Finset.sum_sub_distrib] ; exact Finset.sum_congr rfl fun _ _ => by ring
    have h_bound : |∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ ⌊x / (K : ℝ)⌋₊ := by
      have h_bound : ∀ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, |(μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ 1 := by
        norm_num [abs_mul]
        exact fun n hn₁ hn₂ => (mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)).trans (abs_le.mpr ⟨by linarith [Int.fract_nonneg (x / n)], by linarith [Int.fract_lt_one (x / n)]⟩)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h_bound) (by norm_num))
    have h_sum_floor : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = 1 := by
      convert sum_mobius_floor x hx using 1
    cases abs_cases (x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ) ⌋₊, (μ n : ℝ) / n - 1) <;> cases abs_cases (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ) ⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ) ⌋) <;> linarith [abs_le.mp h_bound, Nat.floor_le (show 0 ≤ x / (K : ℝ) by positivity), Nat.lt_floor_add_one (x / (K : ℝ))]



@[blueprint
  "mu-pnt-alt"
  (title := "Alternate M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n)/n = o(1)$. -/)
  (proof := /--
  As in the proof of Theorem \ref{mun}, we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    $$ = x \sum_{d \leq x} \frac{\mu(d)}{d} - \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \}$$
  so it will suffice to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = o(x).$$
  Let $N$  be a natural number.  It suffices to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = O(x/N).$$
  if $x$ is large enough depending on $N$.
  We can split the left-hand side as the sum of
  $$ \sum_{d \leq x/N} \mu(d) \{ \frac{x}{d} \} $$
  and
  $$ \sum_{j=1}^{N-1} \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j).$$
  The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt}
  and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
  for any given $j$, so in particular
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
  for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.
  Summing all the bounds, we obtain the claim.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    set S : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (μ n : ℝ) / n
    have h_bound : ∀ K : ℕ, 0 < K → ∀ x : ℝ, 1 ≤ x → |S (x / K)| ≤ 1 / K + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x := by
      intros K hK x hx
      have h_approx : |x * S (x / K) - 1| ≤ x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
        convert sum_mobius_div_approx x K hK hx using 1
      rw [abs_le] at *
      ring_nf at *
      constructor <;> nlinarith [inv_pos.2 (by positivity : 0 < x), mul_inv_cancel₀ (by positivity : x ≠ 0), abs_nonneg (∑ n ∈ Finset.Ioc ⌊ (K : ℝ) ⁻¹ * x⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x * (n : ℝ) ⁻¹⌋)]
    have h_tail_zero : ∀ K : ℕ, 0 < K → Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
      intro K hK
      have h_tail_zero : Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
        have := sum_mobius_floor_tail_isLittleO K hK
        rw [Asymptotics.isLittleO_iff_tendsto'] at this
        · simpa [abs_div] using this.abs.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [abs_div, abs_of_nonneg hx.le])
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      convert h_tail_zero using 1
    have h_eps : ∀ ϵ > 0, ∃ Y : ℝ, ∀ y ≥ Y, |S y| < ϵ := by
      intros ϵ hϵ_pos
      obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, 0 < K ∧ 1 / (K : ℝ) < ϵ / 3 := by
        exact ⟨⌊ϵ⁻¹ * 3⌋₊ + 1, Nat.succ_pos _, by rw [div_lt_iff₀] <;> push_cast <;> nlinarith [Nat.lt_floor_add_one (ϵ⁻¹ * 3), mul_inv_cancel₀ hϵ_pos.ne']⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ x ≥ Y, |S (x / K)| < ϵ := by
        have h_tail_zero : Filter.Tendsto (fun x : ℝ => 1 / (K : ℝ) + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds (1 / (K : ℝ))) := by
          simpa using Filter.Tendsto.add (tendsto_const_nhds.add (tendsto_inv_atTop_zero)) (h_tail_zero K hK_pos)
        exact Filter.eventually_atTop.mp (h_tail_zero.eventually (gt_mem_nhds <| by linarith)) |> fun ⟨Y, hY⟩ ↦ ⟨Max.max Y 1, fun x hx ↦ lt_of_le_of_lt (h_bound K hK_pos x <| le_trans (le_max_right _ _) hx) <| hY x <| le_trans (le_max_left _ _) hx⟩
      use Y / K; intros y hy; specialize hY (y * K) (by nlinarith [show (K : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Y (by positivity : (K : ℝ) ≠ 0)]) ; simp_all +decide [ne_of_gt]
    exact Metric.tendsto_atTop.mpr fun ε hε => by simpa using h_eps ε hε
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    convert h_sum_zero using 2 ; erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  simpa [Finset.sum_range_succ] using h_sum_zero.sub (show Filter.Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ) / ⌊x⌋₊) Filter.atTop (nhds 0) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => by positivity) (fun x => by simpa using div_le_div_of_nonneg_right (show |(μ ⌊x⌋₊ : ℝ)| ≤ 1 from mod_cast by { unfold ArithmeticFunction.moebius; aesop }) <| Nat.cast_nonneg _) <| tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop)


blueprint_comment /--
\section{Consequences of the PNT in arithmetic progressions}
-/

blueprint_comment /--
\label{chebyshev-asymptotic-pnt}
If $a\ (q)$ is a primitive residue class, then
$\sum_{p \leq x: p = a\ (q)} \log p = x/\phi(q) + o(x)$.
This is Mathlib's `Chebyshev.tendsto_sum_log_prime_modEq_div_atTop`.
-/

blueprint_comment /--
\label{dirichlet_thm}
Any primitive residue class contains infinitely many primes. This is Mathlib's
`Nat.infinite_setOfPred_prime_and_modEq`; converting the set to its subtype and
using the reduced residue representative gives the natural-modulus form.
-/

blueprint_comment /--
\section{Consequences of the Chebotarev density theorem}

-/

blueprint_comment /--
\begin{lemma}[Cyclotomic Chebotarev]\label{Chebotarev-cyclic}
Let $m\geq 1$ and $G = \mathrm{Gal}(\mathbb{Q}(\mu_m)/\mathbb{Q}) \cong (\mathbb{Z}/m\mathbb{Z})^\times$.
For any $a$ coprime to $m$,
\[
\sum_{\substack{N\mathfrak{p}\leq x\\ N\mathfrak{p}\equiv a\pmod{m}}} \log N\mathfrak{p}
\;=\;
\frac{1}{|G|} \sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}
\;+\; o\Bigl(\sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}\Bigr).
\]
In particular the primes in the progression $a\pmod{m}$ have natural density $1/\varphi(m)$
(Dirichlet's theorem).
\end{lemma}
-/

blueprint_comment /--
\begin{proof}\uses{Chebotarev-cyclotomic-density, Dedekind-PNT, WeakPNT-AP}
Specialise Proposition~\ref{Chebotarev-cyclotomic-density} to $K=\mathbb{Q}$ and
$L=\mathbb{Q}(\mu_m)$: the Frobenius condition $\varphi_p=\sigma_a$ with
$\sigma_a(\zeta_m)=\zeta_m^a$ is exactly $p\equiv a\pmod{m}$.  The asymptotic form with
$\log N\mathfrak{p}$ follows by Fourier expansion of the indicator of the progression against
characters of $G$, using Lemma~\ref{Dedekind-PNT} to kill the nontrivial character sums and
the prime-number theorem in AP (Lemma~\ref{WeakPNT-AP}) for the main term.  Cf.\ also
Corollary~7.2.3 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.
\end{proof}
-/
