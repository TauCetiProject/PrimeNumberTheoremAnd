import Architect
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve

open Complex Filter Set
local notation (name := riemannzeta2) "ζ" => riemannZeta
local notation (name := derivriemannzeta2) "ζ'" => deriv riemannZeta

blueprint_comment /--
It would perhaps (?) be better to refactor this entire file so that we're not using explicit
constants but instead systematically using big Oh notation... The punchline would be:
-/

@[blueprint
  (title := "LogDerivZetaBndAlt")
  (statement := /--
    There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $|t|\to\infty$,
    $$
    |\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
    $$
    (Same statement but using big-Oh and filters.)
  -/)
  (proof := /-- Same as above. -/)
  (latexEnv := "lemma")]
lemma LogDerivZetaBndAlt :
    ∃ A > 0, ∀ (σ) (_ : σ ∈ Ico ((1 : ℝ) / 2) (1 : ℝ)),
    (fun (t : ℝ) ↦ ζ' (σ + t * I) / ζ (σ + t * I)) =O[cocompact ℝ ⊓
      Filter.principal {t | 1 - A / Real.log |t| ^ 9 < σ}]
        fun t ↦ Real.log |t| ^ 9 := by
  obtain ⟨β, C, hβ, -, h⟩ := TauCeti.riemannZeta_deriv_logDeriv_bound
  refine ⟨β / 2, by positivity, fun σ ⟨σ_ge, σ_lt⟩ ↦ ?_⟩
  rw [Asymptotics.isBigO_iff]
  use 2 * |C| + 1
  rw [eventually_inf, cocompact_eq_atBot_atTop]
  refine ⟨{t : ℝ | 4 ≤ |t|}, ?_, {t | 1 - β / 2 / Real.log |t| ^ 9 < σ},
    fun ⦃a⦄ a ↦ a, fun t ⟨t_ge, ht⟩ ↦ ?_⟩
  · rw [mem_sup]
    refine ⟨?_, ?_⟩
    · simp only [mem_atBot_sets, mem_ofPred_eq]
      refine ⟨-4, fun b hb ↦ ?_⟩
      rw [_root_.abs_of_nonpos (by linarith)]
      linarith
    · simp only [mem_atTop_sets, ge_iff_le, mem_ofPred_eq]
      refine ⟨4, fun b hb ↦ ?_⟩
      rwa [_root_.abs_of_nonneg (by linarith)]
  simp only [mem_ofPred_eq] at ht t_ge
  set s : ℂ := σ + t * I
  have him : s.im = t := by simp [s]
  have hre : s.re = σ := by simp [s]
  have hL1 : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL9 : Real.log |t| ≤ Real.log |t| ^ 9 := le_self_pow₀ hL1 (by norm_num)
  have hlog2 : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
    rw [show 2 * Real.log |t| = Real.log (|t| ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
  have hs1 : s ≠ 1 := fun h1 ↦ by
    have := congrArg Complex.im h1
    rw [him, one_im] at this
    rw [this, abs_zero] at t_ge
    norm_num at t_ge
  have hreg : 1 - β / Real.log (|s.im| + 2) ≤ s.re := by
    rw [him, hre]
    refine le_trans (sub_le_sub_left ?_ 1) ht.le
    calc β / 2 / Real.log |t| ^ 9 ≤ β / 2 / Real.log |t| :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hL9
      _ = β / (2 * Real.log |t|) := by rw [div_div]
      _ ≤ β / Real.log (|t| + 2) := div_le_div_of_nonneg_left hβ.le hlog2pos hlog2
  obtain ⟨-, -, hb⟩ := h s hs1 hreg
  rw [him] at hb
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    refine div_le_one_of_le₀ (le_trans ?_ (abs_im_le_norm _)) (norm_nonneg _)
    simp only [sub_im, him, one_im, sub_zero]
    linarith
  have hnorm : ‖Real.log |t| ^ 9‖ = Real.log |t| ^ 9 := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc ‖ζ' s / ζ s‖ = ‖(ζ' s / ζ s + 1 / (s - 1)) - 1 / (s - 1)‖ := by ring_nf
    _ ≤ C * Real.log (|t| + 2) + 1 := (norm_sub_le _ _).trans (add_le_add hb hinv)
    _ ≤ |C| * (2 * Real.log |t|) + Real.log |t| := by
        have := mul_le_mul (le_abs_self C) hlog2 hlog2pos.le (abs_nonneg C)
        linarith
    _ ≤ (2 * |C| + 1) * Real.log |t| ^ 9 := by nlinarith [abs_nonneg C]
