import PrimeNumberTheoremAnd.ZetaBounds

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
  obtain ⟨A, hA, C, _, h⟩ := LogDerivZetaBnd
  refine ⟨A, hA.1, fun σ ⟨σ_ge, σ_lt⟩ ↦ ?_⟩
  -- This could all be done much cleaner; TODO: refactor
  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_inf, cocompact_eq_atBot_atTop]
  refine ⟨{t : ℝ | 4 ≤ |t|}, ?_, {t | 1 - A / Real.log |t| ^ 9 < σ},
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
  simp only [mem_ofPred_eq] at ht
  simp only [mem_ofPred_eq] at t_ge
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hband : σ ∈ Ico (1 - A / Real.log |t| ^ (9 : ℝ))
      (1 + A / Real.log |t| ^ (9 : ℝ)) := by
    simp only [Real.rpow_ofNat] at *
    exact ⟨ht.le, lt_of_lt_of_le σ_lt (le_add_of_nonneg_right (div_nonneg hA.1.le (pow_pos hlog 9).le))⟩
  simpa only [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_pos (pow_pos hlog 9)] using
    h σ t (by linarith) hband
