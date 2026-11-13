module

public import Architect
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp


public section

open scoped Complex ComplexConjugate


blueprint_comment /--
Now in Mathlib:
-/
blueprint_comment /--
\begin{theorem}\label{deriv-conj-conj}
    Let $f : \mathbb{C} \to \mathbb{C}$ be a function at $p \in \mathbb{C}$ with derivative $a$.
    Then the derivative of the function $g(z) = \overline{f(\overline{z})}$ at $\overline{p}$ is
    $\overline{a}$.
  \end{theorem}
\begin{proof}
    We proceed by case analysis on whether $f$ is differentiable at $p$. If $f$ is differentiable
    at $p$, then we can apply the previous theorem. If $f$ is not differentiable at $p$, then
    neither is $g$, and both derivatives have the default value of zero.
  \end{proof}
-/

@[blueprint
  (title := "deriv-riemannZeta-conj")
  (statement := /--
    Conjugation symmetry of the derivative of the Riemann zeta function. Let $s \in \mathbb{C}$.
    Then $$\zeta'(\overline{s}) = \overline{\zeta'(s)}.$$
  -/)
  (proof := /--
    We apply the derivative conjugation symmetry to the Riemann zeta function and use the
    conjugation symmetry of the Riemann zeta function itself.
  -/)]
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hc : conj ∘ riemannZeta ∘ conj = riemannZeta := by
    funext z
    simp
  simpa only [hc, Function.comp_apply, Complex.conj_conj] using!
    congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)

theorem logDerivZeta_conj (s : ℂ) :
    logDeriv riemannZeta (conj s) = conj (logDeriv riemannZeta s) := by
  unfold logDeriv
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

blueprint_comment /--
\begin{theorem}\label{intervalIntegral-conj}
    The conjugation symmetry of the interval integral. Let $f : \mathbb{R} \to \mathbb{C}$ be a
    measurable function, and let $a, b \in \mathbb{R}$. Then
    $$\int_{a}^{b} \overline{f(x)} \, dx = \overline{\int_{a}^{b} f(x) \, dx}.$$
  \end{theorem}
\begin{proof}
    We unfold the interval integral into an integral over a uIoc and use the conjugation property
    of integrals.
  \end{proof}
-/
