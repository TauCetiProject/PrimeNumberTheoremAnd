module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Polynomial derivatives and logarithmic derivatives

Auxiliary derivative identities for exponential polynomials, used in the polynomial factor
appearing in Hadamard products.
-/

@[expose] public section

namespace Polynomial

/-- The logarithmic derivative of the exponential of a complex polynomial is the polynomial
derivative. -/
theorem logDeriv_exp_eval (P : ℂ[X]) (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
      Polynomial.eval z P.derivative := by
  simpa only [Function.comp_def, Complex.logDeriv_exp, Pi.one_apply, one_mul, P.deriv] using
    (logDeriv_comp (Complex.differentiable_exp.differentiableAt) (P.hasDerivAt z).differentiableAt)

/-- The derivative of a degree-one complex polynomial is constant. -/
theorem degree_derivative_le_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) :
    P.derivative.degree ≤ 0 := by
  apply Polynomial.degree_le_of_natDegree_le (n := 0)
  exact (Polynomial.natDegree_derivative_le P).trans (by
    have hp : P.natDegree ≤ 1 := Polynomial.natDegree_le_of_degree_le hP
    omega)

/-- The derivative of a degree-one complex polynomial is independent of the evaluation point. -/
theorem eval_derivative_eq_eval_derivative_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) (z : ℂ) :
    Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative := by
  have hder :
      P.derivative.degree ≤ 0 :=
    degree_derivative_le_zero_of_degree_le_one hP
  rw [Polynomial.eq_C_of_degree_le_zero hder]
  simp

end Polynomial
