/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
module

public import Architect
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Completely multiplicative arithmetic functions

The shared predicate and its elementary closure properties are used by both the
Iwaniec–Kowalski development and the Selberg bounds. Arithmetic functions still vanish
at zero, and the multiplication identity here holds for all natural inputs.

The predicate and blueprint metadata are relocated from IwaniecKowalskiCh1;
the closure and power proofs are relocated from the SelbergBounds development.
-/

@[expose] public section

open scoped ArithmeticFunction.zeta

namespace ArithmeticFunction

/--
Define Complete Multiplicativity for an arithmetic function. -/
@[blueprint
  "IsCompletelyMultiplicative"
  (title := "IsCompletelyMultiplicative")
  (statement := /-- Define Complete Multiplicativity for an arithmetic function. -/)]
def IsCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

/-- A function that is completely multiplicative is also multiplicative. -/
@[blueprint
  "IsCompletelyMultiplicative.isMultiplicative"
  (title := "IsCompletelyMultiplicative.isMultiplicative")
  (statement := /-- A function that is completely multiplicative is also multiplicative. -/)
  (proof := /--
  Let $f$ be a completely multiplicative function. To show that $f$ is multiplicative, we need to verify that $f(1) = 1$ and that $f(ab) = f(a)f(b)$ for all coprime natural numbers $a$ and $b$. Since $f$ is completely multiplicative, we have $f(1) = 1$ by definition. For coprime $a$ and $b$, we can write $ab$ as a product of prime factors, and since $f$ is completely multiplicative, it will factor as the product of the values of $f$ at those prime factors. This means that $f(ab) = f(a)f(b)$ for coprime $a$ and $b$, which shows that $f$ is multiplicative.
  -/)]
lemma IsCompletelyMultiplicative.isMultiplicative {f : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative := by
  exact ⟨hf.1, fun {m n} _ => hf.2 m n⟩

namespace IsCompletelyMultiplicative

theorem zeta : IsCompletelyMultiplicative ζ := by
  unfold IsCompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : IsCompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : IsCompletelyMultiplicative f)
    (hg : IsCompletelyMultiplicative g) :
    IsCompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f)
    (hg : IsCompletelyMultiplicative g) :
    IsCompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : IsCompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  let F : ℕ →* ℝ := { toFun := f, map_one' := hf.1, map_mul' := hf.2 }
  exact F.map_pow a n

end IsCompletelyMultiplicative

end ArithmeticFunction
