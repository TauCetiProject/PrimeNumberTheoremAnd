module

public import Mathlib.Data.Real.Archimedean
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Mertens function

The real-cutoff sum of the Möbius function used in the PNT consequences.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

/-- The Mertens function, summing `μ n` up to the natural floor of `x`. -/
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)
