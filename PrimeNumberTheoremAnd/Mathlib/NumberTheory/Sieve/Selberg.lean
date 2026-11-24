/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
module

public import Batteries.Tactic.Lemma
public import TauCeti.NumberTheory.SelbergSieve.LambdaSquared
public import TauCeti.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


@[expose] public noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)
local notation3 "S" => BoundingSieve.truncatedSelbergSum
  (SelbergSieve.toBoundingSieve (self := s)) (Real.sqrt (SelbergSieve.level (self := s)))

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  refine (s.toBoundingSieve.siftedSum_le_totalMass_div_truncatedSelbergSum_add_errSum
    (Real.one_le_sqrt.mpr hy)).trans (add_le_add le_rfl ?_)
  refine errSum_lambdaSquared_le_sum_three_pow_cardDistinctFactors _ _ y
    (fun d _ ↦ s.toBoundingSieve.abs_selbergWeights_le_one _ d) fun d hd hdy ↦ ?_
  exact selbergWeights_eq_zero_of_lt _ _ _ ((Real.sqrt_lt' (Nat.cast_pos.mpr
    (Nat.pos_of_mem_divisors hd))).mpr (lt_of_not_ge hdy))

end SelbergSieve
