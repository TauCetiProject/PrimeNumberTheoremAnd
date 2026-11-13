/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics

/-!
# Uniform Asymptotics

For a family of functions `f : ι × α → E` and `g : α → E`, we can think of
`f =O[𝓟 s ×ˢ l] fun (i, x) ↦ g x` as expressing that `f i` is O(g) uniformly on `s`.

This file provides methods for constructing `=O[𝓟 s ×ˢ l]` relations (similarly `Θ`)
and deriving their consequences.
-/

public section

open Filter

open Topology

namespace Asymptotics

variable {α ι E F : Type*} {s : Set ι}

section Order

variable [NormedAddCommGroup α] [LinearOrder α] [ProperSpace α] [NormedAddCommGroup F]

theorem isLittleO_const_fst_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atBot ×ˢ ly] Prod.fst := by
  exact (isLittleO_const_id_atBot2 c).comp_tendsto tendsto_fst


theorem isLittleO_const_snd_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atBot] Prod.snd := by
  exact (isLittleO_const_id_atBot2 c).comp_tendsto tendsto_snd


theorem isLittleO_const_fst_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atTop ×ˢ ly] Prod.fst := by
  exact (isLittleO_const_id_atTop2 c).comp_tendsto tendsto_fst


theorem isLittleO_const_snd_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atTop] Prod.snd := by
  exact (isLittleO_const_id_atTop2 c).comp_tendsto tendsto_snd

end Order

end Asymptotics
