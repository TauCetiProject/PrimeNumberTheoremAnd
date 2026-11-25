# Migration status

Updated 26 November 2026. Migration is in progress. [ROADMAPS.md](ROADMAPS.md) lists the three groups that need additional roadmap authorization; existing roadmap work and adoption of merged APIs continue separately.

Pins: Lean **v4.37.0-rc1**, Mathlib **31ce06eaadf4a200c0e1407c5f10953cf606b8f8**, Tau Ceti **7433fc3695f4fbf5a07041090628c5c94067c0b9**.

The 19 Lean files (including the root import file) contain **6,767 lines**; the four `Unused/` files account for **2,758**, leaving **4,009 active lines**. `Unused/` and IEANTN remain outside migration scope.

## Prime number theorem

`MediumPNT` and `StrongPNT` are derived from Tau Ceti. `StrongPNT` is the `O`-form of the prime number theorem with de la Vallée Poussin's error term, `Chebyshev.exists_isBigO_psi_sub_id_mul_exp_neg_mul_sqrt_log`, and `MediumPNT` follows from `StrongPNT`. Both use only `propext`, `Classical.choice` and `Quot.sound`.

The blueprint chapters on Mellin calculus, zeta bounds, the medium PNT and the strong PNT now follow Tau Ceti's route (Ingham's transfer theorem, the zero-free region, the window form of `ζ′/ζ`, and the bounds for `ζ′/ζ` and `1/ζ` right of the zero-free curve). Their nodes are `attribute [blueprint]` blocks on the Tau Ceti and Mathlib declarations; the fork's own proofs of these steps have been removed. Each removed declaration is either recovered from Tau Ceti in a short checked derivation or replaced by the more general upstream result its blueprint node now points at. The 3-4-1 lower bound `ZetaLowerBound3` (`|ζ(σ+it)| ≫ (σ-1)^{3/4} log^{-1/4} |t|`) has no Tau Ceti counterpart and stays in `ZetaBounds.lean`.

## Iwaniec–Kowalski chapter 1 and the remaining files

The divisor power sum `σ_ν`, the power function `n ↦ n^ν`, `k^{ω(n)}`, complete additivity and the
`ζ³` identities are Tau Ceti's (`sigmaC`, `cpow`, `powOfAdditive`, `IsCompletelyAdditive`); the
chapter's nodes for them are `attribute [blueprint]` blocks or short restatements on that API.
Untagged scaffolding with no consumer and an upstream counterpart (the residue and argument-principle
lemmas on rectangles, the Selberg bound, the `finsum`/`finprod` forms of the Chebyshev and primorial
asymptotics) has been removed. Apart from the three groups below, every remaining declaration outside
`Unused/` is blueprint glue over Mathlib and Tau Ceti.

## Remaining roadmap gaps

The three groups in ROADMAPS.md are:

1. The Möbius-square divisor-sum identity, including its multiplicativity and prime-power evaluations.
2. Laplace-weighted sinc integrals and pointwise Laplace inversion under the original weak hypotheses.
3. The 3-4-1 lower bound for ζ to the right of `Re s = 1`.

## Validation

Each pass runs `lake build` (warnings only in `Unused/`), `lake build :blueprint`, a check that every blueprint `\ref`/`\uses` target has a `\label` (4 pre-existing dangling references, in the Consequences and IwaniecKowalskiCh1 chapters), and an axiom check of the two endpoints. Hosted CI runs `lake build` and `lake build :blueprint`.
