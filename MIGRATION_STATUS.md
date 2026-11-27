# Migration status

Updated 28 November 2026. [ROADMAPS.md](ROADMAPS.md) lists the one group that still needs additional roadmap authorization; everything else outside `Unused/` is blueprint glue over Mathlib and Tau Ceti.

Pins: Lean **v4.37.0-rc1**, Mathlib **31ce06eaadf4a200c0e1407c5f10953cf606b8f8**, Tau Ceti **9f9b83d89310ef42af5e39909d921db244f24e9b**.

The 19 Lean files (including the root import file) contain **6,590 lines**; the four `Unused/` files account for **2,758**, leaving **3,832 active lines**. `Unused/` and IEANTN remain outside migration scope.

## Prime number theorem

`MediumPNT` and `StrongPNT` are derived from Tau Ceti. `StrongPNT` is the `O`-form of the prime number theorem with de la Vallée Poussin's error term, `Chebyshev.exists_isBigO_psi_sub_id_mul_exp_neg_mul_sqrt_log`, and `MediumPNT` follows from `StrongPNT`. Both use only `propext`, `Classical.choice` and `Quot.sound`.

The blueprint chapters on Mellin calculus, zeta bounds, the medium PNT and the strong PNT now follow Tau Ceti's route (Ingham's transfer theorem, the zero-free region, the window form of `ζ′/ζ`, and the bounds for `ζ′/ζ` and `1/ζ` right of the zero-free curve). Their nodes are `attribute [blueprint]` blocks on the Tau Ceti and Mathlib declarations; the fork's own proofs of these steps have been removed. Each removed declaration is either recovered from Tau Ceti in a short checked derivation or replaced by the more general upstream result its blueprint node now points at. The 3-4-1 nodes in `ZetaBounds.lean` are short glue: `ZetaInvBound1` is Mathlib's `DirichletCharacter.norm_LFunction_product_ge_one` at the trivial character of modulus 1, and `ZetaInvBound2` and `ZetaLowerBound3` (`|ζ(σ+it)| ≫ (σ-1)^{3/4} log^{-1/4} |t|`) interpolate Tau Ceti's bounds `1/|ζ| ≪ log |t|` (`riemannZeta_zeroFreeStrip_bounds`) and `1/|ζ| < 1 + 1/(σ-1)` (`inv_norm_riemannZeta_lt_one_add_one_div_sub_one`).

## Iwaniec–Kowalski chapter 1 and the remaining files

The divisor power sum `σ_ν`, the power function `n ↦ n^ν`, `k^{ω(n)}`, complete additivity and the
`ζ³` identities are Tau Ceti's (`sigmaC`, `cpow`, `powOfAdditive`, `IsCompletelyAdditive`); the
chapter's nodes for them are `attribute [blueprint]` blocks or short restatements on that API.
Untagged scaffolding with no consumer and an upstream counterpart (the residue and argument-principle
lemmas on rectangles, the Selberg bound, the `finsum`/`finprod` forms of the Chebyshev and primorial
asymptotics) has been removed. The Möbius-square identity `μ²(n) = ∑_{d²∣n} μ(d)` (I-K (1.33)), its multiplicativity and
prime-power steps are Tau Ceti's (`sum_divisors_filter_sq_dvd_moebius`, with `μ² = ζ * μ_□` as
`coe_zeta_mul_dilateSq_moebius_apply`, from ExplicitMultiplicativeFunctions §7.1a); their nodes are
`attribute [blueprint]` blocks. Apart from the group below, every remaining declaration outside
`Unused/` is blueprint glue over Mathlib and Tau Ceti. The nodes for the series of `φ` and for
`2^{ω(n)} ≤ σ₀(n)` sit on Tau Ceti's `LSeries_totient` (AnalyticNumberTheoryPartIII §11.4, whose
targets are all on Tau Ceti main) and `two_pow_cardDistinctFactors_le_sigma_zero`.

## Remaining roadmap gap

The one group in ROADMAPS.md is the Laplace-weighted sinc integrals (offered to Mathlib) and
pointwise Laplace inversion under Dini hypotheses, whose Fourier reductions go through Tau Ceti's
truncated Mellin inversion step.

## Validation

Each pass runs `lake build` (warnings only in `Unused/`), `lake build :blueprint`, a check that every blueprint `\ref`/`\uses` target has a `\label` (3 pre-existing dangling references, in the Consequences chapter), and an axiom check of the two endpoints. Hosted CI runs `lake build` and `lake build :blueprint`.
