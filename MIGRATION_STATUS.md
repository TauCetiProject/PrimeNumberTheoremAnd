# Migration status

Locally verified 20 November 2026; the preceding published baseline is `dbca0f6`. Migration is in progress. [ROADMAPS.md](ROADMAPS.md) lists the six groups that need additional roadmap authorization; existing roadmap work and adoption of merged APIs continue separately.

The locally validated fork has completed **44 native-reuse cleanup passes**, removing **138 unique declarations** and **eight obsolete modules**. Deleted mathematics is preserved by checked short recoveries of the complete original types. The latest cleanup removes six algebraic covariance lemmas for raw and normalized rectangle integrals. Their complete original types have checked independent recoveries of three, five, one, four, three and five natural proof lines using pinned native interval-integral APIs and kept fork integral carriers. These preserve universe-polymorphic normed complex vector spaces without completeness, regularity, integrability, corner ordering or nonzero-scalar assumptions, including the exact normalization and totalized defaults. No new helper API is introduced. No compatibility aliases or forwarding modules were added.

Pins remain stock Lean **4.36.0-rc2**, Mathlib **048fffa1dbcd080d3058fab41d8c188168595c22**, and Tau Ceti **0642eae29e0a59ef798d04de325386445906e755**. No unmerged provider is consumed. A forward pin change remains a separate unresolved decision. The **56** Lean files contain **27,146 lines** including comments and blanks; four `Unused/` files account for **2,727**, leaving **24,419 active lines**. `Unused/` and IEANTN remain outside migration scope.

## Remaining roadmap gaps

The six groups in ROADMAPS.md remain unchanged:

1. Elementary PNT consequences for Möbius and Liouville sums.
2. The Möbius-square divisor-sum identity, including its multiplicativity and prime-power evaluations.
3. Laplace-weighted sinc integrals and pointwise Laplace inversion under the original weak hypotheses.
4. Numerical completed-zeta nonvanishing at zero and one, with the stated Euler-constant and logarithmic bounds.
5. The lower bound `ζ(2σ) / ζ(σ) ≤ |ζ(σ + it)|` used in StrongPNT.
6. The Fourier-side `W21` test-function space and its approximation theory.

Gamma growth, global pole-cleared zeta growth, quantitative zero counting, and the relevant contour/factorization work have existing roadmap coverage. They are migration or adoption work, not additional gaps. Every adoption still requires the provider to be merged, approved compatible pins and verification of the fork's original hypotheses, constants and defaults.

## Validation

The current cleanup passes the local full library build, focused proof and module checks, and blueprint export. The preceding published baseline `dbca0f6` passes hosted CI; hosted validation of this cleanup follows publication. Local strict checks cover the eight active affected library modules; the required unchanged `Unused` dependent is checked through its actual ordinary build. Its pre-existing unused-simp warning prevents claiming a strict pass for that whole closure; no excluded source or options were changed to suppress it.

The latest cleanup preserves all 963 retained declaration headers. All 229 physical blueprint artifacts retain their payloads, providers, primary/inner labels and paths; only three reviewed Residue source ranges change. All 566 literal references, including the pre-existing external `WeakPNT` reference, and all 565 internal dependency edges remain unchanged. All six fresh old-type recoveries and literal kernel comparisons, current selected-name absence, twelve edge cases, rectangle checks and 28 named axiom requests pass; all 28 requests use only permitted axioms. The external case fixture retains two unnecessary-simpa style warnings. The mathematical source shrinks by 33 lines; all surviving source frames are unchanged. Detailed historical reports are archived separately; this summary does not claim a global rerun of every earlier recovery certificate.

Environment lint of Residue reports missing docstrings on nine unchanged definitions and the existing unused CompleteSpace argument of `RectanglePullToNhdOfPole'`. It therefore does not pass; no suppressions, unrelated repairs or separate baseline environment-lint run were made.
