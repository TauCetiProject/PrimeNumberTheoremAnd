# Migration status

Locally verified 20 November 2026; the preceding published baseline is `afc97c4`. Migration is in progress. [ROADMAPS.md](ROADMAPS.md) lists the six groups that need additional roadmap authorization; existing roadmap work and adoption of merged APIs continue separately.

The locally validated fork has completed **45 native-reuse cleanup passes**, removing **140 unique declarations** and **eight obsolete modules**. Deleted mathematics is preserved by checked short recoveries of the complete original types. The latest cleanup removes the unrestricted rectangle-neighborhood and border-exclusion lemmas and uses native arguments in their six surviving callers. Their complete original types have checked two-line and seven-line recoveries: Mathlib interior algebra for the first, and the unconditional pinned Tau Ceti frontier theorem plus kept RectangleBorder for the second. Arbitrary reversed and degenerate complex corners remain covered without new ordering assumptions. Generic vector classes, existing completeness requirements, arbitrary residue coefficients including zero, and the truncated shift's original right-side integrability and tail assumptions are preserved. No new helper API is introduced. No compatibility aliases or forwarding modules were added.

Pins remain stock Lean **4.36.0-rc2**, Mathlib **048fffa1dbcd080d3058fab41d8c188168595c22**, and Tau Ceti **0642eae29e0a59ef798d04de325386445906e755**. No unmerged provider is consumed. A forward pin change remains a separate unresolved decision. The **56** Lean files contain **27,155 lines** including comments and blanks; four `Unused/` files account for **2,727**, leaving **24,428 active lines**. `Unused/` and IEANTN remain outside migration scope.

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

The current cleanup passes the local full library build, focused proof and module checks, and blueprint export. The preceding published baseline `afc97c4` passes hosted CI; hosted validation of this cleanup follows publication. Local strict checks cover the nine active affected library modules; the required unchanged `Unused` dependent is checked through its actual ordinary build. Its pre-existing unused-simp warning prevents claiming a strict pass for that whole closure; no excluded source or options were changed to suppress it.

The latest cleanup preserves all 961 retained declaration headers. All 229 physical blueprint artifacts retain their payloads, providers, primary/inner labels and paths; only 37 reviewed source ranges change. All 566 literal references, including the pre-existing external `WeakPNT` reference, and all 565 internal dependency edges remain unchanged. Both complete old-type recoveries, six literal caller interfaces and kernel comparisons, current selected-name absence, twelve edge cases, refreshed affected earlier witnesses, rectangle checks and all 37 named axiom requests pass; all 37 requests use only permitted axioms. The mathematical source grows by nine lines. All other source frames are unchanged. Detailed historical reports are archived separately; this summary does not claim a global rerun of every earlier recovery certificate.

Environment lint of the four changed modules reports missing docstrings on 35 unchanged definitions and the existing unused CompleteSpace argument of `RectanglePullToNhdOfPole'`. That caller's header and argument are unchanged, while its body intentionally changes. The environment lint therefore does not pass; no suppressions, unrelated repairs or separate baseline environment-lint run were made.
