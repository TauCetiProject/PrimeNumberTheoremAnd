# Roadmaps needed to finish the migration

Most of the fork is covered by existing TauCetiRoadmap targets and is being upstreamed. The
following fork material has no target yet; each item needs a new roadmap section (or a target line
in the suggested existing section) before it can move to Tau Ceti.

1. **Elementary consequences of PNT for μ and λ** (`Consequences.lean`, about 750 lines): from
   `ψ(x) ∼ x`, `M(x) = o(x)`, `∑_{n≤x} μ(n)/n → 0` with `|∑_{n≤x} μ(n)/n| ≤ 1`, and `L(x) = o(x)`.
   Suggested home: a new AnalyticNumberTheoryPartIII §11.5, or the missing
   ExplicitMultiplicativeFunctions roadmap that ExplicitPrimeCounting already refers to.
2. **μ² as a divisor sum** (`IwaniecKowalskiCh1.lean`, about 150 lines): `μ²(n) = ∑_{d²∣n} μ(d)` and
   the unique decomposition `n = a²b` with `b` squarefree. A target line in AnalyticNumberTheoryPartIII
   §11.4, where it is only a Check.
3. **Laplace-weighted sinc integrals and pointwise Laplace inversion** (`LaplaceInversion.lean`,
   about 400 lines): `∫₀^∞ e^{−ax} sin x / x dx = arctan(1/a)` and its `a → 0⁺` limit, and
   vertical-line inversion at a point under Dini or continuity hypotheses. An extension of
   AnalyticNumberTheoryPartIII §§7.2–7.3, which state only the bounded-variation mean-limit form.
4. **Numerical constants for completed zeta** (`RiemannZetaValues.lean`): nonvanishing of
   `completedRiemannZeta₀` at `0` and `1`, with the bounds `γ > 27/50` and `log(4π) < 127/50`.
   A target under ZerosOfLFunctions §5.6 or a numerical-constants section of ExplicitZetaBounds.
5. **`ζ(2σ)/ζ(σ) ≤ |ζ(σ + it)|`** (used by `StrongPNT.lean`): one clause in ExplicitZetaBounds §3.4,
   where it is only a Check (§7.10).
6. **The Fourier-side space `W21`** (`Sobolev.lean`, about 200 lines): `‖f‖₁ + (4π²)⁻¹‖f''‖₁`
   test functions. An AnalyticNumberTheoryPartIII §7 test-function class.
