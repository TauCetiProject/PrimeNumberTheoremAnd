# Roadmaps needed to finish the migration

Most of the fork is covered by existing TauCetiRoadmap targets and is being upstreamed. The
following fork material has no target yet; each item needs a new roadmap section (or a target line
in the suggested existing section) before it can move to Tau Ceti.

1. **μ² as a divisor sum** (`IwaniecKowalskiCh1.lean`, about 150 lines): `μ²(n) = ∑_{d²∣n} μ(d)`,
   with multiplicativity and prime-power evaluations for the divisor sum. A target line in AnalyticNumberTheoryPartIII
   §11.4, where it is only a Check.
2. **Laplace-weighted sinc integral and pointwise Laplace inversion** (`LaplaceInversion.lean`,
   about 500 lines): `∫₀^∞ e^{−ax} sin x / x dx = arctan(1/a)` and its `a → 0⁺` limit, and the
   bilateral Laplace line-inversion wrappers (truncated inversion on a vertical line and in the
   `x^s` form, under Dini hypotheses), now derived from Tau Ceti's Dini Fourier inversion. An
   extension of AnalyticNumberTheoryPartIII §§7.2–7.3, which state only the bounded-variation
   mean-limit form.
