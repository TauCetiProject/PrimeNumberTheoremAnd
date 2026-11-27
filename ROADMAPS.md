# Roadmaps needed to finish the migration

Apart from the items below, every fork declaration outside `Unused/` is blueprint glue over
Mathlib and Tau Ceti. The following fork material has no target yet; each item needs a new roadmap
section (or a target line in the suggested existing section) before it can move to Tau Ceti.

1. **μ² as a divisor sum** (`IwaniecKowalskiCh1.lean`, about 150 lines): `μ²(n) = ∑_{d²∣n} μ(d)`,
   with multiplicativity and prime-power evaluations for the divisor sum. A target line in
   AnalyticNumberTheoryPartIII §11.4, where it is only a Check; that section's targets are on Tau Ceti
   main and do not imply it.
2. **Laplace-weighted sinc integral and pointwise Laplace inversion** (`LaplaceInversion.lean`,
   about 500 lines). The `arctan` block, `∫₀^∞ e^{−ax} sin x / x dx = arctan(1/a)` and its `a → 0⁺`
   limit, is offered to Mathlib as https://github.com/leanprover-community/mathlib4/pull/46525.
   Left after that: the two damped-sinc tail bounds, and the bilateral Laplace wrappers (the
   transform, its continuity on vertical lines, and truncated inversion on a line and in the `x^s`
   form under Dini hypotheses). Their reductions to Fourier inversion are proved from Mathlib's
   `mellin_eq_fourier` and Tau Ceti's `intervalIntegral_cpow_smul_mellin_eq`, the
   AnalyticNumberTheoryPartIII §7.3 step; §§7.2–7.3 state only the bounded-variation form.
