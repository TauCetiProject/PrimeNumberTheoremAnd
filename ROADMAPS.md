# Roadmaps needed to finish the migration

Apart from the item below, every fork declaration outside `Unused/` is blueprint glue over
Mathlib and Tau Ceti. This material has no target yet; it needs a new roadmap section (or a target
line in an existing section) before it can move to Tau Ceti.

1. **Laplace-weighted sinc integral and pointwise Laplace inversion** (`LaplaceInversion.lean`,
   about 500 lines). The `arctan` block, `∫₀^∞ e^{−ax} sin x / x dx = arctan(1/a)` and its `a → 0⁺`
   limit, is offered to Mathlib as https://github.com/leanprover-community/mathlib4/pull/46525.
   Left after that: the two damped-sinc tail bounds, and the bilateral Laplace wrappers (the
   transform, its continuity on vertical lines, and truncated inversion on a line and in the `x^s`
   form under Dini hypotheses). Their reductions to Fourier inversion are proved from Mathlib's
   `mellin_eq_fourier` and Tau Ceti's `intervalIntegral_cpow_smul_mellin_eq`, the
   AnalyticNumberTheoryPartIII §7.3 step; §§7.2–7.3 state only the bounded-variation form.
