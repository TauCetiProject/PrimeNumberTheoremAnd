We need approval of §§1.1, 1.3 and 1.6 of [SieveMethodsAndPrimePatterns (#1495)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1495) before we can migrate the sieve normalizer bounds, Selberg-weight estimates and interval-prime bound from PNT+ into Tau Ceti.

We also need approval of §§9.1, 11.3 and 11.4 of [AnalyticNumberTheoryPartIII (#2008)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2008) before we can migrate Mellin convolution, Ramanujan’s identity and the Dirichlet-series identities for `2^ω`, `μ²`, Liouville and totient from PNT+ into Tau Ceti.

We need §10.2 of #2008 extended to explicitly cover the Möbius and Liouville forms of the PNT, including ∑μ(n)/n → 0, before we can migrate those from PNT+.

Currently, the way these draft roadmaps are written, after #1495 we need to review and merge the following prerequisites before #2008, in this order:

1. [ExplicitZetaBounds (#1954)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1954).
2. [ArithmeticDirichletSeriesPartII (#1415)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1415).
3. [ProbabilisticAndMetricNumberTheory (#1421)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1421).
4. [ExplicitPrimeCounting (#1945)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1945).

Alternatively, we could write a fresh roadmap covering just these sieve, Mellin-convolution, Möbius/Liouville PNT, Ramanujan and Dirichlet-series results. That could potentially be reviewed and merged sooner, and we could rewrite the larger draft roadmaps to depend on it.
