We need approval of §§11.3 and 11.4 of [AnalyticNumberTheoryPartIII (#2008)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2008) before we can migrate Ramanujan’s identity and the Dirichlet-series identities for `2^ω`, `μ²`, Liouville and totient from PNT+ into Tau Ceti.

We need §10.2 of #2008 extended to explicitly cover the Möbius and Liouville forms of the PNT, including ∑μ(n)/n → 0, before we can migrate those from PNT+.

Currently, the way these draft roadmaps are written, we need to review and merge the following prerequisites before #2008, in this order:

1. [ExplicitZetaBounds (#1954)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1954).
2. [ExplicitPrimeCounting (#1945)](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1945). We also need §0.3b before we can migrate the nth-prime asymptotic from PNT+ into Tau Ceti.

Alternatively, we could write a fresh roadmap covering just these Möbius/Liouville PNT, nth-prime asymptotics, Ramanujan and Dirichlet-series results. That could potentially be reviewed and merged sooner, and we could rewrite the larger draft roadmaps to depend on it.
