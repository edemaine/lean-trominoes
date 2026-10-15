# SAT problems and reductions

Periodic CNF, 3SAT, occurrence-bounded SAT, exact-one SAT, and planar SAT from Section 3; 2SAT and Horn algorithms from Section 4. Finite and one-dimensional variants remain with their SAT family.

The reorganization placed 2,969 existing modules here.

Import `LeanTrominoes.SAT.Results` for the curated public results.

Useful entry points:

- [Plane completeness](CNF/PeriodicSATPlaneCompleteness.lean)
- [CNF PSPACE completeness](CNF/PeriodicCNFPolySpaceMembership.lean)
- [Planar SAT line reductions](Planar/PeriodicPlanarSATLineReduction.lean)
- [2SAT polynomial-time solver](TwoSAT/PeriodicTwoSATPolynomialTime.lean)
- [Horn linear-time certificate](Horn/PeriodicHornLinearTime.lean)

See the [repository organization guide](../../docs/organization.md) for the paper map, module migration, and validation commands.
