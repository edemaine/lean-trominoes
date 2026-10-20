/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricPlaneCompleteness
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricLineHardness
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricMembership

/-! # Faithful supplied-drawing SAT classifications

The four plane classifications imported above are co-r.e.-complete. Their
four line variants below are PSPACE-complete under the same original flat
binary encodings. Every supplied drawing is orthogonal, continuously planar,
and has no coincident lifted listed points except at outer route endpoints.
The existing intrinsic linear grid and occurrence restrictions are retained.
-/
namespace LeanTrominoes.PeriodicPlanarSAT

 theorem geometricOrdinary_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding
    (Geometric Orbit.LocalOneDimensionalProblem) :=
  ⟨GeometricMembership.ordinary_inPSPACE,geometricOrdinary_PSPACEHard⟩

 theorem geometricOrdinaryThree_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding
    (Geometric Orbit.LocalOneDimensionalThreeOccurrenceProblem) :=
  ⟨GeometricMembership.ordinaryThree_inPSPACE,geometricOrdinaryThree_PSPACEHard⟩

 theorem geometricExactOne_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding
    (Geometric Unbounded.LocalOneDimensionalExactOneProblem) :=
  ⟨GeometricMembership.exactOne_inPSPACE,geometricExactOne_PSPACEHard⟩

 theorem geometricExactOneThree_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding
    (Geometric Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem) :=
  ⟨GeometricMembership.exactOneThree_inPSPACE,geometricExactOneThree_PSPACEHard⟩

end LeanTrominoes.PeriodicPlanarSAT
