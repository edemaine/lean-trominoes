import LeanTrominoes.Lemma51
import LeanTrominoes.PeriodicGeneralAugmentingPath
import LeanTrominoes.PeriodicTwoSATLocalTime
import LeanTrominoes.PeriodicBipartitionDoubling
import LeanTrominoes.PeriodicShortAugmentingProperties
import LeanTrominoes.PeriodicMatchingSolver
import LeanTrominoes.PeriodicMatchingPeriodOne
import LeanTrominoes.PeriodicHornLinearTime
import LeanTrominoes.PeriodicHornDecision
import LeanTrominoes.PeriodicThreeDMPlanarLineCompleteness
import LeanTrominoes.PeriodicThreeDMLineCompleteness
import LeanTrominoes.NormalizedOrientationLineMembership
import LeanTrominoes.PeriodicThreeDMLineDecision
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.PeriodicPlanarOrdinaryLinePolySpaceCompleteness
import LeanTrominoes.PeriodicPlanarExactOneLinePolySpaceCompleteness
import LeanTrominoes.PeriodicPlanarSATInjectiveRenaming
import LeanTrominoes.PeriodicCNFStripNativeVariableFields
import LeanTrominoes.PeriodicPlanarSATEncodingCompiler
import LeanTrominoes.PeriodicOneInThreePolyTimeSemantics
import LeanTrominoes.PeriodicExactOneThreePolySpaceMembership
import LeanTrominoes.PeriodicExactOnePolySpaceCompleteness
import LeanTrominoes.PeriodicPlanarBoundedLocalCompleteness
import LeanTrominoes.PeriodicPlanarLocalExactOneCompleteness
import LeanTrominoes.PeriodicPlanarLocalThreeOccurrenceCompleteness
import LeanTrominoes.PeriodicThreeSATThreePolySpaceCompleteness
import LeanTrominoes.PeriodicCNFFlatFieldCountSpace
import LeanTrominoes.PeriodicPlanarThreeOccurrenceCompleteness
import LeanTrominoes.PeriodicCNFLinePacked
import LeanTrominoes.PeriodicPlanarSATCompleteness
import LeanTrominoes.PeriodicPlanarExactOneCompleteness
import LeanTrominoes.CompletionAperiodic
import LeanTrominoes.CompletionStripHardness
import LeanTrominoes.CompletionStripPrefillValidity
import LeanTrominoes.CompletionCompleteness
import LeanTrominoes.CompletionLCompilerValidity
import LeanTrominoes.CompletionICompilerValidity
import LeanTrominoes.Theorem52Proof
import LeanTrominoes.TwoTranslationTrominoes
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicSATPlaneCompleteness
import LeanTrominoes.PeriodicOneInThreeCompleteness
import LeanTrominoes.PeriodicThreeDMPlaneCompleteness
import LeanTrominoes.NormalizedOrientationCompleteness
import LeanTrominoes.Theorem55Proof
import LeanTrominoes.Theorem55StripProof
import LeanTrominoes.ThreeTranslationProof
import LeanTrominoes.ThreeTranslationPolycubesProof
import LeanTrominoes.TwoConnectedPolycubesSlabProof
import LeanTrominoes.TwoConnectedPolycubesSpaceProof
import LeanTrominoes.TwoConnectedPolycubesSlabsProof

import LeanTrominoes.PeriodicPlanarSATLineReduction
import LeanTrominoes.PeriodicPlanarSATLineDecision
import LeanTrominoes.PeriodicDrawingPolySpaceVerification
import LeanTrominoes.PeriodicPlanarSATBoundedComponentVerification
import LeanTrominoes.PeriodicPlanarSATLinePolySpaceMembership
import LeanTrominoes.PeriodicPlanarSATRouteObligation
import LeanTrominoes.PeriodicExactOneCNFFlatSize
import LeanTrominoes.PeriodicExactOneLineReduction

/-!
# Main theorem interface

`PeriodicTrominoPrefill.planeProblem_coREComplete` proves co-r.e. completeness
of periodic L- and I-tromino completion in the plane. `compileDrawing_valid`
in `CompletionPattern.LBricks` and `CompletionPattern.IBricks` proves that
every hardness reduction output is a valid partial tiling.
`PeriodicTrominoPrefill.exists_aperiodic_completion` proves that each tromino
admits a valid periodic prefill whose completions exist but have no nonzero
translation period.
`PeriodicStripTrominoPrefill.problem_PSPACEComplete` proves strip completion
PSPACE completeness under the explicit unary encoding for both trominoes.
`CompletionPattern.StripOrientation.compile_valid` proves validity of every
strip reduction output, including those for unsatisfiable inputs.

`Theorem52.proved` proves the complete plane and strip result, and
`Theorem52.stripProved` exposes strip PSPACE completeness. Import
`LeanTrominoes.Theorem52` separately to read only the target statements.
See README.md for the main declarations and docs/theorem-5.2.md for the
completed construction and validation.

`TwoTranslationTrominoes.proved` proves Corollary 5.3: tiling periodic
plane regions by translations of the horizontal and vertical I trominoes is
co-r.e. complete, and the strip problem is PSPACE complete.

`Theorem55.planeProved` proves co-r.e. completeness of plane tiling by a fixed
connected 15-omino and an input disconnected polyomino, allowing rotations
and reflections. `Theorem55.stripProved` proves PSPACE completeness of the
corresponding strip problem under its original unary encoding. See
docs/theorem-5.5.md for the construction and validation.

`ThreeTranslationPolyominoes.proved` proves Corollary 5.6: tiling by translations
of two fixed connected 15-ominoes and an input disconnected Q is co-r.e. complete
in the plane and PSPACE complete in strips. See docs/corollary-5.6.md.

`TwoConnectedPolycubes.slabTwoProved` proves co-r.e. completeness of tiling
the height-two slab with a fixed connected 15-voxel polycube and an input
connected polycube. `TwoConnectedPolycubes.spaceProved` proves full-space
co-r.e. completeness with a fixed connected 45-voxel polycube and an input
connected polycube. Both allow all cube rotations and reflections. See
docs/two-connected-polycubes.md.

`TwoConnectedPolycubes.slabsProved` proves co-r.e. completeness for every
fixed slab height greater than one. The fixed connected tile has at most
45 voxels, independently of the height.

`ThreeTranslationPolycubes.proved` proves Corollary 5.9: tiling full 3D space
or any fixed slab height greater than one by translations of three connected
polycubes is co-r.e. complete. Two tiles are fixed, each with at most 45 voxels.
See docs/corollary-5.9.md.

`WangPeriodicCNF.coREComplete` and `WangPeriodicCNF.localCoREComplete`
prove two-dimensional periodic CNF SAT co-r.e. completeness.
`PeriodicThreeCNF.localThreeCNFCoREComplete` and
`PeriodicThreeSATThree.localThreeSATThreeCoREComplete` prove the corresponding
local 3SAT and 3SAT-3 results. Together with the native flat-encoded one-dimensional PSPACE endpoints,
these complete Theorems 3.3–3.4.

`PeriodicPlanarSAT.ordinary_PSPACEComplete`, `ordinaryThree_PSPACEComplete`,
`exactOne_PSPACEComplete`, and `exactOneThree_PSPACEComplete` prove local
one-dimensional planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3 PSPACE
completeness, with supplied drawings under the native flat encoding and
the original fixed linear grid bounds.

`Gadget.NormalizedOrientation.lineProblem_PSPACEComplete` proves normalized
one-dimensional trichromatic orientation PSPACE-complete under the native binary
cell-table encoding, with separated vertices and a blank vertical boundary.

`PeriodicThreeDM.localPlanarLineProblem_PSPACEComplete` proves local planar
one-dimensional 3DM with colored degree 2 or 3 PSPACE-complete under the native
binary encoding, including verification of the complete supplied drawing.

`PeriodicTwoSAT.local_certified` proves Theorem 4.1 in every fixed dimension:
an executable local periodic 2SAT solver, with a complete polynomial bound of
degree `3(d*d+d+1)` in the explicit indexed input size. It includes clause
anchoring, an explicitly indexed finite lattice cover, and verified Horn
worklist reachability queries. Locality concerns offset differences, allowing
arbitrary common offsets. The cost model is the unit-cost indexed RAM.

`PeriodicLatticeGraph.bounded_augmenting_path` proves Lemma 4.3 in every
dimension, including general nonbipartite graphs. From each free vertex,
it gives a simple augmenting path of diameter at most `2*d*|E|`.

`PeriodicLatticeGraph.bipartition_two_periodic` proves Lemma 4.4 in every
dimension: a connected bipartite periodic graph's coloring is invariant under
twice any lattice translation.
`PeriodicBipartite.perfect_or_short_augmenting` proves Lemma 4.5 for arbitrary
period-one partial matchings of the infinite graph. The augmenting path has
free endpoints, unmatched forward edges, no repeated protovertex, and fewer
edges than the quotient has vertices.

`PeriodicBipartite.exists_period_one` proves Theorem 4.6 in every dimension.
`PeriodicBipartite.perfect_iff_quotient` characterizes perfect matchings by the
finite bipartite quotient, without a locality restriction.
`PeriodicBipartite.matchingSolver_certified` proves Theorem 4.7: an executable
indexed solver decides perfect matching and constructs a finite protoedge table
for a period-one matching, in every dimension. The complete unit-cost RAM
bound is `1000(E+1)(sqrt(V)+1)`; `matchingSolver_edge_sqrt_bound` gives
`4000E*sqrt(V)` for nonempty edge tables, including preparation and construction.

`Horn.exists_period_one` and `Horn.dual_exists_period_one` give constant models
for satisfiable periodic Horn and dual Horn formulas in every dimension.
`PeriodicCNF.hornCheck_correct` and `dualHornCheck_correct` certify executable
solvers on the existing periodic-CNF representation.
`Horn.PeriodicIndexed.certified` adds a linear operation bound for explicitly
indexed inputs in the unit-cost RAM model, including input preparation.
This does not assert a bit-Turing or Lean VM runtime bound.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/

/-!
`PeriodicSubspaceTiling.lemma51` packages Lemma 5.1: arbitrary finite-footprint
periodic subspace tiling and completion are co-r.e. in every dimension, and
both strip problems are in PSPACE for each fixed polynomial bounding box.
The strip inputs use native binary fields; the window-to-Savitch evaluator
has a run-level finite-alphabet Turing-machine space certificate.
-/
