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

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/
