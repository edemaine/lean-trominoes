# Two connected polycubes

The next targets are co-r.e. completeness of tiling the height-2 slab and
full three-dimensional space with two connected polycubes. Height-2 slab co-r.e. hardness is proved; neither
completeness theorem is proved yet. Their exact propositions are
`TwoConnectedPolycubes.slabTwoStatement` and
`TwoConnectedPolycubes.spaceStatement` in
[TwoConnectedPolycubes.lean](LeanTrominoes/TwoConnectedPolycubes.lean).

Inputs explicitly list the variable tile's voxels. The predicates reject
empty or face-disconnected tiles and allow all cube rotations and reflections.
The fixed tiles are the 15-voxel single layer of P and its 45-voxel
thickness-three extrusion, respectively.

## Established foundation

| Result | Module |
| --- | --- |
| Integer voxels, all 48 cube symmetries, inverse actions, finite placements | [PolycubeBasic](LeanTrominoes/PolycubeBasic.lean) |
| Exact tilings, disjointness, finite-height slabs | [PolycubeTiling](LeanTrominoes/PolycubeTiling.lean) |
| Extrusions, capped tiles, fixed-tile cardinalities | [PolycubeExtrusion](LeanTrominoes/PolycubeExtrusion.lean) |
| Face connectivity, spanning-tree certificates, cap attachment criterion | [PolycubeConnectivity](LeanTrominoes/PolycubeConnectivity.lean) |
| Both fixed tiles are connected | [BumpyPolycubeConnected](LeanTrominoes/BumpyPolycubeConnected.lean) |
| The fixed 45-cube tile cannot tile full 3D space alone | [BumpyPolycubeObstruction](LeanTrominoes/BumpyPolycubeObstruction.lean) |
| The fixed 15-cube tile cannot tile the height-2 slab alone | [BumpyPolycubeSlab](LeanTrominoes/BumpyPolycubeSlab.lean) |
| Horizontal slab tilings yield planar slice tilings | [PolycubeHorizontalSlice](LeanTrominoes/PolycubeHorizontalSlice.lean) |
| Compatible planar layer tilings assemble into a slab tiling | [PolycubeLayerAssembly](LeanTrominoes/PolycubeLayerAssembly.lean) |
| An I-tromino source tiling produces a height-2 slab tiling | [KeyedPolycubeForward](LeanTrominoes/KeyedPolycubeForward.lean) |
| Every admissible keyed Q becomes connected under its square cap | [KeyedPolycubeConnected](LeanTrominoes/KeyedPolycubeConnected.lean) |
| A capped Q fitting the height-2 slab is horizontal, with offset determined by its vertical reflection | [KeyedPolycubeSlabOrientation](LeanTrominoes/KeyedPolycubeSlabOrientation.lean) |
| Both locks force background neighbors with the same vertical orientation | [KeyedPolycubeSlabLocks](LeanTrominoes/KeyedPolycubeSlabLocks.lean) |
| An aligned background seed forces its entire canonical quadrant | [KeyedPolycubeSlabPropagation](LeanTrominoes/KeyedPolycubeSlabPropagation.lean) |
| A mixed tiling must use Q whenever P cannot tile alone | [PolycubePair](LeanTrominoes/PolycubePair.lean) |
| Exhaustive covering candidates and inverse-coordinate membership | [PolycubeCovering](LeanTrominoes/PolycubeCovering.lean) |

The capped Q proof includes the keys protruding outside the square cap.
It does not assume that the disconnected planar Q is contained in the cap.

The foundation audit in `tmp/PolycubeFoundationAudit.lean` completed with
exit code 0. Its log is `tmp/polycube-foundation-audit.log`. The audited
connectivity, slab non-tiling, and orientation theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The layer-assembly module also passed
a direct Lean check. No completeness claim follows from these lemmas alone.

The forward construction uses `square_grid_tiling` to cover the cap layer
at exactly the same canonical offsets as Q. The explicit placement union
is exposed by `isTiling_pair_of_complement`; the existing existential
plane theorem retains its statement. `tmp/PolycubeForwardAudit.lean`
checks the forward theorem and layer assembly, with output in
`tmp/polycube-forward-audit.log`. Both use only the three standard axioms.

The slab lock proof excludes a downward-facing cap using the two occupied
horizontal neighbors of each lock. It then applies the exposed planar
`vertical_candidate` and `right_candidate` lemmas to the exact zero-layer
footprint. The original planar neighbor theorems retain their statements.
`tmp/PolycubeSlabLocksAudit.lean` audits both slab neighbors and quadrant
propagation; all use only the three standard axioms. Its output is
`tmp/polycube-slab-locks-audit.log`.

The full-space obstruction uses the two pocket voxels in the middle layer
of the thickness-three extrusion. The finite certificates check every
reference orientation and every orientation/source-voxel candidate with
`decide +kernel`. An arithmetic membership predicate is proved equivalent
to actual voxel membership before it is used by the checker. Both certificate
modules built successfully (about 983 seconds each); the completed
`bumpyThree_not_tileable_space` theorem passed the audit in
`tmp/PolycubeSpaceObstructionAudit.lean`. Its log,
`tmp/polycube-space-obstruction-audit.log`, confirms only the three standard
axioms, with no native-evaluation axiom.

The slab recovery proof now normalizes any background placement by horizontal
translation, planar symmetry, and, when needed, reflection of the slab.
Compactness completes the forced quadrant to a full grid. Its square caps
occupy the upper layer, so the lower layer recovers a planar P/Q tiling.
`TwoConnectedPolycubesSlabGeometry` proves the resulting equivalence with
the source I-tromino problem. `TwoConnectedPolycubesSlabCompiler` certifies
the explicit voxel-list compiler as primitive recursive, and
`TwoConnectedPolycubesSlabHardness.slabTwo_coREHard` closes co-r.e. hardness.
The hardness target builds successfully. The audit in
`tmp/PolycubeSlabHardnessAudit.lean` checks recovery, geometric equivalence,
compiler computability, and hardness. Recovery, geometry, and compiler proofs
use only the three standard axioms. The final hardness theorem also inherits
the existing native-decision certificates in the planar source reduction
and LeanWang; this milestone adds none.

## Next proof obligations

1. Certify the voxel finite-search/compactness upper bound, then close
   height-2 slab co-r.e. completeness.
2. Give explicit vertical keys and locks for full 3D, verify all allowed
   orientations, and prove stacked-grid forcing and simulation recovery.
3. Extend the slab argument to each fixed height greater than two.

The 3D space construction and the taller-slab assertions remain open.
