# Two connected polycubes

Tiling every fixed slab height greater than one with two connected polycubes
is proved co-r.e. complete by `TwoConnectedPolycubes.slabsProved` in
[TwoConnectedPolycubesSlabsProof.lean](LeanTrominoes/TwoConnectedPolycubesSlabsProof.lean).
Full three-dimensional space is proved co-r.e. complete by
`TwoConnectedPolycubes.spaceProved` in
[TwoConnectedPolycubesSpaceProof.lean](LeanTrominoes/TwoConnectedPolycubesSpaceProof.lean).
The target propositions are defined in
[TwoConnectedPolycubes.lean](LeanTrominoes/TwoConnectedPolycubes.lean).

Inputs explicitly list the variable tile's voxels. The predicates reject
empty or face-disconnected tiles and allow all cube rotations and reflections.
The fixed slab tile has 15 voxels at height two, 30 at height three, and
45 at every greater height. Full space also uses the 45-voxel tile.

## Established foundation

| Result | Module |
| --- | --- |
| Integer voxels, all 48 cube symmetries, inverse actions, finite placements | [PolycubeBasic](LeanTrominoes/PolycubeBasic.lean) |
| Cube-symmetry composition and inverses; arbitrary full-space seed normalization | [PolycubeSpaceSymmetry](LeanTrominoes/PolycubeSpaceSymmetry.lean) |
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
| Every full-space tiling admits a complete horizontal background grid | [KeyedPolycubeSpaceNormalization](LeanTrominoes/KeyedPolycubeSpaceNormalization.lean) |
| Arbitrary full-space tilings recover planar P/Q tilings | [KeyedPolycubeSpaceRecovery](LeanTrominoes/KeyedPolycubeSpaceRecovery.lean) |
| Periodic solid-cap bands construct full-space tilings | [KeyedPolycubeSpaceForward](LeanTrominoes/KeyedPolycubeSpaceForward.lean) |
| Primitive-recursive full-space tile compiler | [TwoConnectedPolycubesSpaceCompiler](LeanTrominoes/TwoConnectedPolycubesSpaceCompiler.lean) |
| Full-space co-r.e. completeness | [TwoConnectedPolycubesSpaceProof](LeanTrominoes/TwoConnectedPolycubesSpaceProof.lean) |

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

The upper bound uses finite subsets of all placements meeting a finite voxel
box. Inside-region voxels must have exactly one covering placement; outside
voxels must have none. Compactness converts successful searches for all
boxes into an exact tiling of the prescribed region. The finite search and
the face-connectivity cut test are certified primitive recursive. This proves
`problem_coRE` for every primitive-recursive voxel region, `slab_coRE` for
every fixed slab height, and `space_coRE` for full space.

## Validation of slab completeness

`lake build +LeanTrominoes.TwoConnectedPolycubesSlabProof:olean` completed
successfully (4638 jobs). `tmp/PolycubeSlabCompletenessAudit.lean` audits the
finite-search equivalence, search computability, connectivity computability,
both upper bounds, and the final completeness theorem. The search,
connectivity, and upper-bound proofs use only the three standard axioms.
The final theorem has exactly the same inherited native-decision certificates
as the hardness theorem, and no `sorryAx`. The public root module now imports
the slab result.

Full-space placement normalization is also available as
`IsVoxelTiling.normalize_space`: any selected tile can be moved to the origin
with identity orientation. Composition, inversion, and faithfulness of all
48 cube symmetries are certified on coordinate basis vectors with
`decide +kernel`; proved linearity extends the certificate to every voxel.
The three modules built successfully (727 jobs), and the finite certificates
took 236 seconds. `tmp/PolycubeSpaceSymmetryAudit.lean` audits composition,
inversion, and normalization; all three use only the standard axioms, with
no native-evaluation axiom.

## Full-space solid-cap construction

`KeyedPolycubeSpaceGeometry.spaceTile` places Q in layers 0, 1, and 2,
with solid square caps at -1 and 3. `spaceTile_connected` proves this actual
tile connected, including its protruding planar keys. The slab and space
proofs now share the key-attachment paths in `KeyedPolycubeKeyAttachment`;
the original slab connectivity theorem still builds.

`PolycubeSpaceKeyCertificates` checks that either five-cell protruding key,
extruded through three layers, overlaps a fixed occupied witness when it
tries to fill a side lock upright. `PolycubeSpaceSmallCertificates` checks
that the fixed 45-cube tile cannot fill either side lock in any orientation.
These are kernel-checked finite statements, not experimental searches.
The certificate target built successfully (860 jobs), and the connectivity
regression build succeeded (923 jobs). The audit in
`tmp/SpaceConstructionAudit.lean` confirms only the three standard axioms.

The side-neighbor rules are now proved for every admissible period. A uniform
cap-overlap lemma excludes upright copies sourced inside the square, and the
finite key certificates handle the protrusions. Exact slices force the planar
offset and align all three simulation layers. Vertical reflections of horizontal
background copies are canonicalized without changing their occupied cells.
`space_tileable_has_grid` normalizes an arbitrary full-space tiling, propagates
its background quadrant, and applies compactness to obtain the complete
horizontal background grid. No seed or orientation hypothesis remains.

The neighbor target built successfully (944 jobs), grid propagation (1137 jobs),
and normalization (1146 jobs). `tmp/SpaceLockAudit.lean` confirms that both exact
candidate and neighbor rules use only the three standard axioms. Recovery from
the two solid cap planes is now proved. `planar_tileable_of_space` recovers the
planar P/Q tiling from any full-space tiling. Connected placements cannot cross
the cap planes; any nongrid background tile is too tall, and any upright small
tile fitting between the planes contains a forbidden middle-layer 2-by-2 square.
The recovery target built successfully (1193 jobs), and
`tmp/SpaceRecoveryAudit.lean` confirms only the three standard axioms.

`space_tileable_of_holes` supplies the converse by repeating the compatible
three-body-layer/two-cap-layer tiling every five voxels vertically.
`space_tileable_iff_tromino` and `spaceProblem_iff_of_mask` establish the exact
geometric reduction. The geometry target built successfully (1212 jobs).

## Full-space completeness

`SpaceCompiler.compile` emits three copies of planar Q and its two square
caps as an explicit voxel list. Its primitive-recursiveness proof and exact
source-encoding theorem give `space_coREHard`. Combining this with the
existing finite-search upper bound gives `spaceProved`, now imported by
the public root module.

`lake build +LeanTrominoes.TwoConnectedPolycubesSpaceProof:olean` succeeded
(4666 jobs). `tmp/PolycubeSpaceCompletenessAudit.lean` checks both geometric
directions, the equivalence, compiler computability, the upper bound, and the
final theorem. All new geometric and compiler results use only the three
standard axioms. The final theorem inherits exactly the same 4406 native
certificates as slab completeness, with no new native axiom and no `sorryAx`.
`lake env lean LeanTrominoes.lean` also completed successfully, checking the
public import. The broader repository rebuild was interrupted while rebuilding
existing strip machinery; it is not claimed as a successful whole-repository
build. All eight artifacts affected by that interruption were restored by
successful direct Lean compilations before the public import check.

The rotation-allowing full-space and fixed-height slab assertions are complete.
The translation-only corollaries remain separate targets.


## All fixed slab heights

The taller-slab construction keeps the 45-voxel small tile for every height
at least four and thickens only Q's solid cap. Height three uses a 30-voxel
two-layer extrusion. `TwoConnectedPolycubes.slabSmall_not_tileable` proves
that the selected small tile cannot tile its slab for any height greater
than one. For the exceptional height three, finite kernel certificates show
that every boundary voxel forces the inward voxel, excluding upright copies.
The remaining horizontal tiling would contradict the planar obstruction.
For greater heights, repeating a slab tiling would contradict the existing
full-space obstruction. `tmp/TallSlabObstructionAudit.lean` confirms only the
three standard axioms for all these results.

The variable-cap geometry and both small-tile side-lock exclusions build
successfully (1043 jobs). Uniform background alignment, grid recovery,
connectivity, and forward assembly are now proved. The exact equivalence
`tall_slab_tileable_iff_tromino` builds for every height at least three,
provided the square cap is wider than the slab (1230 jobs).

`repeatMask_carrier` enlarges a period by repeating its holes without changing
the infinite region, and `repeatMask_admissible` preserves the cross-grid and
reserved-corner conditions. This supplies the larger periods needed for tall
slabs. `tmp/TallSlabGeometryAudit.lean` checks the equivalence, connectivity,
and both repetition lemmas; each uses only the three standard axioms.
`TallSlabCompiler.compile` explicitly enumerates the enlarged background's
body and cap voxels. It is primitive recursive for every fixed height, and
`compile_source_correct` proves exact equivalence with the original source.
`tall_slab_coREHard` composes this with the existing Wang reduction.
`slabsProved` combines the height-two theorem with this taller-slab hardness
and the generic slab upper bound. `slabSmall_connected` and
`slabSmall_card_le` certify that the fixed tile is connected and has at most
45 voxels at every height. The completeness target built successfully
(4699 jobs).

`tmp/AllSlabsCompletenessAudit.lean` checks the fixed-tile obstruction, exact
geometric equivalence, compiler primitive recursiveness and correctness,
connectivity, size bound, and final theorem. All new geometric and compiler
results use only the three standard axioms. The final theorem inherits
exactly the same 4406 native certificates as the full-space and height-two
results, with no new native axiom and no `sorryAx`.
`lake env lean LeanTrominoes.lean` also completed successfully, checking the
updated public import.
