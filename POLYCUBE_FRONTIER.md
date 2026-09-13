# Two connected polycubes

Tiling the height-2 slab with two connected polycubes is proved co-r.e.
complete by `TwoConnectedPolycubes.slabTwoProved` in
[TwoConnectedPolycubesSlabProof.lean](LeanTrominoes/TwoConnectedPolycubesSlabProof.lean).
Full three-dimensional space has a co-r.e. upper bound, but its hardness
construction remains open. The target propositions are defined in
[TwoConnectedPolycubes.lean](LeanTrominoes/TwoConnectedPolycubes.lean).

Inputs explicitly list the variable tile's voxels. The predicates reject
empty or face-disconnected tiles and allow all cube rotations and reflections.
The fixed tiles are the 15-voxel single layer of P and its 45-voxel
thickness-three extrusion, respectively.

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

The intended recovery uses a complete horizontal background grid. Its two
solid cap layers would isolate three simulation layers, potentially avoiding
vertical keys and stacked-grid forcing entirely. This recovery is not yet
proved. Exploratory searches at period 96 support both side-neighbor rules;
they are not used as trusted proof certificates.

## Next proof obligations

1. Lift the cap and finite key obstructions to arbitrary periods and actual
   placements, forcing horizontal background neighbors.
2. Complete the horizontal grid by compactness and recover the planar source
   tiling between its solid caps.
3. Construct full-space tilings by periodically stacking the forward simulation,
   certify its output compiler, and combine hardness with `space_coRE`.
4. Extend slab hardness to each fixed height greater than two.

The 3D space construction and the taller-slab completeness assertions remain open.
