# Two connected polycubes

The next targets are co-r.e. completeness of tiling the height-2 slab and
full three-dimensional space with two connected polycubes. Neither
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
| The fixed 15-cube tile cannot tile the height-2 slab alone | [BumpyPolycubeSlab](LeanTrominoes/BumpyPolycubeSlab.lean) |
| Horizontal slab tilings yield planar slice tilings | [PolycubeHorizontalSlice](LeanTrominoes/PolycubeHorizontalSlice.lean) |
| Compatible planar layer tilings assemble into a slab tiling | [PolycubeLayerAssembly](LeanTrominoes/PolycubeLayerAssembly.lean) |
| Every admissible keyed Q becomes connected under its square cap | [KeyedPolycubeConnected](LeanTrominoes/KeyedPolycubeConnected.lean) |
| A capped Q fitting the height-2 slab is horizontal, with offset determined by its vertical reflection | [KeyedPolycubeSlabOrientation](LeanTrominoes/KeyedPolycubeSlabOrientation.lean) |
| A mixed tiling must use Q whenever P cannot tile alone | [PolycubePair](LeanTrominoes/PolycubePair.lean) |
| Exhaustive covering candidates and inverse-coordinate membership | [PolycubeCovering](LeanTrominoes/PolycubeCovering.lean) |

The capped Q proof includes the keys protruding outside the square cap.
It does not assume that the disconnected planar Q is contained in the cap.

The foundation audit in `tmp/PolycubeFoundationAudit.lean` completed with
exit code 0. Its log is `tmp/polycube-foundation-audit.log`. The audited
connectivity, slab non-tiling, and orientation theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The layer-assembly module also passed
a direct Lean check. No completeness claim follows from these lemmas alone.

## Next proof obligations

1. Finish the finite pocket certificates proving that the 45-cube tile
   cannot tile full space by itself. An arithmetic inverse-coordinate
   checker replaces the memory-intensive placed-finset computation.
2. Instantiate the layer-assembly theorem for the canonical planar P/Q
   construction and Q's square caps.
3. Prove the height-2 slab lock-forcing lemmas, including exclusion of a
   vertically reflected cap covering a simulation-layer lock. Propagate
   the forced background placements and recover a planar tiling.
4. Certify the finite output compiler and the 3D finite-search/compactness
   upper bound, then close height-2 slab co-r.e. completeness.
5. Give explicit vertical keys and locks for full 3D, verify all allowed
   orientations, and prove stacked-grid forcing and simulation recovery.
6. Extend the slab argument to each fixed height greater than two.

The 3D space construction and the taller-slab assertions remain open.
