# Two connected polycubes

[TwoConnectedPolycubes.spaceProved](../LeanTrominoes/TwoConnectedPolycubesSpaceProof.lean)
proves co-r.e. completeness in full 3D space.
[TwoConnectedPolycubes.slabsProved](../LeanTrominoes/TwoConnectedPolycubesSlabsProof.lean)
proves it for every fixed slab height greater than one; the height-two case
is also exposed by [slabTwoProved](../LeanTrominoes/TwoConnectedPolycubesSlabProof.lean).

The [target predicates](../LeanTrominoes/TwoConnectedPolycubes.lean) take an
explicit voxel list for Q and reject empty or face-disconnected inputs.
All 48 cube rotations and reflections are allowed. P is fixed: 15 voxels at
height two, 30 at height three, and 45 at greater heights and in full space.

## Construction and recovery

[PolycubeExtrusion](../LeanTrominoes/PolycubeExtrusion.lean) extrudes the planar
bumpy tile and adds square caps to the keyed planar complement Q. The caps
join Q's components, including keys that protrude beyond the cap footprint.
[PolycubeConnectivity](../LeanTrominoes/PolycubeConnectivity.lean) supplies
spanning-tree and cap-attachment criteria.

At height two, Q occupies the bottom layer and its cap the upper layer.
Orientation constraints and side locks force a horizontal grid of Q copies.
Compactness extends a forced quadrant to a complete grid, whose caps leave
a planar simulation layer. The forward and reverse directions are assembled
in [TwoConnectedPolycubesSlabGeometry](../LeanTrominoes/TwoConnectedPolycubesSlabGeometry.lean).

For full space, Q occupies layers 0, 1, and 2, with square caps at -1 and 3.
[KeyedPolycubeSpaceNormalization](../LeanTrominoes/KeyedPolycubeSpaceNormalization.lean)
normalizes an arbitrary seed, propagates the locks, and obtains a complete
horizontal grid. [KeyedPolycubeSpaceRecovery](../LeanTrominoes/KeyedPolycubeSpaceRecovery.lean)
recovers the planar tiling between cap planes. Connected placements cannot
cross the caps; height and middle-layer obstructions exclude unwanted tiles.
[KeyedPolycubeSpaceForward](../LeanTrominoes/KeyedPolycubeSpaceForward.lean)
constructs the converse by repeating compatible five-layer bands.

Taller slabs thicken Q's cap. Height three uses the two-layer P; heights at
least four use the three-layer P. The cap must be wider than the slab.
[KeyedComplementRepeatMask](../LeanTrominoes/KeyedComplementRepeatMask.lean)
enlarges the period without changing the periodic holes, preserving the
geometric promises. [TallSlabCompilerCorrectness](../LeanTrominoes/TallSlabCompilerCorrectness.lean)
proves the resulting exact source equivalence.

## Computability and upper bound

The explicit voxel-list compilers are primitive recursive:

| Region | Compiler |
| --- | --- |
| Height two | [TwoConnectedPolycubesSlabCompiler](../LeanTrominoes/TwoConnectedPolycubesSlabCompiler.lean) |
| Full space | [TwoConnectedPolycubesSpaceCompiler](../LeanTrominoes/TwoConnectedPolycubesSpaceCompiler.lean) |
| Taller slabs | [TallSlabVoxelCompiler](../LeanTrominoes/TallSlabVoxelCompiler.lean) |

Their hardness proofs compose with the existing Wang source reduction.
[TwoConnectedPolycubesUpperBound](../LeanTrominoes/TwoConnectedPolycubesUpperBound.lean)
combines primitive-recursive finite patch search and face-connectivity checks.
Inside-region voxels have exactly one cover; outside voxels have none.
Compactness converts successful searches at all radii to an exact tiling.
This works for every primitive-recursive voxel region.

## Validation

The height-two, full-space, and all-slabs completion builds passed, as did
the public import checks. The geometric, connectivity, and compiler audits
used only `propext`, `Classical.choice`, and `Quot.sound`. Finite geometric
certificates use kernel reduction. Completeness also inherits native checks
from the source reduction and Wang theorem; the audits found no `sorryAx`
or new native axiom.

```sh
lake build +LeanTrominoes.TwoConnectedPolycubesSpaceProof:olean +LeanTrominoes.TwoConnectedPolycubesSlabsProof:olean
```

Use `#print axioms` on the fully qualified final declarations to inspect
current dependencies. The translation-only extension is described in
[Corollary 5.9](corollary-5.9.md). See [README](../README.md) for paper coverage.
