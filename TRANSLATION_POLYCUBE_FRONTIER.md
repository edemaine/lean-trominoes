# Corollary 5.9: three connected polycubes by translation

The target definitions are in
[ThreeTranslationPolycubes.lean](LeanTrominoes/ThreeTranslationPolycubes.lean).
The final proofs are `spaceProved`, `slabsProved`, and `proved` in namespace
`LeanTrominoes.ThreeTranslationPolycubes`, exposed by
[ThreeTranslationPolycubesProof.lean](LeanTrominoes/ThreeTranslationPolycubesProof.lean).

Inputs explicitly list the variable polycube Q's voxels. The predicates
reject empty or face-disconnected Q and allow only identity-symmetry
placements of the three tiles. The two fixed tiles are horizontal and
vertical extrusions of the bumpy 15-omino. Each has 15 voxels at slab height
two, 30 at height three, and 45 at every greater height and in full space.
`ThreeTranslationPolycubeFixed` proves their connectivity, cardinalities,
and distinctness with kernel-checked finite certificates.

## Reduction

`VoxelTranslationTiling` defines restricted and translation-only tilings.
`ThreeTranslationPolycubeGeometry.translationTileable_iff` replaces all eight
horizontal orientations of the bumpy tile by translations of its two fixed
orientations, while requiring Q to remain unturned. Placement replacement
preserves exact footprints, coverage, and disjointness.

`ThreeTranslationPolycubeForward` constructs restricted tilings in the
height-two slab, every taller slab, and full space. Compatible planar layer
tilings give the slabs; full space uses five-layer bands and vertical
stacking. The construction tracks the allowed orientations throughout.

`ThreeTranslationPolycubeCompiler` proves correctness of the existing
primitive-recursive connected-polycube compilers against the new predicates.
For taller slabs, the repeated hole mask enlarges the period beyond the
height without changing the simulated region. The reverse implications
use the previously proved unrestricted two-polycube recovery theorems.
`ThreeTranslationPolycubeHardness` composes these compilers with the existing
Wang-to-planar reduction to establish co-r.e. hardness.

## Upper bound

`TranslationVoxelSearch` adds the orientation restriction to finite patch
search. Its compactness proof requires every forbidden placement to remain
absent. The finite checker is primitive recursive for any primitive-recursive
voxel region, including full space and each fixed slab.
`ThreeTranslationPolycubeUpperBound` combines this search with the existing
connectivity checker to prove co-r.e. membership.

## Validation

`lake build +LeanTrominoes.ThreeTranslationPolycubesProof:olean` passed
(4738 jobs). The public import passed `lake env lean LeanTrominoes.lean`.
The axiom audit in `tmp/ThreeTranslationPolycubeAudit.lean`
passed with no `sorryAx`. The upper bounds, orientation equivalence,
fixed-tile properties, and restricted forward constructions use only
`propext`, `Classical.choice`, and `Quot.sound`.

The combined completeness proof reports 4435 inherited native-check
dependencies, exactly those already present in the two-connected-polycube
space/slab completeness proofs. No new axiom or `native_decide` call was
introduced. The comparison is recorded in
`tmp/ThreeTranslationPolycubeInheritedAudit.lean` and the corresponding
`tmp/three-translation-polycube-*-audit.log` files.
