# Theorem 5.5: plane tiling by a connected and a disconnected polyomino

The plane target is `LeanTrominoes.Theorem55.planeStatement`, defined in
[Theorem55.lean](LeanTrominoes/Theorem55.lean). It fixes the connected
15-omino P and takes an explicit list of cells for Q. Empty and connected
Q inputs are rejected. **The co-r.e.-completeness theorem is not yet proved.**

## Established construction

[Theorem55Construction.lean](LeanTrominoes/Theorem55Construction.lean)
exposes the proved geometric components:

| Declaration | Result |
| --- | --- |
| `Theorem55.smallTile_properties` | P has 15 cells, is side-connected, and cannot tile the plane, including with rotations and reflections. |
| `PlusRefinement.bumpy_tileable_refinement_iff` | For every region E, P tiles its cross refinement iff I trominoes tile E. No periodicity assumption is needed. |
| `KeyedPeriodicComplement.grid_tiling` | The canonical translates of the explicit keyed Q tile exactly the complement of the square-periodic holes. |
| `KeyedPeriodicComplement.tile_bounds` | Q is contained in `[-4,n) × [0,n+4)`. |
| `KeyedPeriodicComplement.bumpy_cannot_fill_vertical_lock` | P cannot cover the bottom of the vertical lock without overlapping its occupied 5-by-5 patch. |
| `KeyedPeriodicComplement.bumpy_cannot_fill_right_lock` | The analogous obstruction for the right lock, in coordinates reflected from the right edge. |
| `Theorem55.pair_tileable_of_tromino` | The forward construction, given an identification of the refined region with the square-periodic mask. |
| `Theorem55.background_occurs` | Every mixed plane tiling uses Q. |
| `Theorem55.recover_tromino_of_background` | Extracts the original I-tromino tiling once the actual Q placements tile the intended complement. |
| `KeyedPeriodicComplement.tile_upper`, `lower_tile` | The actual Q lies between the matching envelopes when the holes satisfy `AdmissibleHoles`. |
| `KeyedPeriodicComplement.tile_not_inside_refinement` | A rigid copy of Q cannot lie entirely in a refined region: its reserved corner contains a 2-by-2 block. |

The two keys move the five cells of each lock across a period boundary.
The residue-representative proof establishes exact coverage and disjointness
for every positive period and every finite hole mask. This forward proof
does not require the geometric promises used by the reverse direction.

## Corner-matching proof organization

[KeyCornerGeometry.lean](LeanTrominoes/KeyCornerGeometry.lean) defines
upper and lower envelopes for Q. The upper envelope fills the square
except for the locks and includes the protruding keys. The lower envelope
keeps the modulo-three background and four solid 18-by-18 corner patches.
[KeyedComplementEnvelope.lean](LeanTrominoes/KeyedComplementEnvelope.lean)
proves both inclusions for the constructed Q. Its `AdmissibleHoles` promise
requires the holes to lie on the cross grid and avoid the reserved corners.

[KeyCornerCompression.lean](LeanTrominoes/KeyCornerCompression.lean)
reduces these local envelope tests at arbitrary periods `n ≥ 96` to period
96. It preserves all relevant inequalities, equalities, and residues for
coordinate perturbations of magnitude at most 16. Residue preservation
requires `n % 3 = 0`.

The vertical lock has six occupied witnesses, measured relative to its
cell `(2,3)`:
`(1,0), (0,1), (-1,-1), (-1,1), (4,-2), (-1,0)`.
The right lock has seven witnesses relative to `(n-4,2)`:
`(1,0), (-9,1), (-1,-1), (0,13), (0,-2), (-1,1), (1,-1)`.

## Compactness and normalization

[TilingPrescribedCompactness.lean](LeanTrominoes/TilingPrescribedCompactness.lean)
proves `TilingSelection.exists_tiling_of_prescriptions` for any finite family
of finite polyominoes: increasing requirements on selected placements can
be imposed simultaneously if each stage is realized by a plane tiling.
The proof uses the compact product of Boolean placement selections; exact
coverage is closed because each cell has finitely many candidate placements.

[TilingPairNormalization.lean](LeanTrominoes/TilingPairNormalization.lean)
proves `tileable_pair_normalize`: when P cannot tile alone, a rigid change
of coordinates puts a Q at the origin in its original orientation.
The supporting translation and symmetry lemmas preserve exact tilings.

## Remaining work

1. Complete and validate the finite reference matching certificates and
   their uniform consequences in `KeyCornerFinite` and `KeyCornerArithmetic`.
2. Combine the proved envelope bounds and matching lemmas with the P lock
   obstructions to force neighbors
   in arbitrary mixed P/Q tilings, allowing all eight symmetries.
3. Apply the proved compactness theorem to increasingly large Q-grid
   patches obtained by recentering the forced quadrant. The resulting
   mixed tiling contains the entire canonical Q grid. Then
   `tile_not_inside_refinement` excludes additional Q placements and
   `recover_tromino_of_background` extracts the source tiling.
   This connection still needs proof. Above/right closure alone must not
   be treated as a proof of a complete global Q grid in the original tiling.
4. Connect the concrete hard instances from the proof of Theorem 5.2 to
   square masks with sufficient empty corner margins and period at least
   96 divisible by three. Prove these guarantees for the actual construction.
   The abstract completeness statement of 5.2 does not provide them.
5. Ensure Q is nonempty and disconnected on every reduction output. A
   separated, independently I-tileable square can provide a bounded
   component of Q; its isolation and preservation of source tileability
   need proofs.
6. Certify the computable reduction and co-r.e. membership of the target
   two-tile problem, then close `Theorem55.planeStatement`.

The strip PSPACE assertion and the translation-only corollary are later
targets. No unproved compiler, drawing, grid-forcing, or complexity witness
is being treated as a completed theorem.
