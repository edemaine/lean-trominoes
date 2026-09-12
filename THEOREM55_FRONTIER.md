# Theorem 5.5: plane tiling by a connected and a disconnected polyomino

The plane target is `LeanTrominoes.Theorem55.planeStatement`, defined in
[Theorem55.lean](LeanTrominoes/Theorem55.lean). It fixes the connected
15-omino P and takes an explicit list of cells for Q. Empty and connected
Q inputs are rejected. **The plane co-r.e.-completeness theorem is proved** by
`LeanTrominoes.Theorem55.planeProved` in
[Theorem55Proof.lean](LeanTrominoes/Theorem55Proof.lean).

## Established geometric reduction

[Theorem55Geometry.lean](LeanTrominoes/Theorem55Geometry.lean) proves:

- `Theorem55.pair_tileable_iff`: the explicit P/Q pair tiles the plane iff
  I trominoes tile the source, assuming the square-periodic mask is its cross
  refinement, the holes avoid the reserved corners, and the period is at least
  96 and divisible by three.
- `Theorem55.planeProblem_iff_of_source_square`: a source 2-by-2 block away
  from the period boundary additionally certifies Q's disconnectedness, giving
  equivalence with the exact target predicate, including its connectivity check.

Both results permit all rotations and reflections. The geometric promises are
now established for the concrete hard-source presentations, with a certified
computable finite tile construction.

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
| `KeyedPeriodicComplement.recover_tromino_of_grid` | A mixed tiling containing the canonical Q grid recovers an I-tromino tiling of the source. Additional Q placements are excluded. |
| `KeyedPeriodicComplement.tile_nonempty` | Every admissible Q is nonempty. |
| `KeyedPeriodicComplement.tile_disconnected_of_source_square` | A source 2-by-2 block away from the period boundary isolates a 2-by-2 component of Q and proves Q disconnected. |
| `KeyCornerArithmetic.vertical_match`, `right_match` | Occupied corner witnesses force the unique matching Q orientation and offset, uniformly for all allowed periods. |
| `KeyedPeriodicComplement.vertical_neighbor`, `right_neighbor` | In a mixed tiling, each lock forces the corresponding neighboring Q. |
| `KeyedPeriodicComplement.quadrant_placements` | The forced neighbors propagate through a canonical quadrant. |
| `KeyedPeriodicComplement.exists_tiling_with_grid` | Compactness produces a new mixed tiling containing the entire canonical Q grid. |

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

[KeyCornerFinite.lean](LeanTrominoes/KeyCornerFinite.lean) combines four
independently checked certificate modules, covering direct and reflected
orientations for each lock. Each module splits the first coordinate and checks
the remaining finite row with `decide +kernel`. No native evaluation axiom is
used. [KeyCornerArithmetic.lean](LeanTrominoes/KeyCornerArithmetic.lean) then
transfers the certificates to arbitrary allowed periods using compression.

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

[KeyedComplementGridCompactness.lean](LeanTrominoes/KeyedComplementGridCompactness.lean)
recenters the forced quadrant to realize arbitrarily large centered Q-grid
patches. Compactness gives a new tiling containing all canonical Q placements;
the solid-square exclusion eliminates any additional Q. This does not assert
that the original mixed tiling already had a complete global Q grid.

## Source margins

[PeriodicThreeDMNormalizationBlankMargin.lean](LeanTrominoes/PeriodicThreeDMNormalizationBlankMargin.lean)
proves that the actual normalized drawing lookup is blank when the horizontal
coordinate modulo 12 lies in `[7,11]` and the vertical coordinate modulo 12
lies in `[1,5]`. The proof follows the final normalization round, including
its local templates and magnified routes; it assumes no extra source promise.

[PeriodicThreeDMSourceBlankRegion.lean](LeanTrominoes/PeriodicThreeDMSourceBlankRegion.lean)
transfers this to the substituted tromino region: residues `[42,71] × [6,35]`
modulo 72 contain no source cells. Translating the origin to `(54,18)` gives
the empty rectangle `[-12,18)²`. Both the drawing and source-region results
use only the standard axioms; the paper-pixel bounds are checked in the kernel.

[Theorem55SourcePreparation.lean](LeanTrominoes/Theorem55SourcePreparation.lean)
centers the source there and adds a periodic 2-by-3 rectangle at `(14,4)`.
`Theorem55Source.tileable_iff` proves exact preservation of source tileability;
`source_square` supplies the required 2-by-2 block, and `blank_corners` proves
that all corner neighborhoods remain empty. The padding proof handles every
orientation of an I tromino and uses a blank gap to exclude mixed placements.

[Theorem55SourceMask.lean](LeanTrominoes/Theorem55SourceMask.lean) constructs
the finite mask of the cross-refined source and proves its exact periodic
carrier and all corner promises. `Theorem55Source.planeProblem_iff` therefore
applies the geometric reduction to every concrete source presentation without
additional geometric hypotheses, including Q's disconnectedness.

## Computable reduction

[Theorem55Compiler.lean](LeanTrominoes/Theorem55Compiler.lean) gives the
executable cell list, and [Theorem55CompilerComputability.lean](LeanTrominoes/Theorem55CompilerComputability.lean)
certifies it primitive recursive. [Theorem55Hardness.lean](LeanTrominoes/Theorem55Hardness.lean)
composes it with the existing Wang source and proves `Theorem55.coREHard`.
The new geometric and compiler certificates use only the standard axioms;
the composed hardness theorem inherits native-evaluation certificates from
the existing source reduction and Wang theorem.

## Upper bound and completion

[PlaneTilingFiniteSearch.lean](LeanTrominoes/PlaneTilingFiniteSearch.lean)
enumerates the placements that can cover each finite box and all subsets of
those candidates. Compactness proves that consistent coverage of every box
is equivalent to a plane tiling, for any pair of finite shapes.
[PlaneTilingSearchComputability.lean](LeanTrominoes/PlaneTilingSearchComputability.lean)
certifies the search primitive recursive and proves the general co-r.e. upper bound.

[PolyominoConnectivitySearch.lean](LeanTrominoes/PolyominoConnectivitySearch.lean)
characterizes disconnectedness of a nonempty shape by a nontrivial cut closed
under side adjacency. Its [computability certificate](LeanTrominoes/PolyominoConnectivityComputability.lean)
enumerates all cuts. [Theorem55UpperBound.lean](LeanTrominoes/Theorem55UpperBound.lean)
combines the connectivity and finite-tiling checks, including rejection of
empty inputs, to prove `Theorem55.coRE`. Together with `Theorem55.coREHard`,
this closes `Theorem55.planeProved` without geometric or compiler hypotheses.

The construction modules and public root are checked with Lean 4.31.0.
The completion audit checks for `sorryAx` and compares the theorem's axioms
with the existing Theorem 5.2 plane proof. The upper bound uses only the
standard axioms; the completed theorem adds no axioms to that source proof.

## Remaining paper results

The strip PSPACE assertion and the translation-only corollary are later
targets. No unproved compiler, drawing, grid-forcing, or complexity witness
is being treated as a completed theorem.
