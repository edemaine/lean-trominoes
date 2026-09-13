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

## Strip construction in progress

The plane tile has vertical keys as well as horizontal keys. The strip
construction instead uses `KeyedStripComplement.tile`: it moves only the
horizontal lock cells, leaving both bounded edges flat.
`KeyedStripComplement.grid_tiling` proves that its horizontal translates
tile exactly the complement of the horizontally repeated holes within the
full strip. `placement_orientation` excludes all quarter-turns and fixes
the vertical offset of every remaining orientation. These results build
successfully (805 jobs).

`plane_tileable_of_strip` repeats any positive-height strip tiling through
the plane. Consequently `PlusRefinement.bumpy_not_tileable_strip` excludes
a tiling by the fixed 15-omino alone, at every positive strip height.
`KeyedStripComplement.right_match` proves horizontal lock matching with
three occupied witnesses. Region normalization, forced row propagation,
and compactness give a tiling containing the complete canonical Q row.
`pair_tileable_iff` proves exact equivalence with the source I-tromino
tiling under the mask promises (1124 jobs). The isolated 2-by-2 component
also certifies Q disconnected (926 jobs). `tmp/StripGeometryAudit.lean`
checks this equivalence, disconnectedness, and the small-tile obstruction;
all use only the three standard axioms.

`Theorem55StripSource` now prepares every periodic-strip source: it shifts
the source ten rows upward, adds separated 2-by-3 padding rectangles, and
uses horizontal period `(width + 72) * period`. The mask is admissible,
its carrier is exactly the refined prepared source, and the preparation
preserves I-tromino tileability. No hard-source geometry promise is assumed.

`Theorem55StripCompiler.compile_correct` proves the exact reduction from
`PeriodicStripTrominoTiling .I` to `Theorem55.stripProblem`, including malformed
inputs. The compiler emits the actual cell list; `compile_primrec` proves
primitive recursiveness. `Theorem55StripEncoding.finEncoding` uses unary
height and signed-coordinate fields, with a proved decoding round trip.
`Theorem55.stripStatement` states PSPACE completeness under this encoding.

`compile_encoding_length_le` bounds the output length by
`(2 + 2*n²) * (n² + 2*n + 9)`, where
`n = 3 * (source.width + 72) * source.period`. The target builds successfully
(1703 jobs). `tmp/StripCompilerAudit.lean` checks compiler correctness,
primitive recursiveness, the size bound, and the unary parser round trip;
all use only the three standard axioms.

The PSPACE-completeness assertion remains open. The next obligations are:

- Certify a polynomial-time machine for the compiler on the concrete hard
  sources. The enlarged period is polynomial in their geometric dimensions;
  these dimensions are already polynomially bounded in the original source
  size. Primitive recursiveness and polynomial output size alone do not
  supply this runtime certificate. An arbitrary binary-encoded periodic
  strip can have exponentially large dimensions.
- Certify the variable-tile transition evaluator, connectivity check, and
  complete machine under the unary geometric encoding. The semantic
  decider, packed search, and polynomial DFS-stack bound are now proved
  below; these do not yet bound the transition evaluator's workspace.
- Compose the hardness reduction and upper bound to prove `stripStatement`.

## Variable-tile strip decider

`PolyominoStripWindow.tileable_iff_cycle` proves that any finite family of
bounded polyominoes tiles a full strip exactly when its finite window graph
has a cycle. The construction handles all eight square symmetries, empty
shapes, and arbitrary disconnected footprints. `LocalWindow.satisfiable_iff_cycle`
is the generic finite-alphabet overlap lemma used in the proof.

`Theorem55StripDecider.decideStrip_correct` proves a total Boolean decider
for the precise strip target, including positivity, nonemptiness, and the
finite disconnectedness test. A window has exactly `2^stateBits` states.
Under the unary input encoding, `stateBits` and the Savitch depth are bounded
by `16*(2*L+15)*(3*L+15)` and this polynomial plus one, respectively.

`PolyominoStripPacked` represents each window by a binary natural number
and proves exact decoding. `decideStripIndexed_correct` uses the existing
arithmetic DFS search, so it never constructs the list of all graph states.
`dfs_encoded_space_le` bounds every serialized DFS stack, at every search
step, by a quartic polynomial in input length. It treats transition evaluation
as a separate operation whose machine certificate remains to be supplied.
The indexed-search target builds successfully (1728 jobs).
`tmp/StripWindowAudit.lean` and `tmp/StripIndexedAudit.lean` check the new
semantic, encoding, and stack-bound results; all use only standard axioms.

## Shared Savitch evaluator certificate

`FiniteState.GenericSavitchStep.exactStep` now proves the evaluator-space
bound for an arbitrary transition leaf and retained input suffix, assuming
the leaf's own certificate. The old tromino step theorem is a direct
application, replacing its duplicated structural proof. Both targets build
(1620 jobs). The generic theorem introduces no native checks; its axiom audit
retains two native arithmetic dependencies from the existing
`scaledFieldSpace_le` helper. This supplies the reusable driver step, not
the missing variable-tile transition certificate.

## Uniform transition and connectivity checks

`PolyominoStripRawKeys` erases dependent finite indices to natural-number
records and proves that the exact binary bit order is unchanged.
`PolyominoStripWindow.Raw.check_correct` verifies a transition checker whose
quantifiers range over explicit lists of rows, placements, and input cells.
It checks containment, unique coverage, and overlap; repeated input cells
do not create extra placements. It never enumerates the window-state type.

`PolyominoConnectivitySearch.disconnectedPacked_correct` replaces the
powerset search with a countdown through binary masks. Each candidate
contains at most the input cell list, and each mask has at most one bit per
input cell. It does not allocate the list of all masks or subsets.

`Theorem55StripDecider.decideStripRaw_correct` combines these checks with
the indexed DFS driver to decide the exact strip predicate. The placement
record count is bounded by `statePolynomial` in the actual input length;
`cut_mask_bits_le` gives the corresponding linear cut-mask bound.
The target builds successfully (1732 jobs). `tmp/StripRawAudit.lean` checks
the equivalences and bounds; all use only the three standard axioms.

The remaining upper-bound obligation is to compile these uniform checks
and unary input handling into the machine model, with evaluator-space
certificates. The finite-loop definitions and data bounds do not by themselves
certify the machine's total workspace. Polynomial-time compilation of the
concrete hard sources also remains open.

## Bounded arithmetic machine compiler

`PartrecBoundedAll` compiles bounded universal quantification to a tail loop.
`boundedAll_uniform` bounds its evaluator workspace linearly in retained
fields, counter bits, and leaf workspace, independently of iteration count.
`BoundedArithmetic.Expr.code_eval` proves total evaluator compilation for
field lookup, arithmetic, conditionals, local bindings, and nested bounded
quantifiers. `Expr.code_fits` supplies a linear workspace allowance assuming
explicit bounds on intermediate binary lengths (`Expr.Safe`). These are
actual evaluator certificates, with a constant depending on the fixed formula.
The combined target builds (1483 jobs); `tmp/BoundedArithmeticAudit.lean`
confirms that the compiler and space results use only standard axioms.

`PolyominoStripWindow.Raw.idxOf_keys_eq_address` replaces placement-list
search by the exact mixed-radix arithmetic bit address. Instantiating the
formula compiler for the strip checks and assembling the complete unary-input
machine remain necessary before claiming PSPACE membership.

`PartrecBitTestSpace.bitTest` now supplies binary-space bit lookup by
repeated halving, without constructing `2^index`. The arithmetic language
includes this primitive. `Expr.code_fits_automatic` proves that every fixed
formula without the explicit power-of-two constructor uses linear evaluator
workspace in its flat input size, including nested bounded quantifiers.
`Expr.safe_automatic` derives all intermediate bounds from the formula.
The target builds (1486 jobs); `tmp/AutomaticArithmeticAudit.lean` reports
only standard axioms for bit lookup and automatic space certification.
The transition formula is the next instantiation.

## Compiled variable-tile transition

`PolyominoStripWindow.Formula.transition_truth` proves the complete bounded
arithmetic formula equivalent to `Raw.Transition`. Its field readers preserve
the signed coordinate encoding and placement-bit order. Containment and
coverage handle all eight orientations; candidate quantifiers enforce unique
coverage and matching overlap. Duplicate input cells remain harmless.

`transition_code_eval` proves the actual evaluator returns the transition
checker result. `transition_code_fits` certifies linear workspace in the binary
flat input fields, with a fixed constant independent of the tiles and strip.
The target builds (1517 jobs), and `tmp/StripFormulaAudit.lean` reports only
standard axioms for semantic correctness, evaluation, and space certification.
Disconnectedness compilation, the complete search/input machine, and the
polynomial-time hardness compiler remain necessary for PSPACE completeness.
