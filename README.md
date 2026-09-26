# lean-trominoes

Lean formalization of
[*Undecidability of Tiling with a Tromino*](https://arxiv.org/abs/2509.07906)
by the MIT--ULB CompGeom Group, Zachary Abel, Hugo Akitaya, Lily Chung,
Erik D. Demaine, Jenny Diomidova, Della Hendrickson, Stefan Langerman, and
Jayson Lynch. The working paper is included as
[PDF](trominoes.pdf) and [source](trominoes.texlish).

The eventual goal is every theorem and lemma in the paper. Theorem 5.2 is
proved: for either single tromino, periodic-subset tiling is co-r.e.-complete
in the plane and PSPACE-complete in a strip.

Theorem 5.5 is also proved: tiling by a fixed connected 15-omino and an
input disconnected polyomino is co-r.e.-complete in the plane and
PSPACE-complete in a strip, allowing arbitrary rotations and reflections.
The strip theorem uses the original unary encoding of the height and tile.
[The proof guide](docs/theorem-5.5.md) records the construction and validation.

Corollary 5.6 is proved too: with translations only, two fixed connected
15-ominoes and an input disconnected Q give co-r.e.-complete plane tiling
and PSPACE-complete strip tiling. See
[the Corollary 5.6 guide](docs/corollary-5.6.md).

Tiling full 3D space with a fixed connected 45-voxel polycube and an input
connected polycube is proved co-r.e.-complete, allowing all cube rotations
and reflections. The same completeness result is proved for every fixed
slab height greater than one, with a fixed connected tile of at most 45 voxels.
[The proof guide](docs/two-connected-polycubes.md) records the constructions and validation.

Corollary 5.9 is proved with translations only: three connected polycubes,
two fixed with at most 45 voxels each, give co-r.e.-complete tiling of full
3D space and every fixed slab height greater than one. See
[the Corollary 5.9 guide](docs/corollary-5.9.md).

Periodic L- and I-tromino completion are proved co-r.e.-complete in the plane.
Both reductions always produce valid, nonoverlapping periodic prefills.
Strip completion is PSPACE-complete under the explicit unary encoding.
For each tromino, there is also a completable periodic prefill whose every
completion is aperiodic: no nonzero translation preserves the completed tiling.

## Main statements and proofs

Start with [Theorem52.lean](LeanTrominoes/Theorem52.lean) to read the complete
target without importing its construction. In namespace
`LeanTrominoes.Theorem52`, the three propositions are:

| Declaration | Statement | Status |
| --- | --- | --- |
| `planeStatement` | For each tromino, periodic-subset tiling in 2D is co-r.e.-complete. | Proved |
| `stripStatement` | For each tromino, periodic-strip tiling under the flat encoding is PSPACE-complete. | Proved |
| `statement` | `planeStatement ∧ stripStatement`, the complete Theorem 5.2. | Proved |

These are **definitions of propositions**, not proofs. The main proof
declarations are below; names are relative to `LeanTrominoes` unless marked
otherwise.

| Result | Proof declaration | Module |
| --- | --- | --- |
| Theorem 5.2, complete result | `Theorem52.proved` | [Theorem52Proof](LeanTrominoes/Theorem52Proof.lean) |
| Theorem 5.2, strip PSPACE completeness | `Theorem52.stripProved` | [Theorem52Proof](LeanTrominoes/Theorem52Proof.lean) |
| Theorem 5.2, complete plane result | `PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement` | [PeriodicWangPlanarThreeDMReduction](LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean) |
| Corollary 5.3, two translation-only I trominoes, plane and strip | `TwoTranslationTrominoes.proved` | [TwoTranslationTrominoes](LeanTrominoes/TwoTranslationTrominoes.lean) |
| Theorem 5.5, plane co-r.e. completeness | `Theorem55.planeProved` | [Theorem55Proof](LeanTrominoes/Theorem55Proof.lean) |
| Theorem 5.5, strip PSPACE completeness | `Theorem55.stripProved` | [Theorem55StripProof](LeanTrominoes/Theorem55StripProof.lean) |
| Corollary 5.6, translations only, plane and strip | `ThreeTranslationPolyominoes.proved` | [ThreeTranslationProof](LeanTrominoes/ThreeTranslationProof.lean) |
| Corollary 5.9, translations only, full 3D and every fixed slab height > 1 | `ThreeTranslationPolycubes.proved` | [ThreeTranslationPolycubesProof](LeanTrominoes/ThreeTranslationPolycubesProof.lean) |
| Two connected polycubes, full-space co-r.e. completeness | `TwoConnectedPolycubes.spaceProved` | [TwoConnectedPolycubesSpaceProof](LeanTrominoes/TwoConnectedPolycubesSpaceProof.lean) |
| Two connected polycubes, every fixed slab height > 1 | `TwoConnectedPolycubes.slabsProved` | [TwoConnectedPolycubesSlabsProof](LeanTrominoes/TwoConnectedPolycubesSlabsProof.lean) |
| Periodic L-tromino completion, plane co-r.e. hardness | `CompletionPattern.LBricks.lCompletion_coREHard` | [CompletionLHardness](LeanTrominoes/CompletionLHardness.lean) |
| Periodic I-tromino completion, plane co-r.e. hardness | `CompletionPattern.IBricks.iCompletion_coREHard` | [CompletionIHardness](LeanTrominoes/CompletionIHardness.lean) |
| Periodic L- and I-tromino completion, plane co-r.e. completeness | `PeriodicTrominoPrefill.planeProblem_coREComplete` | [CompletionCompleteness](LeanTrominoes/CompletionCompleteness.lean) |
| Periodic L- and I-tromino completion, strip PSPACE completeness (unary encoding) | `PeriodicStripTrominoPrefill.problem_PSPACEComplete` | [CompletionStripHardness](LeanTrominoes/CompletionStripHardness.lean) |
| Periodic L- and I-tromino prefills admitting only aperiodic completions | `PeriodicTrominoPrefill.exists_aperiodic_completion` | [CompletionAperiodic](LeanTrominoes/CompletionAperiodic.lean) |
| Plane co-r.e. membership | `periodicTrominoTiling_coRE` | [ComputableSearch](LeanTrominoes/ComputableSearch.lean) |
| Theorem 5.2, strip PSPACE membership | `PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE` | [PartrecFlatStripDeciderSpace](LeanTrominoes/PartrecFlatStripDeciderSpace.lean) |
| Theorem 3.2, local 1D periodic CNF SAT PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEComplete` | [PeriodicCNFPolySpaceMembership](LeanTrominoes/PeriodicCNFPolySpaceMembership.lean) |
| Theorem 3.3, local 1D periodic 3SAT PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicThreeCNF1DSAT_PSPACEComplete` | [PeriodicCNFFieldWidth](LeanTrominoes/PeriodicCNFFieldWidth.lean) |
| Theorem 3.4, local 1D periodic 3SAT-3 PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicThreeSATThree1DSAT_PSPACEComplete` | [PeriodicThreeSATThreePolySpaceCompleteness](LeanTrominoes/PeriodicThreeSATThreePolySpaceCompleteness.lean) |
| Local 1D planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3, total semantic reductions with linear grid bounds (complexity bounds pending) | `PeriodicPlanarSAT.LineReduction.ordinary_correct`, `ordinaryThreeOccurrence_correct`, `exactOne_correct`, `exactOneThreeOccurrence_correct` | [PeriodicPlanarSATLineReduction](LeanTrominoes/PeriodicPlanarSATLineReduction.lean) |
| Supplied periodic drawing planarity, flat binary PSPACE membership | `PeriodicGridDrawing.Arithmetic.isContinuouslyPlanar_inPSPACE` | [PeriodicDrawingPolySpaceVerification](LeanTrominoes/PeriodicDrawingPolySpaceVerification.lean) |
| Local 1D planar SAT, all four variants, executable supplied-drawing decisions | `PeriodicPlanarSAT.LineDecision.ordinaryCheck_correct`, `ordinaryThreeCheck_correct`, `exactOneCheck_correct`, `exactOneThreeCheck_correct` | [PeriodicPlanarSATLineDecision](LeanTrominoes/PeriodicPlanarSATLineDecision.lean) |
| Local 1D 1-in-3SAT and 1-in-3SAT-3, native flat-encoded PSPACE completeness | `PeriodicExactOneCNF.localOneDimensionalThreeSAT_PSPACEComplete`, `localOneDimensionalThreeSATThree_PSPACEComplete` | [PeriodicExactOnePolySpaceCompleteness](LeanTrominoes/PeriodicExactOnePolySpaceCompleteness.lean) |
| Local 1D exact-one SAT, executable decisions for unrestricted, width-three, and occurrence-three variants; linear state and encoding-size bounds | `PeriodicExactOneCNF.check_correct`, `checkThree_correct`, `checkThreeThree_correct`, `state_bits_le_encoding`, `flatEncoding_length_le` | [PeriodicExactOneCNFLocality](LeanTrominoes/PeriodicExactOneCNFLocality.lean), [PeriodicExactOneCNFFlatSize](LeanTrominoes/PeriodicExactOneCNFFlatSize.lean) |
| Local 1D periodic CNF, executable decision procedure and linear state-bit bound | `PeriodicCNF.LineWindow.check_localPeriodicCNF1DSAT`, `state_bits_le_encoding` | [PeriodicCNFLineSearch](LeanTrominoes/PeriodicCNFLineSearch.lean) |
| Theorem 3.2, 2D periodic CNF SAT co-r.e. completeness | `WangPeriodicCNF.coREComplete`, `WangPeriodicCNF.localCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.3, local 2D periodic 3SAT co-r.e. completeness | `PeriodicThreeCNF.localThreeCNFCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.4, local 2D periodic 3SAT-3 co-r.e. completeness | `PeriodicThreeSATThree.localThreeSATThreeCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Local 2D periodic 1-in-3SAT-3 co-r.e. completeness (without a planarity restriction) | `PeriodicOneInThree.localOneInThreeSATThreeCoREComplete` | [PeriodicOneInThreeCompleteness](LeanTrominoes/PeriodicOneInThreeCompleteness.lean) |
| Plane periodic 3SAT with checked continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.WangReduction.coREComplete` | [PeriodicPlanarSATCompleteness](LeanTrominoes/PeriodicPlanarSATCompleteness.lean) |
| Plane periodic 3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction.coREComplete` | [PeriodicPlanarThreeOccurrenceCompleteness](LeanTrominoes/PeriodicPlanarThreeOccurrenceCompleteness.lean) |
| Plane periodic 1-in-3SAT and 1-in-3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ExactOneEndpoint.WangReduction.coREComplete`, `threeOccurrenceCoREComplete` | [PeriodicPlanarExactOneCompleteness](LeanTrominoes/PeriodicPlanarExactOneCompleteness.lean) |
| Plane periodic 3DM with checked drawings and degree 2 or 3, co-r.e. completeness | `PeriodicThreeDM.planeProblem_coREComplete` | [PeriodicThreeDMPlaneCompleteness](LeanTrominoes/PeriodicThreeDMPlaneCompleteness.lean) |
| Normalized plane trichromatic orientation, co-r.e. completeness | `Gadget.NormalizedOrientation.coREComplete` | [NormalizedOrientationCompleteness](LeanTrominoes/NormalizedOrientationCompleteness.lean) |
| Theorem 3.1, Wang tiling co-r.e.-completeness | `LeanWang.domino_problem_coRE_complete` | Dependency module `LeanWang.Final` |

`import LeanTrominoes` exposes these main results. Import
`LeanTrominoes.Theorem52` when only the target statements are needed, or an
individual construction module for its implementation API.

The full proof instantiates the [appender closure](LeanTrominoes/Theorem52DirectSparseClosure.lean)
with the concrete [vertex](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean)
and [route](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean)
compilers. No compiler witness remains assumed.

## Definitions

| Objects | Module |
| --- | --- |
| Integer-grid cells, polyominoes, square-grid symmetries, I and L trominoes | [Basic](LeanTrominoes/Basic.lean) |
| Placements and exact tilings | [Tiling](LeanTrominoes/Tiling.lean) |
| Partial tromino tilings and completion | [TrominoCompletion](LeanTrominoes/TrominoCompletion.lean) |
| Periodic plane and strip prefills | [PeriodicTrominoCompletion](LeanTrominoes/PeriodicTrominoCompletion.lean) |
| Equivalent tilings by geometric three-cell footprints | [FootprintTiling](LeanTrominoes/FootprintTiling.lean) |
| `PeriodicRegion`, `PeriodicStrip`, and their tilability predicates | [Periodic](LeanTrominoes/Periodic.lean) |
| Target strip encoding and decoder | [PeriodicStripFlatEncoding](LeanTrominoes/PeriodicStripFlatEncoding.lean) |
| Finite-alphabet polynomial-space deciders, polynomial-time reductions, PSPACE completeness | [Complexity](LeanTrominoes/Complexity.lean) |
| Periodic CNF formulas and satisfiability | [PeriodicCNF](LeanTrominoes/PeriodicCNF.lean) |
| Finite presentations of periodic graphs | [PeriodicGraph](LeanTrominoes/PeriodicGraph.lean) |
| Scaled integer-grid periodic drawings | [PeriodicGridDrawing](LeanTrominoes/PeriodicGridDrawing.lean) |

A plane input has a finite motif and two full-rank period vectors. A strip
input has a finite motif in a bounded-height strip and one positive
horizontal period. Malformed presentations are no-instances. Complexity
claims use the explicit encodings named in their statements.

PSPACE hardness uses polynomial-time many-one reductions from every encoded
polynomial-space language. Both deciders and reduction machines require finite
alphabets on every stack. The [finite-alphabet certificate](LeanTrominoes/FiniteAlphabetPolyTime.lean)
strengthens Mathlib’s machine interface; a [verified alphabet restriction](LeanTrominoes/TM2FiniteAlphabetRestriction.lean)
converts existing certificates without changing their encodings or running time.
Finite control ensures that each program can write only finitely many symbols.

## Paper coverage

This table is the authoritative summary of completed and open paper results.
A result can have proved hardness reductions without all clauses of its numbered
paper theorem being complete; the entries below distinguish these cases.

| Paper results | Current coverage |
| --- | --- |
| Theorem 3.1 | Imported Wang tiling theorem |
| Theorem 3.2 | 2D CNF SAT co-r.e. completeness, including the local restriction, proved; local 1D PSPACE completeness proved; remaining dimensional clauses open |
| Theorems 3.3–3.4 | Local 1D 3SAT and 3SAT-3 PSPACE-completeness proved; local 2D 3SAT and 3SAT-3 co-r.e. completeness proved |
| Theorem 5.2 | Fully proved |
| Corollary 5.3 | Translation-only plane co-r.e. completeness and strip PSPACE completeness proved |
| Theorem 5.5 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Corollary 5.6 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Two connected polycubes | Full 3D and every fixed slab height > 1 proved |
| Corollary 5.9 | Translation-only co-r.e. completeness in full 3D and every fixed slab height > 1 proved |
| Tromino completion | L- and I-tromino plane co-r.e. completeness, strip PSPACE completeness (unary encoding), and the aperiodic-completion corollary proved |
| Theorems 2.1–2.2, Lemma 2.3 | Concrete drawing constructions used by the hardness proofs exist; full general drawing statements and bounds remain open |
| Theorems 3.5–3.8 | Plane planar 3SAT and 3SAT-3, planar 1-in-3SAT and 1-in-3SAT-3 with supplied drawings, normalized orientation, and checked-drawing 3DM with degree 2 or 3 have completeness endpoints. Local 1-in-3SAT-3 completeness without planarity is also proved. Local plane planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3 are co-r.e. complete even with a linear grid-size restriction in the output formula size; remaining dimensional clauses still need packaging/proofs |
| Section 4, Lemma 5.1 in its full generality, and other results 5.4–5.15 except those listed above | Open |

The local 1D CNF endpoint is now **PSPACE-complete** under the native flat
encoding. The [machine certificate](LeanTrominoes/PeriodicCNFPolySpaceMembership.lean)
combines the [linear-space preprocessor](LeanTrominoes/PeriodicCNFFlatFieldCountSpace.lean),
[compiled transition predicate](LeanTrominoes/PeriodicCNFFieldTransition.lean), and
[polynomial-space cycle search](LeanTrominoes/PeriodicCNFFieldEvaluator.lean).
The [field-indexed window model](LeanTrominoes/PeriodicCNFFieldWindow.lean)
uses three bits per flat field and supports arbitrarily large atom names and
common clause offsets. [Local 1D 3SAT is also PSPACE-complete](LeanTrominoes/PeriodicCNFFieldWidth.lean):
the hardness compiler already emits width-three clauses.
[Local 1D 3SAT-3 is PSPACE-complete](LeanTrominoes/PeriodicThreeSATThreePolySpaceCompleteness.lean).

The [four planar 1D SAT reductions](LeanTrominoes/PeriodicPlanarSATLineReduction.lean)
now preserve one-dimensionality, locality, occurrence bounds, and the intrinsic
linear drawing-grid bounds, including on malformed source inputs.
[Forgetting the drawings](LeanTrominoes/PeriodicExactOneLineReduction.lean) also
gives total reductions to nonplanar exact-one SAT and its occurrence-three variant.
The planar reductions are proved primitive recursive; their native encoded
polynomial-time certificates remain open.

[All four planar 1D SAT variants are in PSPACE](LeanTrominoes/PeriodicPlanarSATLinePolySpaceMembership.lean)
under the [lossless formula-and-drawing encoding](LeanTrominoes/PeriodicPlanarSATFlatEncoding.lean).
The [complete verifier](LeanTrominoes/PeriodicPlanarSATFullVerification.lean)
checks satisfiability, locality, clause width, the applicable occurrence bound,
the grid bound, planarity, incidence counts, vertex compatibility, and route endpoints.
The [finite planarity check](LeanTrominoes/PeriodicDrawingFiniteCheck.lean)
supports arbitrary stored coordinates, without a bounding-box promise.
The [route query's correctness proof](LeanTrominoes/PeriodicPlanarSATRouteSemantics.lean)
connects its [linear-space machine](LeanTrominoes/PeriodicPlanarSATRouteMachine.lean)
to the actual incidence graph, including repeated literals and empty or singleton routes.
Distinct-variable indices follow `List.dedup`'s last-occurrence order.
The remaining completeness work is connecting native encoded reductions to
the four target languages, including their fixed grid and locality promises. The routed exact-one
intermediate has [compiled numeric atom names](LeanTrominoes/PeriodicCNFStripNativeAtomRenaming.lean)
with a proved injective renaming that
[preserves the planar languages and drawings](LeanTrominoes/PeriodicPlanarSATInjectiveRenaming.lean), and
[compiled signed variable-position fields](LeanTrominoes/PeriodicCNFStripNativeVariableFields.lean)
in incidence order. Its [complete route-word compiler](LeanTrominoes/PeriodicCNFStripNativeRouteWords.lean)
outputs the actual clause-to-variable direction words with incidence boundaries
and compiles their signed horizontal and vertical displacements. The [binary input assembler](LeanTrominoes/PeriodicPlanarSATEncodingCompiler.lean)
is also proved. [Canonical clause-origin fields](LeanTrominoes/PeriodicCNFStripNativeIncidenceClauseFields.lean)
are compiled in incidence order. The [offset recovery compiler](LeanTrominoes/CanonicalLiteralOffsetCompiler.lean)
turns signed incidence-coordinate columns and a positive drawing period into
native anchored literal-offset fields. The [concrete literal-offset compiler](LeanTrominoes/PeriodicCNFStripNativeLiteralOffsets.lean)
now discharges those geometric premises for the routed source. Its
[drawing period](LeanTrominoes/PeriodicCNFStripNativePeriodCompiler.lean),
[clause lengths](LeanTrominoes/PeriodicCNFStripNativeClauseArities.lean), and
[literal signs](LeanTrominoes/PeriodicCNFStripNativeLiteralValues.lean) also have
native polynomial-time compilers. The [complete native formula compiler](LeanTrominoes/PeriodicCNFStripNativeFormulaCompiler.lean)
now assembles every field and its binary encoding for the anchor-normalized,
numerically renamed routed formula, preserving exact-one satisfiability.
The [complete ordered vertex table](LeanTrominoes/PeriodicCNFStripNativeDrawingVertices.lean)
and [complete route table](LeanTrominoes/PeriodicCNFStripNativeDrawingRoutes.lean)
also have polynomial-time field compilers, including route counts, point counts,
and every stored route coordinate. [Unit-route reconstruction](LeanTrominoes/DelimitedDirectionVertexGeometry.lean)
proves exact agreement with the stored point lists. The
[indexed segment table](LeanTrominoes/PeriodicCNFStripNativeDrawingSegments.lean)
and [drawing-header fields](LeanTrominoes/PeriodicDrawingHeaderCompiler.lean)
are also compiled, including the exact finite-check radius. The
[complete native binary encoder](LeanTrominoes/PeriodicCNFStripNativePlanarEncoding.lean)
now emits the entire routed exact-one candidate and its supplied drawing.
The four planar hardness endpoints remain unfinished; this routed candidate
is distinct from the earlier primitive-recursive endpoints.

[Local 1D 1-in-3SAT and 1-in-3SAT-3 are PSPACE-complete](LeanTrominoes/PeriodicExactOnePolySpaceCompleteness.lean)
under the native flat encoding. The upper bounds use a direct exact-one window
predicate and compiled Savitch search. The
[polynomial-time reduction](LeanTrominoes/PeriodicOneInThreePolyTimeCompiler.lean)
compiles both literal metadata and compact numeric atom names, including padding
for short clauses. Its correctness preserves locality and the three-occurrence
bound. The [executable decisions](LeanTrominoes/PeriodicExactOneCNFLocality.lean)
and [linear encoding-size bound](LeanTrominoes/PeriodicExactOneCNFFlatSize.lean)
are also proved.

The 3SAT-3 [polynomial-time compiler](LeanTrominoes/PeriodicThreeSATThreePolyTimeCompiler.lean)
combines occurrence-split atom numbers with literal profiles and emits the native flat formula encoding.
[Local planar 3SAT and 3SAT-3 are co-r.e. complete](LeanTrominoes/PeriodicPlanarLocalThreeOccurrenceCompleteness.lean)
with supplied drawings. The construction has
[a linear fundamental-grid side bound](LeanTrominoes/PeriodicPlanarThreeOccurrenceGridSize.lean)
in the source clause-plus-literal count.
[Local planar 1-in-3SAT and 1-in-3SAT-3 are also co-r.e. complete](LeanTrominoes/PeriodicPlanarLocalExactOneCompleteness.lean),
with [the corresponding linear grid bound](LeanTrominoes/PeriodicPlanarExactOneGridSize.lean).
[All four remain co-r.e. complete with an intrinsic linear grid-size restriction](LeanTrominoes/PeriodicPlanarBoundedLocalCompleteness.lean):
the supplied fundamental-square side length is bounded by a fixed constant
times (the output formula’s clause-plus-literal count + 1).
The ordinary endpoint uses a
[finite certificate for vertex orbits](LeanTrominoes/PeriodicGraphOrbitCertificate.lean):
canonical representatives may lie outside the fundamental square, but distinct
vertices cannot coincide under any whole-period translation.

For the plane parts of Theorems 3.2–3.4, the existing Wang reductions already
proved hardness. The shared [finite-obstruction proof](LeanTrominoes/PeriodicCNFFiniteSearch.lean)
and [effective finite search](LeanTrominoes/PeriodicCNFCoRE.lean) now supply
co-r.e. membership for arbitrary periodic CNF presentations.
[Locality, width, and occurrence checks](LeanTrominoes/PeriodicCNFSyntaxComputability.lean)
allow invalid restricted presentations to be rejected. These upper bounds
use only Lean's standard axioms; completeness retains the assumptions of the
existing Wang hardness theorem.

For tromino completion, extending a valid prefill is proved
equivalent to tiling the uncovered region, with a
[finite-obstruction characterization](LeanTrominoes/TrominoCompletionFiniteSearch.lean)
for plane and strip inputs. The paper's ASCII layouts in
[data/completion](data/completion) now have kernel-checked
[major gadget relations](LeanTrominoes/CompletionMajorRelations.lean) and
[complete minor boundary profiles](LeanTrominoes/CompletionMinorBoundaryRelations.lean).
The [L-brick palette](LeanTrominoes/CompletionLBricks.lean) has a verified common
[region](LeanTrominoes/CompletionLBrickRegions.lean),
[Boolean network](LeanTrominoes/CompletionLBrickLogic.lean), and
[local barrier checks](LeanTrominoes/CompletionLAtomBarriers.lean). These yield
a [global assembly criterion](LeanTrominoes/CompletionLAssembly.lean): a plane
completion exists exactly when realizable local gadget states partition the
plane. Canonical states from a completion satisfy
[connector consistency](LeanTrominoes/CompletionLConnectorConsistency.lean).
The [minor-state lemmas](LeanTrominoes/CompletionLMinorStates.lean) force and
propagate Boolean connectors. The full [brick-network equivalence](LeanTrominoes/CompletionLBrickEquivalence.lean)
and [finite periodic prefill compiler](LeanTrominoes/CompletionLPeriodicCompiler.lean)
are proved. Nine [orientation-cell circuits](LeanTrominoes/CompletionCircuitTruthTables.lean)
have checked truth tables and wiring; their [infinite-grid composition](LeanTrominoes/CompletionCircuitReduction.lean)
is proved. The [source interface and finite compiler](LeanTrominoes/CompletionOrientationCompiler.lean)
and its [primitive-recursion proof](LeanTrominoes/CompletionOrientationComputability.lean)
now give unconditional [plane co-r.e. hardness for L-tromino completion](LeanTrominoes/CompletionLHardness.lean).
Every output is a [valid periodic partial tiling](LeanTrominoes/CompletionLCompilerValidity.lean),
including outputs for unsatisfiable inputs. Completing tilings need not be periodic.

For I-trominoes, [guarded gadgets](LeanTrominoes/CompletionIGuardedRelations.lean)
and [no-crossing lemmas](LeanTrominoes/CompletionINoCrossing.lean) give an exact
[brick-network equivalence](LeanTrominoes/CompletionIBrickEquivalence.lean).
Reusing the orientation circuits yields
[plane co-r.e. hardness](LeanTrominoes/CompletionIHardness.lean), with
[valid prefills and independent periods](LeanTrominoes/CompletionICompilerValidity.lean).
[Co-r.e. membership](LeanTrominoes/CompletionCoRE.lean) is proved for both
trominoes by searching for dependent periods, overlapping prescribed tiles,
or an unsatisfiable finite box of uncovered cells. This gives
[plane co-r.e. completeness](LeanTrominoes/CompletionCompleteness.lean).
[Strip PSPACE completeness](LeanTrominoes/CompletionStripHardness.lean) is proved
for both trominoes under an explicit unary encoding of height, period, and motif.
[Membership](LeanTrominoes/CompletionStripMembership.lean) compiles valid prefills
to uncovered strips in polynomial space. Hardness uses
[diagonal routing](LeanTrominoes/CompletionDiagonalPeriod.lean) to preserve
satisfiability, horizontal periods, and bounded height, followed by
[kernel-checked cap bands](LeanTrominoes/CompletionStripCapBands.lean).
The finite compilers for [L](LeanTrominoes/CompletionLStripCompiler.lean) and
[I](LeanTrominoes/CompletionIStripCompiler.lean) produce explicit motifs,
periods, and heights. The [source reduction](LeanTrominoes/CompletionStripSourceReduction.lean)
preserves satisfiability, and its
[polynomial-time machine](LeanTrominoes/CompletionStripHardnessCompiler.lean)
queries the actual source records, evaluates the brick palette, and serializes
the entire prefill in unary. Every output is a
[valid partial tiling](LeanTrominoes/CompletionStripPrefillValidity.lean),
including outputs for unsatisfiable inputs. Completing tilings need not be periodic.

The completion geometry and generic serialization proofs use only standard
Lean axioms. The final completeness theorems inherit existing native-evaluation
certificates from the source reductions and strip decider. Their audits contain
no `sorryAx`; the strip theorem adds no axioms beyond its verified source
semantics, source runtime, and membership proofs.

[Periodic prefills admitting only aperiodic completions](LeanTrominoes/CompletionAperiodic.lean)
are proved to exist for both trominoes. A
[finite tile table](LeanTrominoes/CompletionPeriodicCertificate.lean) certifies a
doubly periodic completion, and the [checks are primitive recursive](LeanTrominoes/CompletionPeriodicComputability.lean).
Every completion with two independent integer translation periods
[yields such a certificate](LeanTrominoes/CompletionPeriodicExtraction.lean).
If every completable prefill had one, plane completion would be r.e.,
contradicting its co-r.e. hardness.
[Cylinder pumping](LeanTrominoes/CompletionCylinderPumping.lean) strengthens this:
a completion with any nonzero translation period would yield a doubly periodic
completion of the same prefill. The proof handles arbitrary period directions
and preserves the prefill's phase. Hence every completion of these examples
has no nonzero translation period. The certificate and pumping proofs use only
standard Lean axioms; the existence theorem adds no axioms beyond plane hardness.

## Proof guides

These guides explain the final constructions and point to their main modules.
Development history is preserved in Git.

| Result | Guide |
| --- | --- |
| Theorem 5.2 | [Periodic-subset tiling with one tromino](docs/theorem-5.2.md) |
| Theorem 5.5 | [Tiling by two polyominoes](docs/theorem-5.5.md) |
| Two connected polycubes | [Full space and fixed-height slabs](docs/two-connected-polycubes.md) |
| Corollary 5.6 | [Three polyominoes by translation](docs/corollary-5.6.md) |
| Corollary 5.9 | [Three connected polycubes by translation](docs/corollary-5.9.md) |

## Build

```sh
lake build
```

The library's `LeanTrominoes.*` glob includes every Lean source module, even
when it is not imported by the small public root. New files therefore enter
the default build automatically. To build one module and its dependencies:

```sh
lake build +LeanTrominoes.Theorem52:olean
```

The project uses Lean 4.31.0 and depends on
[`lean-wang`](https://github.com/edemaine/lean-wang).
[lean-toolchain](lean-toolchain) pins Lean;
[lake-manifest.json](lake-manifest.json) pins the fetched dependencies.
