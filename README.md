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
| Local 1D planar SAT, all four variants, total semantic reductions with linear grid bounds | `PeriodicPlanarSAT.LineReduction.ordinary_correct`, `ordinaryThreeOccurrence_correct`, `exactOne_correct`, `exactOneThreeOccurrence_correct` | [PeriodicPlanarSATLineReduction](LeanTrominoes/PeriodicPlanarSATLineReduction.lean) |
| Local 1D planar 3SAT and 3SAT-3, native flat-encoded PSPACE completeness | `PeriodicPlanarSAT.ordinary_PSPACEComplete`, `ordinaryThree_PSPACEComplete` | [PeriodicPlanarOrdinaryLinePolySpaceCompleteness](LeanTrominoes/PeriodicPlanarOrdinaryLinePolySpaceCompleteness.lean) |
| Local 1D planar 1-in-3SAT and 1-in-3SAT-3, native flat-encoded PSPACE completeness | `PeriodicPlanarSAT.exactOne_PSPACEComplete`, `exactOneThree_PSPACEComplete` | [PeriodicPlanarExactOneLinePolySpaceCompleteness](LeanTrominoes/PeriodicPlanarExactOneLinePolySpaceCompleteness.lean) |
| Supplied periodic drawing planarity, flat binary PSPACE membership | `PeriodicGridDrawing.Arithmetic.isContinuouslyPlanar_inPSPACE` | [PeriodicDrawingPolySpaceVerification](LeanTrominoes/PeriodicDrawingPolySpaceVerification.lean) |
| Local 1D planar SAT, all four variants, executable supplied-drawing decisions | `PeriodicPlanarSAT.LineDecision.ordinaryCheck_correct`, `ordinaryThreeCheck_correct`, `exactOneCheck_correct`, `exactOneThreeCheck_correct` | [PeriodicPlanarSATLineDecision](LeanTrominoes/PeriodicPlanarSATLineDecision.lean) |
| Local 1D 1-in-3SAT and 1-in-3SAT-3, native flat-encoded PSPACE completeness | `PeriodicExactOneCNF.localOneDimensionalThreeSAT_PSPACEComplete`, `localOneDimensionalThreeSATThree_PSPACEComplete` | [PeriodicExactOnePolySpaceCompleteness](LeanTrominoes/PeriodicExactOnePolySpaceCompleteness.lean) |
| Local 1D exact-one SAT, executable decisions for unrestricted, width-three, and occurrence-three variants; linear state and encoding-size bounds | `PeriodicExactOneCNF.check_correct`, `checkThree_correct`, `checkThreeThree_correct`, `state_bits_le_encoding`, `flatEncoding_length_le` | [PeriodicExactOneCNFLocality](LeanTrominoes/PeriodicExactOneCNFLocality.lean), [PeriodicExactOneCNFFlatSize](LeanTrominoes/PeriodicExactOneCNFFlatSize.lean) |
| Local 1D periodic CNF, executable decision procedure and linear state-bit bound | `PeriodicCNF.LineWindow.check_localPeriodicCNF1DSAT`, `state_bits_le_encoding` | [PeriodicCNFLineSearch](LeanTrominoes/PeriodicCNFLineSearch.lean) |
| Theorem 3.2, 2D periodic CNF SAT co-r.e. completeness | `WangPeriodicCNF.coREComplete`, `WangPeriodicCNF.localCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.2, periodic CNF SAT in every dimension ≥ 2 | `PeriodicCNFDimensions.satisfiable_coREComplete`, `PeriodicCNFDimensions.localProblem_coREComplete` | [PeriodicCNFDimensions](LeanTrominoes/PeriodicCNFDimensions.lean) |
| Theorem 3.7, local planar 2D 3DM with colored degree 2 or 3 | `PeriodicThreeDM.localPlaneProblem_coREComplete` | [PeriodicThreeDMLocalPlaneCompleteness](LeanTrominoes/PeriodicThreeDMLocalPlaneCompleteness.lean) |
| Theorem 3.3, local 2D periodic 3SAT co-r.e. completeness | `PeriodicThreeCNF.localThreeCNFCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.4, local 2D periodic 3SAT-3 co-r.e. completeness | `PeriodicThreeSATThree.localThreeSATThreeCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/PeriodicSATPlaneCompleteness.lean) |
| Local 2D periodic 1-in-3SAT-3 co-r.e. completeness (without a planarity restriction) | `PeriodicOneInThree.localOneInThreeSATThreeCoREComplete` | [PeriodicOneInThreeCompleteness](LeanTrominoes/PeriodicOneInThreeCompleteness.lean) |
| Plane periodic 3SAT with checked continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.WangReduction.coREComplete` | [PeriodicPlanarSATCompleteness](LeanTrominoes/PeriodicPlanarSATCompleteness.lean) |
| Plane periodic 3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction.coREComplete` | [PeriodicPlanarThreeOccurrenceCompleteness](LeanTrominoes/PeriodicPlanarThreeOccurrenceCompleteness.lean) |
| Plane periodic 1-in-3SAT and 1-in-3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ExactOneEndpoint.WangReduction.coREComplete`, `threeOccurrenceCoREComplete` | [PeriodicPlanarExactOneCompleteness](LeanTrominoes/PeriodicPlanarExactOneCompleteness.lean) |
| Plane periodic 3DM with checked drawings and degree 2 or 3, co-r.e. completeness | `PeriodicThreeDM.planeProblem_coREComplete` | [PeriodicThreeDMPlaneCompleteness](LeanTrominoes/PeriodicThreeDMPlaneCompleteness.lean) |
| Local 1D periodic 3DM with colored degree 2 or 3, native PSPACE completeness | `PeriodicThreeDM.localLineProblem_PSPACEComplete` | [PeriodicThreeDMLineCompleteness](LeanTrominoes/PeriodicThreeDMLineCompleteness.lean) |
| Local planar 1D periodic 3DM with colored degree 2 or 3 and supplied drawing, native PSPACE completeness | `PeriodicThreeDM.localPlanarLineProblem_PSPACEComplete` | [PeriodicThreeDMPlanarLineCompleteness](LeanTrominoes/PeriodicThreeDMPlanarLineCompleteness.lean) |
| Normalized plane trichromatic orientation, co-r.e. completeness | `Gadget.NormalizedOrientation.coREComplete` | [NormalizedOrientationCompleteness](LeanTrominoes/NormalizedOrientationCompleteness.lean) |
| Normalized 1D trichromatic orientation, native binary PSPACE completeness | `Gadget.NormalizedOrientation.lineProblem_PSPACEComplete` | [NormalizedOrientationLineMembership](LeanTrominoes/NormalizedOrientationLineMembership.lean) |
| Periodic Horn and dual Horn SAT, period-one models in every dimension | `Horn.exists_period_one`, `Horn.dual_exists_period_one` | [PeriodicHornCore](LeanTrominoes/PeriodicHornCore.lean), [PeriodicHornSolver](LeanTrominoes/PeriodicHornSolver.lean) |
| Periodic Horn and dual Horn SAT, executable solvers and period-one model construction | `Horn.periodicCheck_correct`, `periodicDualCheck_correct`; `PeriodicCNF.hornCheck_correct`, `dualHornCheck_correct`, `hornModel_correct`, `dualHornModel_correct` | [PeriodicHornSolver](LeanTrominoes/PeriodicHornSolver.lean), [PeriodicHornDecision](LeanTrominoes/PeriodicHornDecision.lean) |
| Periodic Horn and dual Horn SAT, linear indexed-RAM bound | `Horn.Indexed.certified`, `Horn.PeriodicIndexed.certified` | [HornIndexedTime](LeanTrominoes/HornIndexedTime.lean), [PeriodicHornLinearTime](LeanTrominoes/PeriodicHornLinearTime.lean) |
| Theorem 4.1, local periodic 2SAT in every fixed dimension | `PeriodicTwoSAT.local_certified`, `solveLocal_correct`, `solveLocal_polynomial` | [PeriodicTwoSATLocalTime](LeanTrominoes/PeriodicTwoSATLocalTime.lean), [PeriodicTwoSATPolynomialTime](LeanTrominoes/PeriodicTwoSATPolynomialTime.lean) |
| Lemma 5.1, arbitrary periodic subspace tiling and completion membership | `PeriodicSubspaceTiling.lemma51`, `lattice_tileable_coRE`, `lattice_completable_coRE`, `Strip.tiling_inPSPACE`, `Strip.completion_inPSPACE` | [Lemma51](LeanTrominoes/Lemma51.lean) |
| Lemma 4.3, bounded-diameter augmenting paths in general periodic graphs | `PeriodicLatticeGraph.bounded_augmenting_path`, `perfect_or_bounded_augmenting` | [PeriodicGeneralAugmentingPath](LeanTrominoes/PeriodicGeneralAugmentingPath.lean) |
| Lemma 4.4, 2-periodic bipartition of a connected bipartite periodic graph | `PeriodicLatticeGraph.bipartition_two_periodic` | [PeriodicBipartitionDoubling](LeanTrominoes/PeriodicBipartitionDoubling.lean) |
| Lemma 4.5, a protovertex-simple augmenting path shorter than the quotient vertex count | `PeriodicBipartite.perfect_or_short_augmenting` | [PeriodicShortAugmentingProperties](LeanTrominoes/PeriodicShortAugmentingProperties.lean) |
| Theorem 4.6, period-one bipartite perfect matching in every dimension | `PeriodicBipartite.exists_period_one`, `perfect_iff_quotient` | [PeriodicMatchingPeriodOne](LeanTrominoes/PeriodicMatchingPeriodOne.lean) |
| Theorem 4.7, bipartite perfect matching decision and construction in `O(E√V)` indexed-RAM operations | `PeriodicBipartite.matchingSolver_certified`, `matchingSolver_edge_sqrt_bound` | [PeriodicMatchingSolver](LeanTrominoes/PeriodicMatchingSolver.lean) |
| Finite 3CNF tableaux for bounded-time TM2 acceptance, with symbolic initial configurations and polynomial formula-size bounds | `FiniteMachineTrace.paddedFormula_iff_evals`, `symbolicFormula_iff_evals`, `symbolicFormula_length_le`, `symbolicFormula_width` | [FiniteMachineAcceptanceCNF](LeanTrominoes/FiniteMachineAcceptanceCNF.lean), [FiniteSymbolicMachineCNF](LeanTrominoes/FiniteSymbolicMachineCNF.lean) |
| Cook–Levin: every verifier-defined NP language reduces by an actual polynomial-time machine to ordinary finite 3CNF SAT | `FiniteCNF.threeSatisfiable_npHard`, `satisfiable_npHard`; `Complexity.VerifierInPolyTime.finiteCNFReduction`; `FiniteNPRequestEmitter.computableInPolyTime` | [FiniteSATNPHard](LeanTrominoes/FiniteSATNPHard.lean), [FiniteNPRequestEmitter](LeanTrominoes/FiniteNPRequestEmitter.lean), [FiniteNPSeparatedRequest](LeanTrominoes/FiniteNPSeparatedRequest.lean) |
| Complete polynomial-time verifier initialization and accepting self-loop emission, matching the existing finite tableau programs | `FiniteNPInitializationEmitter.computableInPolyTime`, `initialProgram_encode`; `FiniteNPCertificateStackEmitter.stackProgram_eq`; `FiniteNPPaddedProgramEmitter.computableInPolyTime`, `program_eq` | [FiniteNPInitializationEmitter](LeanTrominoes/FiniteNPInitializationEmitter.lean), [FiniteNPCertificateStackEmitterCorrectness](LeanTrominoes/FiniteNPCertificateStackEmitterCorrectness.lean), [FiniteNPPaddedProgramEmitter](LeanTrominoes/FiniteNPPaddedProgramEmitter.lean) |
| Native finite-verifier machine programs and absolute-time serialization, with polynomial-time squares, products, pairing, and request-header generation | `FiniteNPMachineProgramEmitter.wellFormedComputableInPolyTime`, `stepComputableInPolyTime`, `acceptingComputableInPolyTime`; `FiniteCNF.ProgramColumns.repeated`; `FiniteNPVariableNameCompiler.sourceComputableInPolyTime`, `freshComputableInPolyTime` | [FiniteNPMachineProgramEmitter](LeanTrominoes/FiniteNPMachineProgramEmitter.lean), [FiniteProgramColumns](LeanTrominoes/FiniteProgramColumns.lean), [FiniteNPVariableNameCompiler](LeanTrominoes/FiniteNPVariableNameCompiler.lean) |
| Native finite-CNF compiler backend, with quadratic machine time and correct bounded requests for every NP verifier | `FiniteCNFCompiler.finiteAlphabetComputableInPolyTime`, `Request.correct`, `compiler_time`; `Complexity.VerifierInPolyTime.nativeRequest_correct`, `nativeRequest_encode_length_le`, `nativeRequest_backend_time_le` | [FiniteCNFCompiler](LeanTrominoes/FiniteCNFCompiler.lean), [FiniteNPCompilerRequest](LeanTrominoes/FiniteNPCompilerRequest.lean) |
| Polynomial-time preparation of finite-compiler source words, with exact certificate, time, space, and variable counters | `FiniteNPCompilerPreparation.computableInPolyTime`, `prepared_eq`, `counterCount_prepared`, `sourceSymbols_prepared` | [FiniteNPCompilerPreparation](LeanTrominoes/FiniteNPCompilerPreparation.lean) |
| Flat finite-tableau encoding, with source and auxiliary variable ranges and a polynomial binary-output bound | `Complexity.VerifierInPolyTime.tableau_variable_bounds`, `tableau_encode_length_le` | [FiniteNPTableauEncoding](LeanTrominoes/FiniteNPTableauEncoding.lean), [FiniteCNFFlatEncoding](LeanTrominoes/FiniteCNFFlatEncoding.lean) |
| Every verifier-defined NP language has an equivalent finite width-three tableau with a polynomial clause bound | `Complexity.VerifierInPolyTime.tableau_correct`, `tableau_width`, `tableau_length_le` | [FiniteNPTableau](LeanTrominoes/FiniteNPTableau.lean) |
| Finite 3CNF for existence of an accepted bounded binary certificate, with polynomial formula-size bounds | `FiniteCertificate.formula_correct`, `formula_length_le`, `formula_width` | [FiniteCertificateCNF](LeanTrominoes/FiniteCertificateCNF.lean) |
| Explicit binary certificates for both finite-region tiling and finite-preplacement completion: 24 bits per listed region cell or bounding-box cell | `Tromino.FiniteRegion.tileable_iff_bounded_certificate`; `Tromino.FiniteWitness.completion_iff_box_certificate`, `completion_iff_bounded_certificate` | [FiniteTrominoRegionCertificate](LeanTrominoes/FiniteTrominoRegionCertificate.lean), [FiniteTrominoCompletionCertificate](LeanTrominoes/FiniteTrominoCompletionCertificate.lean) |
| Polynomial-time exact-cover verifier backend for both trominoes, with geometric certificate correctness and serialized candidate-table bounds | `FiniteExactCoverVerifier.finiteAlphabetComputableInPolyTime`; `Tromino.FiniteVerifier.check_correct`, `tileable_iff_certificate`, `completion_iff_certificate`, `nativeRequest_encode_length_le` | [FiniteExactCoverVerifier](LeanTrominoes/FiniteExactCoverVerifier.lean), [FiniteTrominoVerifierBackend](LeanTrominoes/FiniteTrominoVerifierBackend.lean), [FiniteTrominoVerifierSize](LeanTrominoes/FiniteTrominoVerifierSize.lean) |
| Theorem 5.12, finite-preplacement completion decidability for both trominoes | `Tromino.FiniteWitness.decideCompletion_correct`, `completion_iff_bounded_witness` | [FiniteCompletionDecision](LeanTrominoes/FiniteCompletionDecision.lean) |
| Theorem 5.13 and Corollary 5.14, doubled-period domino tilings and completions | `Domino.theorem513`, `corollary514` | [DominoTheorems](LeanTrominoes/DominoTheorems.lean) |
| Corollary 5.15, executable periodic domino decision with a fixed-dimensional polynomial RAM bound | `Domino.corollary515` | [PeriodicDominoSolverCost](LeanTrominoes/PeriodicDominoSolverCost.lean) |
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

[Local planar 1D 3DM with colored degree 2 or 3 is PSPACE-complete](LeanTrominoes/PeriodicThreeDMPlanarLineCompleteness.lean)
under the [complete native binary encoding](LeanTrominoes/PeriodicThreeDMFlatEncoding.lean)
of the instance and supplied drawing. The reduction emits every count, reference,
vertex, segment, and route point. The upper bound combines the matching solver
with a [linear-space drawing verifier](LeanTrominoes/PeriodicThreeDMDrawingVerifier.lean)
that checks incidence endpoints, continuous planarity, halo bounds, and endpoint-only
route-point contacts. [The instance-only matching problem is also PSPACE-complete](LeanTrominoes/PeriodicThreeDMLineCompleteness.lean).
[Normalized 1D trichromatic orientation is PSPACE-complete](LeanTrominoes/NormalizedOrientationLineMembership.lean)
under a [lossless binary encoding](LeanTrominoes/NormalizedOrientationFlatEncoding.lean)
of the full colored cell table and periods. The endpoint requires separated
vertices and a blank vertical boundary. The upper bound checks these constraints
and compiles a bounded reconstruction to the existing unary strip-completion decider.
[Bounded binary preparation](LeanTrominoes/NormalizedOrientationBoundedPreparation.lean)
recovers valid orientation fields in polynomial time without expanding oversized
malformed dimensions. [The complete compiler](LeanTrominoes/NormalizedOrientationCompletionCompiler.lean)
preserves every well-formed drawing. [Valid local 3DM fields also have polynomial numeric bounds](LeanTrominoes/PeriodicThreeDMNativeFieldBounds.lean).

Periodic Horn and dual Horn SAT reduce to finite Horn SAT by identifying all
translates of each variable. The [period-one theorem](LeanTrominoes/PeriodicHornCore.lean)
works over any additive group of offsets, including integer lattices in every
dimension, without a locality bound. The [solver](LeanTrominoes/HornSolver.lean)
performs at most one forward-chaining round per distinct conclusion variable,
then checks negative clauses. It constructs the least Horn model; complementing
it gives a dual Horn model. The [existing CNF API](LeanTrominoes/PeriodicHornDecision.lean)
also checks the Horn restriction. This API uses the repeated-scan solver.

The [indexed worklist solver](LeanTrominoes/HornIndexedSolver.lean) has a
[proved linear operation bound](LeanTrominoes/PeriodicHornLinearTime.lean):
at most `72(n + m + L + 2)` charged operations for periodic Horn or dual Horn
SAT, where `n` is the explicit number of variable slots, `m` the rule count,
and `L` the number of premise occurrences (including duplicates). The bound
includes quotient preparation, occurrence indexing, initialization, and
propagation. The [cost model](LeanTrominoes/HornWorklistRAM.lean) uses unit-cost
indexed RAM access; it is not a bit-Turing or Lean VM runtime bound. Inputs
already use `Fin n` variable indices; renaming arbitrary variable names is
not included. [Examples](LeanTrominoes/HornWorklistExamples.lean) check duplicate
premises and heads, cycles, empty inputs, contradictions, and 3D offsets.

## Paper coverage

This table is the authoritative summary of completed and open paper results.
A result can have proved hardness reductions without all clauses of its numbered
paper theorem being complete; the entries below distinguish these cases.

| Paper results | Current coverage |
| --- | --- |
| Theorem 3.1 | Imported Wang tiling theorem |
| Theorem 3.2 | Complete: local 1D PSPACE completeness, and unrestricted and local co-r.e. completeness in every dimension ≥ 2 |
| Theorems 3.3–3.4 | Local 1D 3SAT and 3SAT-3 PSPACE-completeness proved; local 2D 3SAT and 3SAT-3 co-r.e. completeness proved |
| Theorem 5.2 | Fully proved |
| Corollary 5.3 | Translation-only plane co-r.e. completeness and strip PSPACE completeness proved |
| Theorem 5.5 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Corollary 5.6 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Corollary 5.7 | Proved: finite-seed plane completion by two fixed polyominoes is co-r.e. complete, with a connected 15-cell P. A computable machine-input seed prescribes one Q and canonical refined P patterns. Any completion recovers the universal Wang quarter-plane and every input pin from the original mixed tiling. Unused variables are retained as free bits; inconsistent prescriptions emit an overlapping seed. The input-dependent safety translation preserves the fixed tile pair. The reduction and final theorem pass the axiom audit |
| Two connected polycubes | Full 3D and every fixed slab height > 1 proved |
| Corollary 5.9 | Translation-only co-r.e. completeness in full 3D and every fixed slab height > 1 proved |
| Tromino completion | L- and I-tromino plane co-r.e. completeness, strip PSPACE completeness (unary encoding), and the aperiodic-completion corollary proved |
| Theorems 2.1–2.2, Lemma 2.3 | Theorem 2.1 is proved for arbitrary degrees, including loops and isolated vertices: compatible simple real routes, locality, orthocrossing, vertex avoidance, grid size ≤16(|V|+|E|+1), and orthogonal routes for degree four. Lemma 2.3 is proved for any real planar orthogonal drawing: normalization preserves rational vertex positions, real planarity, simplicity, and locality; the grid grows by a factor of 32; degree-three incidences use west, north, east, with the selected incidence west. General slab separation, crossing-order preservation, complete rational crossing tables of size ≤18M², vertex-rectangle isolation, all 41 degree-four rectangle connector profiles, automatic distinct incidence-ray assignments, simple disjoint slab routes, and cubic refinement bounds are proved; the full planar refinement in Theorem 2.2 remains open |
| Theorems 3.5–3.7 | Complete with supplied, verified planar drawings in 1D and 2D. Local planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3 have the polynomial grid restriction (in fact linear in 2D). Local planar 3DM has colored degree 2 or 3. Native encodings have PSPACE completeness in 1D and co-r.e. completeness in 2D |
| Theorem 3.8 | Normalized trichromatic orientation is co-r.e. complete in 2D and PSPACE complete in 1D under its native binary encoding. Finite normalized planar drawings are NP-complete under a sparse unary encoding. General periodic colored graph orientation is co-r.e. complete via an explicit contracted-edge encoding; the general local planar, 1D, and finite graph packaging remains open |
| Section 4, Horn and dual Horn SAT | Period-one models in every dimension, finite-quotient equivalence, and executable solvers proved; linear operation bound proved for explicitly indexed inputs in the unit-cost RAM model |
| Theorem 4.1 | Executable local periodic 2SAT decision in every fixed dimension, with a verified polynomial indexed-RAM operation bound including clause normalization and finite-cover construction |
| Lemma 4.3 | In every dimension, every free vertex of a period-one matching in a local periodic graph with a perfect matching starts a simple augmenting path of diameter at most `2*d*|E|`; no bipartiteness assumption |
| Lemma 4.4 | Every proper bipartition of a connected periodic graph is invariant under twice every lattice translation, in every dimension |
| Lemma 4.5 | Any imperfect period-one partial matching of a bipartite periodic graph with a perfect matching has an augmenting path with no repeated protovertex and edge length strictly less than the quotient vertex count |
| Theorem 4.6 | Every perfect matching in a bipartite periodic graph implies a period-one perfect matching; equivalence with finite quotient matching proved in every dimension, without a locality restriction |
| Theorem 4.7 | Executable decision and period-one matching construction in every dimension, with a verified `O(E√V)` bound for indexed inputs in the unit-cost RAM model |
| Lemma 5.1 | Arbitrary finite-footprint periodic subspace tiling and completion are co-r.e. in every dimension. Both strip problems are in PSPACE for each fixed polynomial bounding box under native binary encoding; the palette, target, and prefill are all input |
| Theorem 5.12 | Decidability and NP-completeness proved for both trominoes, with the canonical bounding box listed in the encoding: `Tromino.FiniteCoordinateColumns.completion_npComplete` |
| Theorem 5.13 | Every tileable periodic domino region has a tiling invariant under twice each original generator, in every ambient dimension and periodic rank |
| Corollary 5.14 | Every completable periodic domino prefill has a completion with those doubled periods |
| Corollary 5.15 | Executable decision from cell representatives and arbitrary nonsingular integer period matrices; quadratic operation budget in the number of representatives for each fixed dimension, in the unit-cost arithmetic RAM model |
| Corollary 5.4 | Proved for both trominoes under the explicit unary coordinate encoding: `Tromino.FiniteCoordinateColumns.region_npComplete` |
| Other results 5.7–5.11 except those listed above | Open |

The [finite-seed polyomino search](LeanTrominoes/FinitePolyominoCompletionSearch.lean)
keeps every prescribed placement at every finite stage, including placements
outside the inspected box. Its compactness theorem characterizes plane
completion exactly by success at all stages. The
[primitive-recursive verifier](LeanTrominoes/FinitePolyominoCompletionCoRE.lean)
proves co-r.e. membership when both shapes are fixed and only the seed varies.
[Boundary examples](LeanTrominoes/FinitePolyominoCompletionExamples.lean)
check overlapping seeds outside the initial box and reject extra proof axioms.

[Cook–Levin](LeanTrominoes/FiniteSATNPHard.lean) is proved for the
[verifier-based NP definition](LeanTrominoes/NP.lean): every NP language reduces
to ordinary finite 3CNF SAT under the native binary formula encoding. The
[complete request emitter](LeanTrominoes/FiniteNPRequestEmitter.lean) generates
initialization with a bounded unknown certificate, acceptance, well-formedness,
and padded transitions, with absolute variable names and exact clause counts.
It composes with the checked quadratic-time
[finite-CNF backend](LeanTrominoes/FiniteCNFCompiler.lean). The reduction uses
actual finite-alphabet polynomial-time Turing machines throughout.
[Finite-region certificates](LeanTrominoes/FiniteTrominoRegionCertificate.lean)
use 24 bits per listed cell. For
[finite-preplacement completion](LeanTrominoes/FiniteTrominoCompletionCertificate.lean),
24 bits per bounding-box cell suffice for either tromino, including tiles
protruding outside the box. The
[exact-cover verifier backend](LeanTrominoes/FiniteExactCoverVerifier.lean) is
an actual finite-alphabet polynomial-time machine. Its
[geometric correctness](LeanTrominoes/FiniteTrominoVerifierBackend.lean) and
[serialized candidate-table bound](LeanTrominoes/FiniteTrominoVerifierSize.lean)
are proved. The [native coordinate verifier](LeanTrominoes/FiniteTrominoNativeVerifier.lean)
now generates the candidate table itself, including signed coordinate arithmetic,
canonical footprint names, and stable deduplication. This proves
[finite-region membership in NP](LeanTrominoes/FiniteTrominoRegionInNP.lean)
under the explicit unary coordinate encoding, and
[finite-preplacement completion membership in NP](LeanTrominoes/FiniteTrominoCompletionInNP.lean)
when the canonical bounding box is explicitly listed in that encoding.
These statements charge for unary coordinate magnitudes and the listed box;
they do not establish membership under an unpadded binary-coordinate encoding.
[Finite-region NP-completeness](LeanTrominoes/FiniteTrominoRegionNPComplete.lean)
is proved for both trominoes under the original unary coordinate encoding.
[Finite-preplacement plane completion is also NP-complete](LeanTrominoes/FiniteTrominoCompletionNPComplete.lean)
for both trominoes when the canonical bounding box is listed in the encoding.

The [finite substitution bridge](LeanTrominoes/FiniteGadgetSubstitution.lean)
now proves orientation equivalent to finite-motif tileability for both trominoes,
when the normalized drawing has a blank final row and column. A three-cell gap
separates its periodic copies, so this uses the existing substitution theorem
without assuming a periodic tiling. The
[finite region emitter](LeanTrominoes/FiniteGadgetRegionCompiler.lean) expands
compiled sparse drawing records into the original unary coordinate encoding
with verified polynomial-time machines. The finite SAT source-to-drawing
correctness theorem is now connected to this endpoint.

[Finite occurrence-three SAT](LeanTrominoes/FiniteThreeSATThreeNPHard.lean)
is now NP-hard under the native binary formula encoding, with clauses of
width at most three, compact natural variable names, and no empty clauses.
The [compiler](LeanTrominoes/FiniteNPThreeOccurrenceCompiler.lean) composes
the finite Cook–Levin emitter with verified occurrence-splitting machines.
For its zero-offset graph, the
[route bounds](LeanTrominoes/FiniteOrthocrossingBounds.lean) place every segment
inside one fundamental square; canonical crossings use only zero translates.
The [retained planarization](LeanTrominoes/FiniteRetainedPlanarSAT.lean)
now preserves ordinary finite SAT, including its canonical gauge and clause
deduplication. [Zero offsets](LeanTrominoes/FiniteRetainedThreeDMOffsets.lean)
persist through fixed-eight splitting, Figure 9, unit elimination, the final
canonical gauge, routed polarity normalization, and planar 3DM assembly.
[Finite normalization](LeanTrominoes/FiniteThreeDMNormalization.lean) pads the
zero-offset drawing inside one square, preserves complete route separation
and simplicity, and moves the blank seams to the final boundary. The
[finite retained region](LeanTrominoes/FiniteRetainedTrominoRegion.lean) is
tileable exactly when the finite source formula is satisfiable, for either
tromino. The [shared program-source interface](LeanTrominoes/PeriodicCNFProgramSource.lean)
accepts both the existing PSPACE source and the finite NP verifier source. The
[finite source compiler](LeanTrominoes/FiniteProgramTrominoRegionCompiler.lean)
now emits the padded, seam-shifted sparse drawing and its finite gadget region
in the original encoding, with no source-emitter hypothesis.

The [finite completion construction](LeanTrominoes/FiniteDrawingCompletion.lean)
uses a finite collar of preplaced brick motifs. Local barrier and portal
ownership proofs extract the required circuit behavior from any plane
completion. The [completion compiler](LeanTrominoes/FiniteProgramCompletionCompiler.lean)
evaluates signed-coordinate palette queries, emits the prescribed placements,
and computes their exact canonical radius before listing the bounding box.
The final finite NP-completeness theorems use only `propext`, `Classical.choice`,
and `Quot.sound`. All finite certificates are checked by Lean's kernel; the
[axiom regression checks](LeanTrominoes/AxiomAudit.lean) reject additional assumptions.


The [domino results](LeanTrominoes/DominoTheorems.lean) use exact covers by
face-adjacent two-cell footprints. The proofs allow disconnected regions and
arbitrary initial tilings. Completion keeps every prefilled domino fixed.
The decision procedure derives adjacency using an integer-matrix coordinate
decoder, doubles the period lattice to preserve checkerboard colors, and runs
the finite matching solver. Its budget includes coordinate searches and cover
construction. Dimension-dependent constants include `2^d` and determinant
preparation; this is a fixed-dimension arithmetic-RAM bound, not a bit-Turing
or Lean VM runtime claim. [Kernel-evaluated examples](LeanTrominoes/PeriodicDominoExamples.lean)
cover holes, skew periods, and empty and zero-dimensional regions.

The [general subspace membership proof](LeanTrominoes/Lemma51.lean) uses
finite footprint records in fundamental-domain coordinates. Records include
all allowed prototile orientations and representative anchors. The
[geometry bridge](LeanTrominoes/PeriodicSubspaceGeometry.lean) proves their
containment and exact-cover semantics, including transport to physical cells
through a fundamental-domain chart. Completion prescribes whole placement
orbits; the completing tiling itself may be nonperiodic.

The [strip decider](LeanTrominoes/PeriodicSubspaceStripMembership.lean) stores
one bit per record per column in a window of `2*B+1` columns and runs the
verified Savitch cycle search. Its binary encoding includes the target,
records, bound, and prescribed orbit list. For any fixed polynomial `p`,
the input promise is `B ≤ p(input length)`; every reachable machine
configuration has polynomial space. No fixed palette or connectedness
assumption is used. The [regressions](LeanTrominoes/PeriodicSubspaceExamples.lean)
cover empty instances, duplicates, sparse labels, signed offsets, overlap,
and invalid prefills.

The [periodic 2SAT solver](LeanTrominoes/PeriodicTwoSATLocalTime.lean)
accepts empty clauses and duplicated literals for units. Locality bounds
coordinatewise offset differences, which includes the paper's Manhattan
locality. Each clause is first anchored at its first literal, preserving all
assignments even when the common offset is large. The solver uses an explicit
finite cover with base-`M` coordinate indices and the verified Horn worklist
solver for opposite-literal reachability tests. The
[cover theorem](LeanTrominoes/PeriodicPowerTwoCover.lean) proves that a uniformly
chosen power-of-two period preserves contradictions. For every fixed `d`, the
complete operation bound has degree `3(d²+d+1)` in `n + clauses + 1`, where `n`
is the number of explicit variable slots. It uses the same unit-cost indexed
RAM model as the matching and Horn solvers. The
[regressions](LeanTrominoes/PeriodicTwoSATExamples.lean) include kernel-evaluated
units, inconsistent units, empty inputs, and dimension zero, as well as a
satisfiable alternation formula with no period-one assignment.

The [bipartite matching solver](LeanTrominoes/PeriodicMatchingSolver.lean)
uses breadth-first layers and disjoint blocking paths. Its bound includes
quotient indexing, vertex-array initialization, and selection of a finite
protoedge table describing the period-one matching. Here `E` counts edge
records and `V` counts vertex slots. The uniform bound is
`1000(E+1)(⌊√V⌋+1)`, with `4000E⌊√V⌋` for nonempty edge tables.
Indices and scalar operations have unit cost; coordinate vectors remain in
the input store. This is not a bit-Turing or Lean VM runtime bound.

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
The original planar reductions are primitive recursive. Separate native
polynomial-time reductions now prove all four planar PSPACE-hardness endpoints.

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
[Local 1D planar 1-in-3SAT and 1-in-3SAT-3 are PSPACE-complete](LeanTrominoes/PeriodicPlanarExactOneLinePolySpaceCompleteness.lean)
under that encoding. The [native binary encoder](LeanTrominoes/PeriodicCNFStripNativePlanarEncoding.lean)
compiles the entire routed formula and supplied drawing: numeric atom names,
signed offsets, vertices, routes, indexed segments, and finite-check radius.
[Semantic correctness and planarity](LeanTrominoes/PeriodicCNFStripNativePlanarSemantics.lean),
[locality and the occurrence-three bound](LeanTrominoes/PeriodicCNFStripNativePlanarLocality.lean),
and the [original fixed grid bound](LeanTrominoes/PeriodicCNFStripNativePlanarGridBound.lean)
connect this encoder to both target languages. The reduction uses the
anchor-normalized, numerically renamed routed exact-one construction,
which differs from the earlier primitive-recursive endpoint.

[Local 1D planar 3SAT and 3SAT-3 are also PSPACE-complete](LeanTrominoes/PeriodicPlanarOrdinaryLinePolySpaceCompleteness.lean).
Their [native binary encoder](LeanTrominoes/PeriodicCNFStripNativeOrdinaryEncoding.lean)
compiles the entire ordinary formula and supplied drawing.
[Semantic correctness](LeanTrominoes/PeriodicCNFStripNativeOrdinaryInput.lean)
preserves one-dimensionality, locality, the three-occurrence bound, planarity,
and the original fixed linear grid bound after anchor normalization and numeric renaming.

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
allow invalid restricted presentations to be rejected. The membership and completeness theorems
use only `propext`, `Classical.choice`, and `Quot.sound`.

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

The completion geometry, serialization, and final completeness theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. Their finite certificates
are checked by Lean's kernel, and the [axiom regression checks](LeanTrominoes/AxiomAudit.lean)
reject native-evaluation assumptions and unfinished proofs.

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

Check the final theorems' axiom dependencies and replay imported proofs
in a fresh kernel environment:

```sh
lake env lean LeanTrominoes/AxiomAudit.lean
lake env leanchecker --fresh LeanTrominoes
```

The project uses Lean 4.31.0 and depends on
[`lean-wang`](https://github.com/edemaine/lean-wang).
[lean-toolchain](lean-toolchain) pins Lean;
[lake-manifest.json](lake-manifest.json) pins the fetched dependencies.
