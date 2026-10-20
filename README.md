# lean-trominoes

Lean formalization of
[*Undecidability of Tiling with a Tromino*](https://arxiv.org/abs/2509.07906)
by the MIT--ULB CompGeom Group, Zachary Abel, Hugo Akitaya, Lily Chung,
Erik D. Demaine, Jenny Diomidova, Della Hendrickson, Stefan Langerman, and
Jayson Lynch. The working paper is included as
[PDF](trominoes.pdf) and [source](trominoes.texlish).
Use the checked-in source as the reference for theorem statements and proofs
in this formalization.

The numbered paper results and their formalization scope are summarized in
the coverage table below. Theorem 5.2 is
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

## Formal abstracts

Two formal abstracts present the main results with the mathematical definitions
needed to read their statements. To review what the formalization proves, check
these definitions and theorem statements; Lean verifies the proofs through the
corresponding bridges and the rest of the development. Section comments organize
each abstract. `ComplexityAbstract` supplies the shared complexity definitions
and a bounded-word RAM model; Mathlib and `lean-wang` are background.
All other graph and tiling notions and encodings are defined within the
abstract suite; only proof bodies refer to the implementation.
`ComplexityAbstract.RAM.DecidesWithin` is defined in the shared abstract's
bounded-word RAM section. The verification files contain full proofs and examples;
they are separate from the public abstract suite.

The abstracts’ supplied planar SAT drawings are orthogonal and continuously planar, with
coincident lifted listed points allowed only at outer route endpoints.
The co-r.e. and PSPACE classifications include these conditions for ordinary
and exact-one SAT, including the occurrence-bounded variants.

A RAM algorithm must use one fixed program for every sufficiently large word
size `w ≥ c log₂(n+2)` accommodating the input words. Arithmetic overflow and
out-of-range addresses fault. Horn SAT, local periodic 2SAT, finite bipartite matching, and periodic domino
decision now have complete original-input program simulations in this model.

The [word RAM with memory allocation](LeanTrominoes/Computation/RAM/Allocation.lean)
reserves fresh blocks without freeing or reusing addresses. A zeroed block of
`k` words takes exactly `4k+7` primitive instructions;
[indexed array reads and writes](LeanTrominoes/Computation/RAM/Arrays.lean)
take two instructions each. Fixed-size records use the same blocks with constant
field indices. These operations compile to the RAM above. Space usage is the
high-water mark, including storage no longer used. Its bound ensures pointers
fit in words; this does not assert a separate solver space-complexity result.

The [concrete Horn RAM program](LeanTrominoes/SAT/Horn/HornWordRAMProgram.lean)
has a checked [linear-time decision theorem](LeanTrominoes/SAT/Horn/HornWordRAMLinearTime.lean):
one fixed 32-register program decides the original finite Horn rule/occurrence
encoding in at most `120(S+1)` primitive instructions for every
`w ≥ 27 log₂(S+2)+2`. Here `S` counts variables, rules, occurrences, and one.
The bound includes allocation and zeroing, occurrence indexing, initial-stack
construction, propagation, the answer test, and halt. Duplicate premises and
clauses with a contradiction head are included.
The [finite reachability query kernel](LeanTrominoes/Computation/Compiler/FiniteReachWordRAM.lean)
also has a linear word-RAM bound in its explicit dense graph-query encoding.
The [complete periodic 2SAT program](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATWordRAMPolynomialTime.lean)
now has a polynomial-time RAM theorem from its original signed clause records,
including normalization, cover construction, query batching, and halt.
The [finite matching program](LeanTrominoes/Graphs/Matching/BipartiteMatchingDenseWordRAMPolynomialTime.lean)
uses 64 registers and at most `1000(S+1)^4` instructions, where
`S = left vertices + right vertices + edge records + 1`, for every
`w ≥ 8 log₂(S+2)+2`. It reads the original endpoint arrays and includes
allocation, search, path rewrites, answer, and halt.

The [periodic domino program](LeanTrominoes/Tiling/Domino/DominoWordRAMPolynomialTime.lean)
uses 128 registers and decides valid original binary presentations in every
fixed dimension. Its conservative instruction bound is `C(d)(S+1)^16`, with
`w ≥ k(d) log₂(S+2)+2`; `S` is the explicitly defined binary presentation size.
The proof includes multiword signed arithmetic, determinant and lattice tests,
all candidate loops, endpoint packing, matching, and halt. The candidate scan
has a quartic bound; clearing the cold matching arena accounts for exponent 16.

| Abstract | Proof bridge |
| --- | --- |
| [Complexity and RAM model](LeanTrominoes/ComplexityAbstract.lean) | [ComplexityAbstractBridge](LeanTrominoes/ComplexityAbstractBridge.lean) |
| [Graphs, constraints, and algorithms](LeanTrominoes/GraphAbstract.lean) | [Graphs](LeanTrominoes/GraphAbstractBridge.lean), [drawings](LeanTrominoes/GraphDrawingAbstractBridge.lean), [constraints](LeanTrominoes/GraphConstraintsAbstractBridge.lean), [planar SAT](LeanTrominoes/GraphPlanarAbstractBridge.lean), [3DM](LeanTrominoes/GraphThreeDMAbstractBridge.lean), [orientation](LeanTrominoes/GraphOrientationAbstractBridge.lean), [Horn and matching](LeanTrominoes/GraphAlgorithmsAbstractBridge.lean), [2SAT](LeanTrominoes/GraphTwoSATAbstractBridge.lean) |
| [Tiling and completion](LeanTrominoes/TilingAbstract.lean) | [TilingAbstractBridge](LeanTrominoes/TilingAbstractBridge.lean), [domino algorithm](LeanTrominoes/TilingAlgorithmsAbstractBridge.lean) |

Import `LeanTrominoes.GraphAbstract` or `LeanTrominoes.TilingAbstract` individually;
`import LeanTrominoes` includes both. To check both abstracts and their bridges:

```sh
lake build +LeanTrominoes.GraphAbstract:olean +LeanTrominoes.TilingAbstract:olean
```

The [dependency audit](LeanTrominoes/Verification/AbstractDependencies.lean) checks
the public definition and theorem-statement boundary transitively.
The [axiom audit](LeanTrominoes/Verification/AxiomAudit.lean) checks every declaration
in the abstracts and their bridges, including future additions, the
[RAM semantics checks](LeanTrominoes/Verification/WordRAM.lean), and the word-bound modules below.

[Polynomial magnitudes fit logarithmic words](LeanTrominoes/Computation/RAM/WordBounds.lean),
uniformly for every larger word size. Checked magnitude invariants cover
[Horn counters and queues](LeanTrominoes/SAT/Horn/HornWorklistWordBounds.lean),
[matching breadth-first labels](LeanTrominoes/Graphs/Matching/BipartiteMatchingWordBounds.lean),
[2SAT finite-cover indices](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATWordBounds.lean), and
[domino coordinate decoding](LeanTrominoes/Tiling/Domino/PeriodicDominoWordBounds.lean).
These establish scalar bounds; they do not supply the missing program simulations.
Domino inputs permit arbitrary integer coordinates and period matrices. Their
decoder bounds depend on input-entry magnitudes as well as dimension. A determinant
can exceed a single input word, so accommodating all input words alone does not
justify one-word determinant arithmetic. For fixed dimension, the new proofs
show that determinants and neighbor probes need only a constant number of input
words. The multiword arithmetic implementation and its instruction costs remain
to be proved.

## Repository organization

The library is organized by mathematical subject. The result and coverage tables
below follow the paper's order.

| Directory | Contents | Paper material |
| --- | --- | --- |
| [Graphs](LeanTrominoes/Graphs/README.md) | `Core` and `Drawings`; `Orientation`; `Matching` | Section 2; Section 3 orientation; Section 4 matching |
| [SAT](LeanTrominoes/SAT/README.md) | CNF, 3SAT, exact-one and planar SAT; `TwoSAT` and `Horn` algorithms | Section 3 reductions; Section 4 algorithms |
| [ThreeDM](LeanTrominoes/ThreeDM/README.md) | Three-dimensional matching, reductions, encodings, and completeness | Section 3 planar 3DM |
| [Tiling](LeanTrominoes/Tiling/README.md) | Trominoes, polyominoes, polycubes, completion, and dominoes | Section 5 |
| [Common](LeanTrominoes/Common/README.md) | Shared geometry, lists, arithmetic, and periodic constraints | Shared infrastructure |
| [Complexity](LeanTrominoes/Complexity/README.md) | Complexity interfaces, encodings, reductions, and certifications | Shared infrastructure |
| [Computation](LeanTrominoes/Computation/README.md) | Reusable machines, evaluators, encoders, and compiler combinators | Shared infrastructure |
| [Verification](LeanTrominoes/Verification/README.md) | Axiom audits and complete-library verification | Verification infrastructure |

Finite, line, plane, and slab variants stay with their mathematical subject.
Specialized compilers stay with their reductions: the CNF-to-tromino strip
compiler is in `Tiling/Tromino/Strip`, while SAT occurrence-splitting geometry
is in `SAT/Planar/OccurrenceSplit`. Larger families have subdirectories for
carriers, routes, raster requests, encodings, and finite certificates.

The public root [LeanTrominoes.lean](LeanTrominoes.lean) imports each subject's
`Results.lean`, collecting the previously exposed results. Orientation also has
a [separate entry point](LeanTrominoes/Graphs/Orientation/Results.lean).
The verification batches jointly cover every local module.

Module paths changed during reorganization; declaration namespaces and theorem
names are preserved. The [module relocation map](data/module-relocations.json)
records updated imports. See [the maintenance guide](docs/organization.md) for
import lookup, build and verification commands, and generator conventions.

## Main statements and proofs

Start with [Theorem52.lean](LeanTrominoes/Tiling/Tromino/Theorem52.lean) to read the complete
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
| Theorem 5.2, complete result | `Theorem52.proved` | [Theorem52Proof](LeanTrominoes/Tiling/Tromino/Theorem52Proof.lean) |
| Theorem 5.2, strip PSPACE completeness | `Theorem52.stripProved` | [Theorem52Proof](LeanTrominoes/Tiling/Tromino/Theorem52Proof.lean) |
| Theorem 5.2, complete plane result | `PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement` | [PeriodicWangPlanarThreeDMReduction](LeanTrominoes/ThreeDM/PeriodicWangPlanarThreeDMReduction.lean) |
| Corollary 5.3, two translation-only I trominoes, plane and strip | `TwoTranslationTrominoes.proved` | [TwoTranslationTrominoes](LeanTrominoes/Tiling/Tromino/TwoTranslationTrominoes.lean) |
| Theorem 5.5, plane co-r.e. completeness | `Theorem55.planeProved` | [Theorem55Proof](LeanTrominoes/Tiling/Polyomino/Theorem55Proof.lean) |
| Theorem 5.5, strip PSPACE completeness | `Theorem55.stripProved` | [Theorem55StripProof](LeanTrominoes/Tiling/Polyomino/Theorem55StripProof.lean) |
| Corollary 5.6, translations only, plane and strip | `ThreeTranslationPolyominoes.proved` | [ThreeTranslationProof](LeanTrominoes/Tiling/Polyomino/ThreeTranslationProof.lean) |
| Corollary 5.9, translations only, full 3D and every fixed slab height > 1 | `ThreeTranslationPolycubes.proved` | [ThreeTranslationPolycubesProof](LeanTrominoes/Tiling/Polycube/ThreeTranslationPolycubesProof.lean) |
| Two connected polycubes, full-space co-r.e. completeness | `TwoConnectedPolycubes.spaceProved` | [TwoConnectedPolycubesSpaceProof](LeanTrominoes/Tiling/Polycube/TwoConnectedPolycubesSpaceProof.lean) |
| Two connected polycubes, every fixed slab height > 1 | `TwoConnectedPolycubes.slabsProved` | [TwoConnectedPolycubesSlabsProof](LeanTrominoes/Tiling/Polycube/TwoConnectedPolycubesSlabsProof.lean) |
| Periodic L-tromino completion, plane co-r.e. hardness | `CompletionPattern.LBricks.lCompletion_coREHard` | [CompletionLHardness](LeanTrominoes/Tiling/Completion/CompletionLHardness.lean) |
| Periodic I-tromino completion, plane co-r.e. hardness | `CompletionPattern.IBricks.iCompletion_coREHard` | [CompletionIHardness](LeanTrominoes/Tiling/Completion/CompletionIHardness.lean) |
| Periodic L- and I-tromino completion, plane co-r.e. completeness | `PeriodicTrominoPrefill.planeProblem_coREComplete` | [CompletionCompleteness](LeanTrominoes/Tiling/Completion/CompletionCompleteness.lean) |
| Periodic L- and I-tromino completion, strip PSPACE completeness (unary encoding) | `PeriodicStripTrominoPrefill.problem_PSPACEComplete` | [CompletionStripHardness](LeanTrominoes/Tiling/Completion/CompletionStripHardness.lean) |
| Periodic L- and I-tromino prefills admitting only aperiodic completions | `PeriodicTrominoPrefill.exists_aperiodic_completion` | [CompletionAperiodic](LeanTrominoes/Tiling/Completion/CompletionAperiodic.lean) |
| Plane co-r.e. membership | `periodicTrominoTiling_coRE` | [ComputableSearch](LeanTrominoes/Tiling/Periodic/ComputableSearch.lean) |
| Theorem 5.2, strip PSPACE membership | `PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE` | [PartrecFlatStripDeciderSpace](LeanTrominoes/Tiling/Tromino/Strip/PartrecFlatStripDeciderSpace.lean) |
| Theorem 3.2, local 1D periodic CNF SAT PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEComplete` | [PeriodicCNFPolySpaceMembership](LeanTrominoes/SAT/CNF/PeriodicCNFPolySpaceMembership.lean) |
| Theorem 3.3, local 1D periodic 3SAT PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicThreeCNF1DSAT_PSPACEComplete` | [PeriodicCNFFieldWidth](LeanTrominoes/SAT/CNF/PeriodicCNFFieldWidth.lean) |
| Theorem 3.4, local 1D periodic 3SAT-3 PSPACE completeness | `PeriodicCNF.PolySpaceHardness.localPeriodicThreeSATThree1DSAT_PSPACEComplete` | [PeriodicThreeSATThreePolySpaceCompleteness](LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreePolySpaceCompleteness.lean) |
| Supplied-drawing planar SAT, all four variants, full orthogonal/contact geometry, plane co-r.e. completeness | `PeriodicPlanarSAT.GeometricNat.ordinary`, `ordinaryThree`, `exactOne`, `exactOneThree` | [PeriodicPlanarSATGeometricNatCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarSATGeometricNatCompleteness.lean) |
| Supplied-drawing planar SAT, all four variants, full orthogonal/contact geometry, binary PSPACE completeness on the line | `PeriodicPlanarSAT.geometricOrdinary_PSPACEComplete`, `geometricOrdinaryThree_PSPACEComplete`, `geometricExactOne_PSPACEComplete`, `geometricExactOneThree_PSPACEComplete` | [PeriodicPlanarSATGeometricCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarSATGeometricCompleteness.lean) |
| Local 1D planar SAT, all four variants, total semantic reductions with linear grid bounds | `PeriodicPlanarSAT.LineReduction.ordinary_correct`, `ordinaryThreeOccurrence_correct`, `exactOne_correct`, `exactOneThreeOccurrence_correct` | [PeriodicPlanarSATLineReduction](LeanTrominoes/SAT/Planar/PeriodicPlanarSATLineReduction.lean) |
| Local 1D planar 3SAT and 3SAT-3, native flat-encoded PSPACE completeness | `PeriodicPlanarSAT.ordinary_PSPACEComplete`, `ordinaryThree_PSPACEComplete` | [PeriodicPlanarOrdinaryLinePolySpaceCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarOrdinaryLinePolySpaceCompleteness.lean) |
| Local 1D planar 1-in-3SAT and 1-in-3SAT-3, native flat-encoded PSPACE completeness | `PeriodicPlanarSAT.exactOne_PSPACEComplete`, `exactOneThree_PSPACEComplete` | [PeriodicPlanarExactOneLinePolySpaceCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarExactOneLinePolySpaceCompleteness.lean) |
| Supplied periodic drawing planarity, flat binary PSPACE membership | `PeriodicGridDrawing.Arithmetic.isContinuouslyPlanar_inPSPACE` | [PeriodicDrawingPolySpaceVerification](LeanTrominoes/Graphs/Drawings/Grid/PeriodicDrawingPolySpaceVerification.lean) |
| Local 1D planar SAT, all four variants, executable supplied-drawing decisions | `PeriodicPlanarSAT.LineDecision.ordinaryCheck_correct`, `ordinaryThreeCheck_correct`, `exactOneCheck_correct`, `exactOneThreeCheck_correct` | [PeriodicPlanarSATLineDecision](LeanTrominoes/SAT/Planar/PeriodicPlanarSATLineDecision.lean) |
| Local 1D 1-in-3SAT and 1-in-3SAT-3, native flat-encoded PSPACE completeness | `PeriodicExactOneCNF.localOneDimensionalThreeSAT_PSPACEComplete`, `localOneDimensionalThreeSATThree_PSPACEComplete` | [PeriodicExactOnePolySpaceCompleteness](LeanTrominoes/SAT/ExactOne/PeriodicExactOnePolySpaceCompleteness.lean) |
| Local 1D exact-one SAT, executable decisions for unrestricted, width-three, and occurrence-three variants; linear state and encoding-size bounds | `PeriodicExactOneCNF.check_correct`, `checkThree_correct`, `checkThreeThree_correct`, `state_bits_le_encoding`, `flatEncoding_length_le` | [PeriodicExactOneCNFLocality](LeanTrominoes/SAT/ExactOne/PeriodicExactOneCNFLocality.lean), [PeriodicExactOneCNFFlatSize](LeanTrominoes/SAT/ExactOne/PeriodicExactOneCNFFlatSize.lean) |
| Local 1D periodic CNF, executable decision procedure and linear state-bit bound | `PeriodicCNF.LineWindow.check_localPeriodicCNF1DSAT`, `state_bits_le_encoding` | [PeriodicCNFLineSearch](LeanTrominoes/SAT/CNF/PeriodicCNFLineSearch.lean) |
| Theorem 3.2, 2D periodic CNF SAT co-r.e. completeness | `WangPeriodicCNF.coREComplete`, `WangPeriodicCNF.localCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/SAT/CNF/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.2, periodic CNF SAT in every dimension ≥ 2 | `PeriodicCNFDimensions.satisfiable_coREComplete`, `PeriodicCNFDimensions.localProblem_coREComplete` | [PeriodicCNFDimensions](LeanTrominoes/SAT/CNF/PeriodicCNFDimensions.lean) |
| Theorem 3.7, local planar 2D 3DM with colored degree 2 or 3 | `PeriodicThreeDM.localPlaneProblem_coREComplete` | [PeriodicThreeDMLocalPlaneCompleteness](LeanTrominoes/ThreeDM/Plane/PeriodicThreeDMLocalPlaneCompleteness.lean) |
| Theorem 3.3, local 2D periodic 3SAT co-r.e. completeness | `PeriodicThreeCNF.localThreeCNFCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/SAT/CNF/PeriodicSATPlaneCompleteness.lean) |
| Theorem 3.4, local 2D periodic 3SAT-3 co-r.e. completeness | `PeriodicThreeSATThree.localThreeSATThreeCoREComplete` | [PeriodicSATPlaneCompleteness](LeanTrominoes/SAT/CNF/PeriodicSATPlaneCompleteness.lean) |
| Local 2D periodic 1-in-3SAT-3 co-r.e. completeness (without a planarity restriction) | `PeriodicOneInThree.localOneInThreeSATThreeCoREComplete` | [PeriodicOneInThreeCompleteness](LeanTrominoes/SAT/ExactOne/PeriodicOneInThreeCompleteness.lean) |
| Plane periodic 3SAT with checked continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.WangReduction.coREComplete` | [PeriodicPlanarSATCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarSATCompleteness.lean) |
| Plane periodic 3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction.coREComplete` | [PeriodicPlanarThreeOccurrenceCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarThreeOccurrenceCompleteness.lean) |
| Plane periodic 1-in-3SAT and 1-in-3SAT-3 with supplied continuous planar drawings, co-r.e. completeness | `PeriodicPlanarSAT.ExactOneEndpoint.WangReduction.coREComplete`, `threeOccurrenceCoREComplete` | [PeriodicPlanarExactOneCompleteness](LeanTrominoes/SAT/Planar/PeriodicPlanarExactOneCompleteness.lean) |
| Plane periodic 3DM with checked drawings and degree 2 or 3, co-r.e. completeness | `PeriodicThreeDM.planeProblem_coREComplete` | [PeriodicThreeDMPlaneCompleteness](LeanTrominoes/ThreeDM/Plane/PeriodicThreeDMPlaneCompleteness.lean) |
| Local 1D periodic 3DM with colored degree 2 or 3, native PSPACE completeness | `PeriodicThreeDM.localLineProblem_PSPACEComplete` | [PeriodicThreeDMLineCompleteness](LeanTrominoes/ThreeDM/Line/PeriodicThreeDMLineCompleteness.lean) |
| Local planar 1D periodic 3DM with colored degree 2 or 3 and supplied drawing, native PSPACE completeness | `PeriodicThreeDM.localPlanarLineProblem_PSPACEComplete` | [PeriodicThreeDMPlanarLineCompleteness](LeanTrominoes/ThreeDM/Line/PeriodicThreeDMPlanarLineCompleteness.lean) |
| Normalized plane trichromatic orientation, co-r.e. completeness | `Gadget.NormalizedOrientation.coREComplete` | [NormalizedOrientationCompleteness](LeanTrominoes/Graphs/Orientation/NormalizedOrientationCompleteness.lean) |
| Normalized 1D trichromatic orientation, native binary PSPACE completeness | `Gadget.NormalizedOrientation.lineProblem_PSPACEComplete` | [NormalizedOrientationLineMembership](LeanTrominoes/Graphs/Orientation/NormalizedOrientationLineMembership.lean) |
| Ordinary local 1D colored graph orientation, native binary PSPACE completeness | `TrichromaticGraphOrientation.localLineProblem_PSPACEComplete` | [TrichromaticGraphOrientationLineHardness](LeanTrominoes/Graphs/Orientation/TrichromaticGraphOrientationLineHardness.lean) |
| Ordinary finite colored graph orientation, native binary NP completeness | `TrichromaticGraphOrientation.finiteProblem_npComplete` | [TrichromaticGraphOrientationFiniteBinaryInNP](LeanTrominoes/Graphs/Orientation/TrichromaticGraphOrientationFiniteBinaryInNP.lean), [TrichromaticGraphOrientationFiniteHardness](LeanTrominoes/Graphs/Orientation/TrichromaticGraphOrientationFiniteHardness.lean) |
| Periodic Horn and dual Horn SAT, period-one models in every dimension | `Horn.exists_period_one`, `Horn.dual_exists_period_one` | [PeriodicHornCore](LeanTrominoes/SAT/Horn/PeriodicHornCore.lean), [PeriodicHornSolver](LeanTrominoes/SAT/Horn/PeriodicHornSolver.lean) |
| Periodic Horn and dual Horn SAT, executable solvers and period-one model construction | `Horn.periodicCheck_correct`, `periodicDualCheck_correct`; `PeriodicCNF.hornCheck_correct`, `dualHornCheck_correct`, `hornModel_correct`, `dualHornModel_correct` | [PeriodicHornSolver](LeanTrominoes/SAT/Horn/PeriodicHornSolver.lean), [PeriodicHornDecision](LeanTrominoes/SAT/Horn/PeriodicHornDecision.lean) |
| Periodic Horn and dual Horn SAT, linear charged-operation bound | `Horn.Indexed.certified`, `Horn.PeriodicIndexed.certified` | [HornIndexedTime](LeanTrominoes/SAT/Horn/HornIndexedTime.lean), [PeriodicHornLinearTime](LeanTrominoes/SAT/Horn/PeriodicHornLinearTime.lean) |
| Theorem 4.1, local periodic 2SAT in every fixed dimension | `PeriodicTwoSAT.local_certified`, `solveLocal_correct`, `solveLocal_polynomial` | [PeriodicTwoSATLocalTime](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATLocalTime.lean), [PeriodicTwoSATPolynomialTime](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATPolynomialTime.lean) |
| Lemma 5.1, arbitrary periodic subspace tiling and completion membership | `PeriodicSubspaceTiling.lemma51`, `lattice_tileable_coRE`, `lattice_completable_coRE`, `Strip.tiling_inPSPACE`, `Strip.completion_inPSPACE` | [Lemma51](LeanTrominoes/Tiling/Periodic/Lemma51.lean) |
| Lemma 4.3, bounded-diameter augmenting paths in general periodic graphs | `PeriodicLatticeGraph.bounded_augmenting_path`, `perfect_or_bounded_augmenting` | [PeriodicGeneralAugmentingPath](LeanTrominoes/Graphs/Matching/PeriodicGeneralAugmentingPath.lean) |
| Lemma 4.4, 2-periodic bipartition of a connected bipartite periodic graph | `PeriodicLatticeGraph.bipartition_two_periodic` | [PeriodicBipartitionDoubling](LeanTrominoes/Graphs/Matching/PeriodicBipartitionDoubling.lean) |
| Lemma 4.5, a protovertex-simple augmenting path shorter than the quotient vertex count | `PeriodicBipartite.perfect_or_short_augmenting` | [PeriodicShortAugmentingProperties](LeanTrominoes/Graphs/Matching/PeriodicShortAugmentingProperties.lean) |
| Theorem 4.6, period-one bipartite perfect matching in every dimension | `PeriodicBipartite.exists_period_one`, `perfect_iff_quotient` | [PeriodicMatchingPeriodOne](LeanTrominoes/Graphs/Matching/PeriodicMatchingPeriodOne.lean) |
| Theorem 4.7, bipartite perfect matching decision and construction with an `O(E√V)` charged-operation bound | `PeriodicBipartite.matchingSolver_certified`, `matchingSolver_edge_sqrt_bound` | [PeriodicMatchingSolver](LeanTrominoes/Graphs/Matching/PeriodicMatchingSolver.lean) |
| Finite 3CNF tableaux for bounded-time TM2 acceptance, with symbolic initial configurations and polynomial formula-size bounds | `FiniteMachineTrace.paddedFormula_iff_evals`, `symbolicFormula_iff_evals`, `symbolicFormula_length_le`, `symbolicFormula_width` | [FiniteMachineAcceptanceCNF](LeanTrominoes/Complexity/FiniteMachineAcceptanceCNF.lean), [FiniteSymbolicMachineCNF](LeanTrominoes/Complexity/FiniteSymbolicMachineCNF.lean) |
| Cook–Levin: every verifier-defined NP language reduces by an actual polynomial-time machine to ordinary finite 3CNF SAT | `FiniteCNF.threeSatisfiable_npHard`, `satisfiable_npHard`; `Complexity.VerifierInPolyTime.finiteCNFReduction`; `FiniteNPRequestEmitter.computableInPolyTime` | [FiniteSATNPHard](LeanTrominoes/SAT/CNF/FiniteSATNPHard.lean), [FiniteNPRequestEmitter](LeanTrominoes/Complexity/FiniteNPRequestEmitter.lean), [FiniteNPSeparatedRequest](LeanTrominoes/Complexity/FiniteNPSeparatedRequest.lean) |
| Complete polynomial-time verifier initialization and accepting self-loop emission, matching the existing finite tableau programs | `FiniteNPInitializationEmitter.computableInPolyTime`, `initialProgram_encode`; `FiniteNPCertificateStackEmitter.stackProgram_eq`; `FiniteNPPaddedProgramEmitter.computableInPolyTime`, `program_eq` | [FiniteNPInitializationEmitter](LeanTrominoes/Complexity/FiniteNPInitializationEmitter.lean), [FiniteNPCertificateStackEmitterCorrectness](LeanTrominoes/Complexity/FiniteNPCertificateStackEmitterCorrectness.lean), [FiniteNPPaddedProgramEmitter](LeanTrominoes/Complexity/FiniteNPPaddedProgramEmitter.lean) |
| Native finite-verifier machine programs and absolute-time serialization, with polynomial-time squares, products, pairing, and request-header generation | `FiniteNPMachineProgramEmitter.wellFormedComputableInPolyTime`, `stepComputableInPolyTime`, `acceptingComputableInPolyTime`; `FiniteCNF.ProgramColumns.repeated`; `FiniteNPVariableNameCompiler.sourceComputableInPolyTime`, `freshComputableInPolyTime` | [FiniteNPMachineProgramEmitter](LeanTrominoes/Complexity/FiniteNPMachineProgramEmitter.lean), [FiniteProgramColumns](LeanTrominoes/Tiling/Tromino/Finite/FiniteProgramColumns.lean), [FiniteNPVariableNameCompiler](LeanTrominoes/Complexity/FiniteNPVariableNameCompiler.lean) |
| Native finite-CNF compiler backend, with quadratic machine time and correct bounded requests for every NP verifier | `FiniteCNFCompiler.finiteAlphabetComputableInPolyTime`, `Request.correct`, `compiler_time`; `Complexity.VerifierInPolyTime.nativeRequest_correct`, `nativeRequest_encode_length_le`, `nativeRequest_backend_time_le` | [FiniteCNFCompiler](LeanTrominoes/SAT/CNF/FiniteCNFCompiler.lean), [FiniteNPCompilerRequest](LeanTrominoes/Complexity/FiniteNPCompilerRequest.lean) |
| Polynomial-time preparation of finite-compiler source words, with exact certificate, time, space, and variable counters | `FiniteNPCompilerPreparation.computableInPolyTime`, `prepared_eq`, `counterCount_prepared`, `sourceSymbols_prepared` | [FiniteNPCompilerPreparation](LeanTrominoes/Complexity/FiniteNPCompilerPreparation.lean) |
| Flat finite-tableau encoding, with source and auxiliary variable ranges and a polynomial binary-output bound | `Complexity.VerifierInPolyTime.tableau_variable_bounds`, `tableau_encode_length_le` | [FiniteNPTableauEncoding](LeanTrominoes/Complexity/FiniteNPTableauEncoding.lean), [FiniteCNFFlatEncoding](LeanTrominoes/SAT/CNF/FiniteCNFFlatEncoding.lean) |
| Every verifier-defined NP language has an equivalent finite width-three tableau with a polynomial clause bound | `Complexity.VerifierInPolyTime.tableau_correct`, `tableau_width`, `tableau_length_le` | [FiniteNPTableau](LeanTrominoes/Complexity/FiniteNPTableau.lean) |
| Finite 3CNF for existence of an accepted bounded binary certificate, with polynomial formula-size bounds | `FiniteCertificate.formula_correct`, `formula_length_le`, `formula_width` | [FiniteCertificateCNF](LeanTrominoes/Complexity/FiniteCertificateCNF.lean) |
| Explicit binary certificates for both finite-region tiling and finite-preplacement completion: 24 bits per listed region cell or bounding-box cell | `Tromino.FiniteRegion.tileable_iff_bounded_certificate`; `Tromino.FiniteWitness.completion_iff_box_certificate`, `completion_iff_bounded_certificate` | [FiniteTrominoRegionCertificate](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoRegionCertificate.lean), [FiniteTrominoCompletionCertificate](LeanTrominoes/Tiling/Completion/FiniteTrominoCompletionCertificate.lean) |
| Polynomial-time exact-cover verifier backend for both trominoes, with geometric certificate correctness and serialized candidate-table bounds | `FiniteExactCoverVerifier.finiteAlphabetComputableInPolyTime`; `Tromino.FiniteVerifier.check_correct`, `tileable_iff_certificate`, `completion_iff_certificate`, `nativeRequest_encode_length_le` | [FiniteExactCoverVerifier](LeanTrominoes/SAT/ExactOne/FiniteExactCoverVerifier.lean), [FiniteTrominoVerifierBackend](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoVerifierBackend.lean), [FiniteTrominoVerifierSize](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoVerifierSize.lean) |
| Theorem 5.12, finite-preplacement completion decidability for both trominoes | `Tromino.FiniteWitness.decideCompletion_correct`, `completion_iff_bounded_witness` | [FiniteCompletionDecision](LeanTrominoes/Tiling/Completion/FiniteCompletionDecision.lean) |
| Theorem 5.13 and Corollary 5.14, doubled-period domino tilings and completions | `Domino.theorem513`, `corollary514` | [DominoTheorems](LeanTrominoes/Tiling/Domino/DominoTheorems.lean) |
| Corollary 5.15, executable periodic domino decision with a fixed-dimensional polynomial arithmetic-operation budget | `Domino.corollary515` | [PeriodicDominoSolverCost](LeanTrominoes/Tiling/Domino/PeriodicDominoSolverCost.lean) |
| Theorem 3.1, Wang tiling co-r.e.-completeness | `LeanWang.domino_problem_coRE_complete` | Dependency module `LeanWang.Final` |

`import LeanTrominoes` exposes these main results. Import
`LeanTrominoes.Tiling.Tromino.Theorem52` when only the target statements are needed, or an
individual construction module for its implementation API.

The full proof instantiates the [appender closure](LeanTrominoes/Tiling/Tromino/Strip/Theorem52DirectSparseClosure.lean)
with the concrete [vertex](LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Vertex/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean)
and [route](LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Route/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean)
compilers. No compiler witness remains assumed.

## Definitions

| Objects | Module |
| --- | --- |
| Integer-grid cells, polyominoes, square-grid symmetries, I and L trominoes | [Basic](LeanTrominoes/Tiling/Basic/Basic.lean) |
| Placements and exact tilings | [Tiling](LeanTrominoes/Tiling/Basic/Tiling.lean) |
| Partial tromino tilings and completion | [TrominoCompletion](LeanTrominoes/Tiling/Completion/TrominoCompletion.lean) |
| Periodic plane and strip prefills | [PeriodicTrominoCompletion](LeanTrominoes/Tiling/Completion/PeriodicTrominoCompletion.lean) |
| Equivalent tilings by geometric three-cell footprints | [FootprintTiling](LeanTrominoes/Tiling/Basic/FootprintTiling.lean) |
| `PeriodicRegion`, `PeriodicStrip`, and their tilability predicates | [Periodic](LeanTrominoes/Tiling/Periodic/Periodic.lean) |
| Target strip encoding and decoder | [PeriodicStripFlatEncoding](LeanTrominoes/Tiling/Periodic/PeriodicStripFlatEncoding.lean) |
| Finite-alphabet polynomial-space deciders, polynomial-time reductions, PSPACE completeness | [Complexity](LeanTrominoes/Complexity/Complexity.lean) |
| Periodic CNF formulas and satisfiability | [PeriodicCNF](LeanTrominoes/SAT/CNF/PeriodicCNF.lean) |
| Finite presentations of periodic graphs | [PeriodicGraph](LeanTrominoes/Graphs/Core/PeriodicGraph.lean) |
| Scaled integer-grid periodic drawings | [PeriodicGridDrawing](LeanTrominoes/Graphs/Drawings/Grid/PeriodicGridDrawing.lean) |

A plane input has a finite motif and two full-rank period vectors. A strip
input has a finite motif in a bounded-height strip and one positive
horizontal period. Malformed presentations are no-instances. Complexity
claims use the explicit encodings named in their statements.

PSPACE hardness uses polynomial-time many-one reductions from every encoded
polynomial-space language. Both deciders and reduction machines require finite
alphabets on every stack. The [finite-alphabet certificate](LeanTrominoes/Complexity/FiniteAlphabetPolyTime.lean)
strengthens Mathlib’s machine interface; a [verified alphabet restriction](LeanTrominoes/Computation/TM2/TM2FiniteAlphabetRestriction.lean)
converts existing certificates without changing their encodings or running time.
Finite control ensures that each program can write only finitely many symbols.

[Local planar 1D 3DM with colored degree 2 or 3 is PSPACE-complete](LeanTrominoes/ThreeDM/Line/PeriodicThreeDMPlanarLineCompleteness.lean)
under the [complete native binary encoding](LeanTrominoes/ThreeDM/Encoding/PeriodicThreeDMFlatEncoding.lean)
of the instance and supplied drawing. The reduction emits every count, reference,
vertex, segment, and route point. The upper bound combines the matching solver
with a [linear-space drawing verifier](LeanTrominoes/ThreeDM/PeriodicThreeDMDrawingVerifier.lean)
that checks incidence endpoints, continuous planarity, halo bounds, and endpoint-only
route-point contacts. [The instance-only matching problem is also PSPACE-complete](LeanTrominoes/ThreeDM/Line/PeriodicThreeDMLineCompleteness.lean).
[Normalized 1D trichromatic orientation is PSPACE-complete](LeanTrominoes/Graphs/Orientation/NormalizedOrientationLineMembership.lean)
under a [lossless binary encoding](LeanTrominoes/Graphs/Orientation/NormalizedOrientationFlatEncoding.lean)
of the full colored cell table and periods. The endpoint requires separated
vertices and a blank vertical boundary. The upper bound checks these constraints
and compiles a bounded reconstruction to the existing unary strip-completion decider.
[Bounded binary preparation](LeanTrominoes/Graphs/Orientation/NormalizedOrientationBoundedPreparation.lean)
recovers valid orientation fields in polynomial time without expanding oversized
malformed dimensions. [The complete compiler](LeanTrominoes/Graphs/Orientation/NormalizedOrientationCompletionCompiler.lean)
preserves every well-formed drawing. [Valid local 3DM fields also have polynomial numeric bounds](LeanTrominoes/ThreeDM/Encoding/PeriodicThreeDMNativeFieldBounds.lean).

Periodic Horn and dual Horn SAT reduce to finite Horn SAT by identifying all
translates of each variable. The [period-one theorem](LeanTrominoes/SAT/Horn/PeriodicHornCore.lean)
works over any additive group of offsets, including integer lattices in every
dimension, without a locality bound. The [solver](LeanTrominoes/SAT/Horn/HornSolver.lean)
performs at most one forward-chaining round per distinct conclusion variable,
then checks negative clauses. It constructs the least Horn model; complementing
it gives a dual Horn model. The [existing CNF API](LeanTrominoes/SAT/Horn/PeriodicHornDecision.lean)
also checks the Horn restriction. This API uses the repeated-scan solver.

The [indexed worklist solver](LeanTrominoes/SAT/Horn/HornIndexedSolver.lean) has a
[proved linear operation bound](LeanTrominoes/SAT/Horn/PeriodicHornLinearTime.lean):
at most `72(n + m + L + 2)` charged operations for periodic Horn or dual Horn
SAT, where `n` is the explicit number of variable slots, `m` the rule count,
and `L` the number of premise occurrences (including duplicates). The bound
includes quotient preparation, occurrence indexing, initialization, and
propagation. The [cost model](LeanTrominoes/SAT/Horn/HornWorklistRAM.lean) charges indexed accesses at unit cost. Counter and queue magnitudes are bounded
above, but an instruction-level bounded-word implementation remains to be proved. Inputs
already use `Fin n` variable indices; renaming arbitrary variable names is
not included. [Examples](LeanTrominoes/SAT/Horn/HornWorklistExamples.lean) check duplicate
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
| Corollary 5.8 | Two connected polycubes: full 3D and every fixed slab height > 1 proved |
| Corollary 5.9 | Translation-only co-r.e. completeness in full 3D and every fixed slab height > 1 proved |
| Theorem 5.10, Corollary 5.11 | L- and I-tromino plane co-r.e. completeness, strip PSPACE completeness (unary encoding), and the aperiodic-completion corollary proved |
| Theorems 2.1–2.2, Lemma 2.3 | Theorem 2.1 is proved for arbitrary degrees, loops, and isolated vertices: simple real routes, locality, orthocrossing, vertex avoidance, grid size ≤16(|V|+|E|+1), and orthogonality at degree four. Lemma 2.3 preserves rational vertex positions, planarity, simplicity, and locality, multiplies the grid by 32, and normalizes degree-three incidence directions. Theorem 2.2 is proved with the current manuscript’s O(M³) bound: `PeriodicGridDrawing.polygonal_cubic_refinement` gives a planar local orthogonal drawing of any planar local polygonal drawing of degree at most four, with grid size ≤84480M³. It includes loops and periodic seam bends and scales original vertices exactly by (16M+32)(160M+1600). The straight-input theorem retains its sharper constant ≤3300M³ |
| Theorems 3.5–3.7 | Complete with supplied, verified planar drawings in 1D and 2D. Local planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3 have the polynomial grid restriction (in fact linear in 2D). Local planar 3DM has colored degree 2 or 3. Native encodings have PSPACE completeness in 1D and co-r.e. completeness in 2D |
| Theorem 3.8 | Normalized trichromatic orientation is co-r.e. complete in 2D and PSPACE complete in 1D under its native binary encoding. Finite normalized planar drawings are NP-complete under a sparse unary encoding. Ordinary local periodic colored graph orientation is co-r.e. complete, with hard outputs admitting verified orthogonal planar presentations. Ordinary local 1D colored graph orientation is PSPACE-complete under a lossless native binary encoding of vertex kinds and edge records. The decider verifies endpoints, offsets, degree three, and colors, then searches three-column states with one bit per edge and column. The polynomial-time reduction compiles the actual contracted graph, including dense vertex names and signed offsets. Ordinary finite colored graph orientation is NP-complete under the same native binary encoding. An actual polynomial-time verifier checks endpoint bounds, zero offsets, degree and color constraints, and inward counts, with one witness bit per edge. Oversized binary fields are rejected before unary expansion; loops contribute two incidences. NP completeness also holds for the lossless unary graph encoding |
| Theorem 4.2 | Horn and dual Horn SAT: period-one models in every dimension, finite-quotient equivalence, and executable solvers proved; linear operation-counter bound and original-input word-RAM theorem proved (`120(S+1)` instructions) |
| Theorem 4.1 | Executable local periodic 2SAT decision in every fixed dimension, with a polynomial operation-counter bound including normalization and finite-cover construction; complete original-input polynomial-time word-RAM theorem proved |
| Lemma 4.3 | In every dimension, every free vertex of a period-one matching in a local periodic graph with a perfect matching starts a simple augmenting path of diameter at most `2*d*|E|`; no bipartiteness assumption |
| Lemma 4.4 | Every proper bipartition of a connected periodic graph is invariant under twice every lattice translation, in every dimension |
| Lemma 4.5 | Any imperfect period-one partial matching of a bipartite periodic graph with a perfect matching has an augmenting path with no repeated protovertex and edge length strictly less than the quotient vertex count |
| Theorem 4.6 | Every perfect matching in a bipartite periodic graph implies a period-one perfect matching; equivalence with finite quotient matching proved in every dimension, without a locality restriction |
| Theorem 4.7 | Executable decision and period-one matching construction in every dimension, with a `O(E√V)` operation-counter bound for indexed inputs; separate original-input dense word-RAM program proved with a quartic instruction bound |
| Lemma 5.1 | Arbitrary finite-footprint periodic subspace tiling and completion are co-r.e. in every dimension. Both strip problems are in PSPACE for each fixed polynomial bounding box under native binary encoding; the palette, target, and prefill are all input |
| Theorem 5.12 | Decidability and NP-completeness proved for both trominoes, with the canonical bounding box listed in the encoding: `Tromino.FiniteCoordinateColumns.completion_npComplete` |
| Theorem 5.13 | Every tileable periodic domino region has a tiling invariant under twice each original generator, in every ambient dimension and periodic rank |
| Corollary 5.14 | Every completable periodic domino prefill has a completion with those doubled periods |
| Corollary 5.15 | Executable decision from cell representatives and arbitrary nonsingular integer period matrices; quadratic arithmetic-operation budget in the number of representatives for fixed dimension; complete original-binary-input word-RAM theorem proved with a conservative degree-16 instruction bound |
| Corollary 5.4 | Proved for both trominoes under the explicit unary coordinate encoding: `Tromino.FiniteCoordinateColumns.region_npComplete` |

The [finite-seed polyomino search](LeanTrominoes/Tiling/Polyomino/FinitePolyominoCompletionSearch.lean)
keeps every prescribed placement at every finite stage, including placements
outside the inspected box. Its compactness theorem characterizes plane
completion exactly by success at all stages. The
[primitive-recursive verifier](LeanTrominoes/Tiling/Polyomino/FinitePolyominoCompletionCoRE.lean)
proves co-r.e. membership when both shapes are fixed and only the seed varies.
[Boundary examples](LeanTrominoes/Tiling/Polyomino/FinitePolyominoCompletionExamples.lean)
check overlapping seeds outside the initial box and reject extra proof axioms.

[Cook–Levin](LeanTrominoes/SAT/CNF/FiniteSATNPHard.lean) is proved for the
[verifier-based NP definition](LeanTrominoes/Complexity/NP.lean): every NP language reduces
to ordinary finite 3CNF SAT under the native binary formula encoding. The
[complete request emitter](LeanTrominoes/Complexity/FiniteNPRequestEmitter.lean) generates
initialization with a bounded unknown certificate, acceptance, well-formedness,
and padded transitions, with absolute variable names and exact clause counts.
It composes with the checked quadratic-time
[finite-CNF backend](LeanTrominoes/SAT/CNF/FiniteCNFCompiler.lean). The reduction uses
actual finite-alphabet polynomial-time Turing machines throughout.
[Finite-region certificates](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoRegionCertificate.lean)
use 24 bits per listed cell. For
[finite-preplacement completion](LeanTrominoes/Tiling/Completion/FiniteTrominoCompletionCertificate.lean),
24 bits per bounding-box cell suffice for either tromino, including tiles
protruding outside the box. The
[exact-cover verifier backend](LeanTrominoes/SAT/ExactOne/FiniteExactCoverVerifier.lean) is
an actual finite-alphabet polynomial-time machine. Its
[geometric correctness](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoVerifierBackend.lean) and
[serialized candidate-table bound](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoVerifierSize.lean)
are proved. The [native coordinate verifier](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoNativeVerifier.lean)
now generates the candidate table itself, including signed coordinate arithmetic,
canonical footprint names, and stable deduplication. This proves
[finite-region membership in NP](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoRegionInNP.lean)
under the explicit unary coordinate encoding, and
[finite-preplacement completion membership in NP](LeanTrominoes/Tiling/Completion/FiniteTrominoCompletionInNP.lean)
when the canonical bounding box is explicitly listed in that encoding.
These statements charge for unary coordinate magnitudes and the listed box;
they do not establish membership under an unpadded binary-coordinate encoding.
[Finite-region NP-completeness](LeanTrominoes/Tiling/Tromino/Finite/FiniteTrominoRegionNPComplete.lean)
is proved for both trominoes under the original unary coordinate encoding.
[Finite-preplacement plane completion is also NP-complete](LeanTrominoes/Tiling/Completion/FiniteTrominoCompletionNPComplete.lean)
for both trominoes when the canonical bounding box is listed in the encoding.

The [finite substitution bridge](LeanTrominoes/Tiling/Tromino/Finite/FiniteGadgetSubstitution.lean)
now proves orientation equivalent to finite-motif tileability for both trominoes,
when the normalized drawing has a blank final row and column. A three-cell gap
separates its periodic copies, so this uses the existing substitution theorem
without assuming a periodic tiling. The
[finite region emitter](LeanTrominoes/Tiling/Tromino/Finite/FiniteGadgetRegionCompiler.lean) expands
compiled sparse drawing records into the original unary coordinate encoding
with verified polynomial-time machines. The finite SAT source-to-drawing
correctness theorem is now connected to this endpoint.

[Finite occurrence-three SAT](LeanTrominoes/SAT/ThreeSAT/FiniteThreeSATThreeNPHard.lean)
is now NP-hard under the native binary formula encoding, with clauses of
width at most three, compact natural variable names, and no empty clauses.
The [compiler](LeanTrominoes/Complexity/FiniteNPThreeOccurrenceCompiler.lean) composes
the finite Cook–Levin emitter with verified occurrence-splitting machines.
For its zero-offset graph, the
[route bounds](LeanTrominoes/SAT/Planar/FiniteOrthocrossingBounds.lean) place every segment
inside one fundamental square; canonical crossings use only zero translates.
The [retained planarization](LeanTrominoes/SAT/Planar/FiniteRetainedPlanarSAT.lean)
now preserves ordinary finite SAT, including its canonical gauge and clause
deduplication. [Zero offsets](LeanTrominoes/ThreeDM/FiniteRetainedThreeDMOffsets.lean)
persist through fixed-eight splitting, Figure 9, unit elimination, the final
canonical gauge, routed polarity normalization, and planar 3DM assembly.
[Finite normalization](LeanTrominoes/ThreeDM/FiniteThreeDMNormalization.lean) pads the
zero-offset drawing inside one square, preserves complete route separation
and simplicity, and moves the blank seams to the final boundary. The
[finite retained region](LeanTrominoes/Tiling/Tromino/Finite/FiniteRetainedTrominoRegion.lean) is
tileable exactly when the finite source formula is satisfiable, for either
tromino. The [shared program-source interface](LeanTrominoes/SAT/CNF/Compiler/PeriodicCNFProgramSource.lean)
accepts both the existing PSPACE source and the finite NP verifier source. The
[finite source compiler](LeanTrominoes/Tiling/Tromino/Finite/FiniteProgramTrominoRegionCompiler.lean)
now emits the padded, seam-shifted sparse drawing and its finite gadget region
in the original encoding, with no source-emitter hypothesis.

The [finite completion construction](LeanTrominoes/Tiling/Completion/Finite/FiniteDrawingCompletion.lean)
uses a finite collar of preplaced brick motifs. Local barrier and portal
ownership proofs extract the required circuit behavior from any plane
completion. The [completion compiler](LeanTrominoes/Tiling/Tromino/Finite/FiniteProgramCompletionCompiler.lean)
evaluates signed-coordinate palette queries, emits the prescribed placements,
and computes their exact canonical radius before listing the bounding box.
The final finite NP-completeness theorems use only `propext`, `Classical.choice`,
and `Quot.sound`. All finite certificates are checked by Lean's kernel; the
[axiom regression checks](LeanTrominoes/Verification/AxiomAudit.lean) reject additional assumptions.


The [domino results](LeanTrominoes/Tiling/Domino/DominoTheorems.lean) use exact covers by
face-adjacent two-cell footprints. The proofs allow disconnected regions and
arbitrary initial tilings. Completion keeps every prefilled domino fixed.
The decision procedure derives adjacency using an integer-matrix coordinate
decoder, doubles the period lattice to preserve checkerboard colors, and runs
the finite matching solver. Its budget includes coordinate searches and cover
construction. Dimension-dependent constants include `2^d` and determinant
preparation. The quadratic result bounds charged arithmetic operations; arbitrary
integer input entries require the magnitude and multiword considerations above. [Kernel-evaluated examples](LeanTrominoes/Tiling/Domino/PeriodicDominoExamples.lean)
cover holes, skew periods, and empty and zero-dimensional regions.

The [general subspace membership proof](LeanTrominoes/Tiling/Periodic/Lemma51.lean) uses
finite footprint records in fundamental-domain coordinates. Records include
all allowed prototile orientations and representative anchors. The
[geometry bridge](LeanTrominoes/Tiling/Periodic/PeriodicSubspaceGeometry.lean) proves their
containment and exact-cover semantics, including transport to physical cells
through a fundamental-domain chart. Completion prescribes whole placement
orbits; the completing tiling itself may be nonperiodic.

The [strip decider](LeanTrominoes/Tiling/Periodic/PeriodicSubspaceStripMembership.lean) stores
one bit per record per column in a window of `2*B+1` columns and runs the
verified Savitch cycle search. Its binary encoding includes the target,
records, bound, and prescribed orbit list. For any fixed polynomial `p`,
the input promise is `B ≤ p(input length)`; every reachable machine
configuration has polynomial space. No fixed palette or connectedness
assumption is used. The [regressions](LeanTrominoes/Tiling/Periodic/PeriodicSubspaceExamples.lean)
cover empty instances, duplicates, sparse labels, signed offsets, overlap,
and invalid prefills.

The [periodic 2SAT solver](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATLocalTime.lean)
accepts empty clauses and duplicated literals for units. Locality bounds
coordinatewise offset differences, which includes the paper's Manhattan
locality. Each clause is first anchored at its first literal, preserving all
assignments even when the common offset is large. The solver uses an explicit
finite cover with base-`M` coordinate indices and the verified Horn worklist
solver for opposite-literal reachability tests. The
[cover theorem](LeanTrominoes/Graphs/Reachability/PeriodicPowerTwoCover.lean) proves that a uniformly
chosen power-of-two period preserves contradictions. For every fixed `d`, the
complete operation bound has degree `3(d²+d+1)` in `n + clauses + 1`, where `n`
is the number of explicit variable slots. Normalization produces two-bit offset
differences, and cover indices have polynomial magnitude. The [instruction-level word-RAM theorem](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATWordRAMPolynomialTime.lean)
now proves polynomial time for the whole original-input program, including
cover construction and reachability calls. The
[regressions](LeanTrominoes/SAT/TwoSAT/PeriodicTwoSATExamples.lean) include kernel-evaluated
units, inconsistent units, empty inputs, and dimension zero, as well as a
satisfiable alternation formula with no period-one assignment.

The [bipartite matching solver](LeanTrominoes/Graphs/Matching/PeriodicMatchingSolver.lean)
uses breadth-first layers and disjoint blocking paths. Its bound includes
quotient indexing, vertex-array initialization, and selection of a finite
protoedge table describing the period-one matching. Here `E` counts edge
records and `V` counts vertex slots. The uniform bound is
`1000(E+1)(⌊√V⌋+1)`, with `4000E⌊√V⌋` for nonempty edge tables.
The counter charges indices and scalar operations at unit cost; coordinate vectors
remain in the input store. Search labels are bounded by the vertex count. A [separate dense matching program](LeanTrominoes/Graphs/Matching/BipartiteMatchingDenseWordRAMPolynomialTime.lean)
has a checked concrete layout and quartic word-RAM instruction bound from
original endpoint records. The `O(E√V)` bound remains a result about the
blocking-path solver's operation counter.

The local 1D CNF endpoint is now **PSPACE-complete** under the native flat
encoding. The [machine certificate](LeanTrominoes/SAT/CNF/PeriodicCNFPolySpaceMembership.lean)
combines the [linear-space preprocessor](LeanTrominoes/SAT/CNF/PeriodicCNFFlatFieldCountSpace.lean),
[compiled transition predicate](LeanTrominoes/SAT/CNF/PeriodicCNFFieldTransition.lean), and
[polynomial-space cycle search](LeanTrominoes/SAT/CNF/PeriodicCNFFieldEvaluator.lean).
The [field-indexed window model](LeanTrominoes/SAT/CNF/PeriodicCNFFieldWindow.lean)
uses three bits per flat field and supports arbitrarily large atom names and
common clause offsets. [Local 1D 3SAT is also PSPACE-complete](LeanTrominoes/SAT/CNF/PeriodicCNFFieldWidth.lean):
the hardness compiler already emits width-three clauses.
[Local 1D 3SAT-3 is PSPACE-complete](LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreePolySpaceCompleteness.lean).

The [four planar 1D SAT reductions](LeanTrominoes/SAT/Planar/PeriodicPlanarSATLineReduction.lean)
now preserve one-dimensionality, locality, occurrence bounds, and the intrinsic
linear drawing-grid bounds, including on malformed source inputs.
[Forgetting the drawings](LeanTrominoes/SAT/ExactOne/PeriodicExactOneLineReduction.lean) also
gives total reductions to nonplanar exact-one SAT and its occurrence-three variant.
The original planar reductions are primitive recursive. Separate native
polynomial-time reductions now prove all four planar PSPACE-hardness endpoints.

[All four planar 1D SAT variants are in PSPACE](LeanTrominoes/SAT/Planar/PeriodicPlanarSATLinePolySpaceMembership.lean)
under the [lossless formula-and-drawing encoding](LeanTrominoes/SAT/Planar/PeriodicPlanarSATFlatEncoding.lean).
The [complete verifier](LeanTrominoes/SAT/Planar/PeriodicPlanarSATFullVerification.lean)
checks satisfiability, locality, clause width, the applicable occurrence bound,
the grid bound, planarity, incidence counts, vertex compatibility, and route endpoints.
The [finite planarity check](LeanTrominoes/Graphs/Drawings/Grid/PeriodicDrawingFiniteCheck.lean)
supports arbitrary stored coordinates, without a bounding-box promise.
The [route query's correctness proof](LeanTrominoes/SAT/Planar/PeriodicPlanarSATRouteSemantics.lean)
connects its [linear-space machine](LeanTrominoes/SAT/Planar/PeriodicPlanarSATRouteMachine.lean)
to the actual incidence graph, including repeated literals and empty or singleton routes.
Distinct-variable indices follow `List.dedup`'s last-occurrence order.
[Local 1D planar 1-in-3SAT and 1-in-3SAT-3 are PSPACE-complete](LeanTrominoes/SAT/Planar/PeriodicPlanarExactOneLinePolySpaceCompleteness.lean)
under that encoding. The [native binary encoder](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativePlanarEncoding.lean)
compiles the entire routed formula and supplied drawing: numeric atom names,
signed offsets, vertices, routes, indexed segments, and finite-check radius.
[Semantic correctness and planarity](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativePlanarSemantics.lean),
[locality and the occurrence-three bound](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativePlanarLocality.lean),
and the [original fixed grid bound](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativePlanarGridBound.lean)
connect this encoder to both target languages. The reduction uses the
anchor-normalized, numerically renamed routed exact-one construction,
which differs from the earlier primitive-recursive endpoint.

[Local 1D planar 3SAT and 3SAT-3 are also PSPACE-complete](LeanTrominoes/SAT/Planar/PeriodicPlanarOrdinaryLinePolySpaceCompleteness.lean).
Their [native binary encoder](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativeOrdinaryEncoding.lean)
compiles the entire ordinary formula and supplied drawing.
[Semantic correctness](LeanTrominoes/Tiling/Tromino/Strip/Native/PeriodicCNFStripNativeOrdinaryInput.lean)
preserves one-dimensionality, locality, the three-occurrence bound, planarity,
and the original fixed linear grid bound after anchor normalization and numeric renaming.

[Local 1D 1-in-3SAT and 1-in-3SAT-3 are PSPACE-complete](LeanTrominoes/SAT/ExactOne/PeriodicExactOnePolySpaceCompleteness.lean)
under the native flat encoding. The upper bounds use a direct exact-one window
predicate and compiled Savitch search. The
[polynomial-time reduction](LeanTrominoes/SAT/ExactOne/PeriodicOneInThreePolyTimeCompiler.lean)
compiles both literal metadata and compact numeric atom names, including padding
for short clauses. Its correctness preserves locality and the three-occurrence
bound. The [executable decisions](LeanTrominoes/SAT/ExactOne/PeriodicExactOneCNFLocality.lean)
and [linear encoding-size bound](LeanTrominoes/SAT/ExactOne/PeriodicExactOneCNFFlatSize.lean)
are also proved.

The 3SAT-3 [polynomial-time compiler](LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreePolyTimeCompiler.lean)
combines occurrence-split atom numbers with literal profiles and emits the native flat formula encoding.
[Local planar 3SAT and 3SAT-3 are co-r.e. complete](LeanTrominoes/SAT/Planar/PeriodicPlanarLocalThreeOccurrenceCompleteness.lean)
with supplied drawings. The construction has
[a linear fundamental-grid side bound](LeanTrominoes/SAT/Planar/PeriodicPlanarThreeOccurrenceGridSize.lean)
in the source clause-plus-literal count.
[Local planar 1-in-3SAT and 1-in-3SAT-3 are also co-r.e. complete](LeanTrominoes/SAT/Planar/PeriodicPlanarLocalExactOneCompleteness.lean),
with [the corresponding linear grid bound](LeanTrominoes/SAT/Planar/PeriodicPlanarExactOneGridSize.lean).
[All four remain co-r.e. complete with an intrinsic linear grid-size restriction](LeanTrominoes/SAT/Planar/PeriodicPlanarBoundedLocalCompleteness.lean):
the supplied fundamental-square side length is bounded by a fixed constant
times (the output formula’s clause-plus-literal count + 1).
The ordinary endpoint uses a
[finite certificate for vertex orbits](LeanTrominoes/Graphs/Core/PeriodicGraphOrbitCertificate.lean):
canonical representatives may lie outside the fundamental square, but distinct
vertices cannot coincide under any whole-period translation.

For the plane parts of Theorems 3.2–3.4, the existing Wang reductions already
proved hardness. The shared [finite-obstruction proof](LeanTrominoes/SAT/CNF/PeriodicCNFFiniteSearch.lean)
and [effective finite search](LeanTrominoes/SAT/CNF/PeriodicCNFCoRE.lean) now supply
co-r.e. membership for arbitrary periodic CNF presentations.
[Locality, width, and occurrence checks](LeanTrominoes/SAT/CNF/PeriodicCNFSyntaxComputability.lean)
allow invalid restricted presentations to be rejected. The membership and completeness theorems
use only `propext`, `Classical.choice`, and `Quot.sound`.

For tromino completion, extending a valid prefill is proved
equivalent to tiling the uncovered region, with a
[finite-obstruction characterization](LeanTrominoes/Tiling/Completion/TrominoCompletionFiniteSearch.lean)
for plane and strip inputs. The paper's ASCII layouts in
[data/completion](data/completion) now have kernel-checked
[major gadget relations](LeanTrominoes/Tiling/Completion/CompletionMajorRelations.lean) and
[complete minor boundary profiles](LeanTrominoes/Tiling/Completion/CompletionMinorBoundaryRelations.lean).
The [L-brick palette](LeanTrominoes/Tiling/Completion/CompletionLBricks.lean) has a verified common
[region](LeanTrominoes/Tiling/Completion/CompletionLBrickRegions.lean),
[Boolean network](LeanTrominoes/Tiling/Completion/CompletionLBrickLogic.lean), and
[local barrier checks](LeanTrominoes/Tiling/Completion/CompletionLAtomBarriers.lean). These yield
a [global assembly criterion](LeanTrominoes/Tiling/Completion/CompletionLAssembly.lean): a plane
completion exists exactly when realizable local gadget states partition the
plane. Canonical states from a completion satisfy
[connector consistency](LeanTrominoes/Tiling/Completion/CompletionLConnectorConsistency.lean).
The [minor-state lemmas](LeanTrominoes/Tiling/Completion/CompletionLMinorStates.lean) force and
propagate Boolean connectors. The full [brick-network equivalence](LeanTrominoes/Tiling/Completion/CompletionLBrickEquivalence.lean)
and [finite periodic prefill compiler](LeanTrominoes/Tiling/Completion/CompletionLPeriodicCompiler.lean)
are proved. Nine [orientation-cell circuits](LeanTrominoes/Tiling/Completion/CompletionCircuitTruthTables.lean)
have checked truth tables and wiring; their [infinite-grid composition](LeanTrominoes/Tiling/Completion/CompletionCircuitReduction.lean)
is proved. The [source interface and finite compiler](LeanTrominoes/Tiling/Completion/CompletionOrientationCompiler.lean)
and its [primitive-recursion proof](LeanTrominoes/Tiling/Completion/CompletionOrientationComputability.lean)
now give unconditional [plane co-r.e. hardness for L-tromino completion](LeanTrominoes/Tiling/Completion/CompletionLHardness.lean).
Every output is a [valid periodic partial tiling](LeanTrominoes/Tiling/Completion/CompletionLCompilerValidity.lean),
including outputs for unsatisfiable inputs. Completing tilings need not be periodic.

For I-trominoes, [guarded gadgets](LeanTrominoes/Tiling/Completion/CompletionIGuardedRelations.lean)
and [no-crossing lemmas](LeanTrominoes/Tiling/Completion/CompletionINoCrossing.lean) give an exact
[brick-network equivalence](LeanTrominoes/Tiling/Completion/CompletionIBrickEquivalence.lean).
Reusing the orientation circuits yields
[plane co-r.e. hardness](LeanTrominoes/Tiling/Completion/CompletionIHardness.lean), with
[valid prefills and independent periods](LeanTrominoes/Tiling/Completion/CompletionICompilerValidity.lean).
[Co-r.e. membership](LeanTrominoes/Tiling/Completion/CompletionCoRE.lean) is proved for both
trominoes by searching for dependent periods, overlapping prescribed tiles,
or an unsatisfiable finite box of uncovered cells. This gives
[plane co-r.e. completeness](LeanTrominoes/Tiling/Completion/CompletionCompleteness.lean).
[Strip PSPACE completeness](LeanTrominoes/Tiling/Completion/CompletionStripHardness.lean) is proved
for both trominoes under an explicit unary encoding of height, period, and motif.
[Membership](LeanTrominoes/Tiling/Completion/CompletionStripMembership.lean) compiles valid prefills
to uncovered strips in polynomial space. Hardness uses
[diagonal routing](LeanTrominoes/Tiling/Completion/CompletionDiagonalPeriod.lean) to preserve
satisfiability, horizontal periods, and bounded height, followed by
[kernel-checked cap bands](LeanTrominoes/Tiling/Completion/CompletionStripCapBands.lean).
The finite compilers for [L](LeanTrominoes/Tiling/Completion/CompletionLStripCompiler.lean) and
[I](LeanTrominoes/Tiling/Completion/CompletionIStripCompiler.lean) produce explicit motifs,
periods, and heights. The [source reduction](LeanTrominoes/Tiling/Completion/CompletionStripSourceReduction.lean)
preserves satisfiability, and its
[polynomial-time machine](LeanTrominoes/Tiling/Completion/CompletionStripHardnessCompiler.lean)
queries the actual source records, evaluates the brick palette, and serializes
the entire prefill in unary. Every output is a
[valid partial tiling](LeanTrominoes/Tiling/Completion/CompletionStripPrefillValidity.lean),
including outputs for unsatisfiable inputs. Completing tilings need not be periodic.

The completion geometry, serialization, and final completeness theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. Their finite certificates
are checked by Lean's kernel, and the [axiom regression checks](LeanTrominoes/Verification/AxiomAudit.lean)
reject native-evaluation assumptions and unfinished proofs.

[Periodic prefills admitting only aperiodic completions](LeanTrominoes/Tiling/Completion/CompletionAperiodic.lean)
are proved to exist for both trominoes. A
[finite tile table](LeanTrominoes/Tiling/Completion/CompletionPeriodicCertificate.lean) certifies a
doubly periodic completion, and the [checks are primitive recursive](LeanTrominoes/Tiling/Completion/CompletionPeriodicComputability.lean).
Every completion with two independent integer translation periods
[yields such a certificate](LeanTrominoes/Tiling/Completion/CompletionPeriodicExtraction.lean).
If every completable prefill had one, plane completion would be r.e.,
contradicting its co-r.e. hardness.
[Cylinder pumping](LeanTrominoes/Tiling/Completion/CompletionCylinderPumping.lean) strengthens this:
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

For bounded compiler concurrency and resumable progress, use
`python scripts/build_subjects.py --resume --batch-size 4`.

The library's `LeanTrominoes.*` glob includes every Lean source module, even
when it is not imported by the small public root. New files therefore enter
the default build automatically. To build one module and its dependencies:

```sh
lake build +LeanTrominoes.Tiling.Tromino.Theorem52:olean
```

Check the final theorems' axiom dependencies:

```sh
lake build +LeanTrominoes.Verification.AxiomAudit:olean
```

Optionally replay all imported proofs in fresh kernel environments, including
foundations and dependencies. This can take hours and substantial memory:

```sh
python scripts/check_module_layout.py --kernel
```

Separate verification batches preserve independent legacy helpers that use
the same declaration name for different statements.

The project uses Lean 4.35.0 and depends on
[`lean-wang`](https://github.com/edemaine/lean-wang).
[lean-toolchain](lean-toolchain) pins Lean;
[lake-manifest.json](lake-manifest.json) pins the fetched dependencies.
