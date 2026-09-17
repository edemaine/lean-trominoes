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
For each tromino, there is also a completable periodic prefill with no
doubly periodic completion.

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
| Periodic L- and I-tromino prefills admitting completions but no doubly periodic completion | `PeriodicTrominoPrefill.exists_no_doubly_periodic_completion` | [CompletionAperiodic](LeanTrominoes/CompletionAperiodic.lean) |
| Plane co-r.e. membership | `periodicTrominoTiling_coRE` | [ComputableSearch](LeanTrominoes/ComputableSearch.lean) |
| Theorem 5.2, strip PSPACE membership | `PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE` | [PartrecFlatStripDeciderSpace](LeanTrominoes/PartrecFlatStripDeciderSpace.lean) |
| Theorem 3.2, local 1D periodic CNF SAT PSPACE hardness | `PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEHard` | [PeriodicCNFPolySpaceHardness](LeanTrominoes/PeriodicCNFPolySpaceHardness.lean) |
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
Intermediate construction lemmas do not by themselves close a paper theorem.

| Paper results | Current coverage |
| --- | --- |
| Theorem 3.1 | Imported Wang tiling theorem |
| Theorem 3.2 | Local 1D CNF SAT hardness proved; full theorem open |
| Theorem 5.2 | Fully proved |
| Theorem 5.5 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Corollary 5.6 | Plane co-r.e. completeness and strip PSPACE completeness proved |
| Two connected polycubes | Full 3D and every fixed slab height > 1 proved |
| Corollary 5.9 | Translation-only co-r.e. completeness in full 3D and every fixed slab height > 1 proved |
| Tromino completion | L- and I-tromino plane co-r.e. completeness and strip PSPACE completeness (unary encoding) proved |
| Theorems 2.1–2.2, Lemma 2.3, Theorems 3.3–3.8 | Construction infrastructure exists; full paper statements remain open |
| Section 4, Lemma 5.1 in its full generality, and other results 5.3–5.15 except those listed above | Open |

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

[Periodic prefills without doubly periodic completions](LeanTrominoes/CompletionAperiodic.lean)
are proved to exist for both trominoes. A
[finite tile table](LeanTrominoes/CompletionPeriodicCertificate.lean) certifies a
periodic completion, and the [checks are primitive recursive](LeanTrominoes/CompletionPeriodicComputability.lean).
Every completion with two independent integer translation periods
[yields such a certificate](LeanTrominoes/CompletionPeriodicExtraction.lean).
If every completable prefill had one, plane completion would be r.e.,
contradicting its co-r.e. hardness. The result excludes full-rank period
lattices; absence of even a single nonzero translation period remains a
stronger statement. The certificate proofs use only standard Lean axioms;
the existence theorem adds no axioms beyond plane hardness.

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
