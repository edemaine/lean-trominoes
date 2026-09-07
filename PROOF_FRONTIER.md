# Current proof frontier

The target is an unconditional proof of
[`LeanTrominoes.Theorem52.statement`](LeanTrominoes/Theorem52.lean).
The plane conjunct and strip PSPACE membership have proofs. The outstanding
work is the strip hardness reduction. This file tracks witnesses consumed by
the final construction; the old intermediate checklist is in
[PROGRESS_ARCHIVE.md](PROGRESS_ARCHIVE.md).

## Route-word agreement

The immediate semantic obligation is the `sourceWords` premise of
[`directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata_of_sourceWords`](LeanTrominoes/PeriodicCNFStripDirectSourceFinalExactMetadataDirectionListReduction.lean):
every direct header/tail pair denotes the final-gauged source direction word
at its attached clause/literal index.

The common proof-side stream is now
[`SourceOccurrence`](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrences.lean).
It retains the original parent index, absolute generated-clause index,
directed profile, header, and ordered tail row. Its pair projection is the
existing executable stream, so machine serialization is unchanged.

[`OccurrenceWitness`](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata.lean)
ties a record to both its original refined clause and its generated metadata
using the full `ClauseMetadata.key`. Its `metadataCoordinates` theorem
recovers the original/reordered literal indices and proves the source index
is in bounds. Its `inheritedTail` theorem identifies the selected tail with
the canonical route at **that metadata's original parent index**.
The [direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceWitness.lean)
now supplies the existing
[metadata lookup](LeanTrominoes/PeriodicCNFStripDirectSourceFinalMetadataProfileCoordinateLookup.lean).

The witness now proves the [exact local route and both literal-index bounds](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLocalRoutes.lean),
the [inherited connector at its selected source slot](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedConnectors.lean),
and [direction-word transport to the final gauged index](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedRoutes.lean).
The connector proof uses [direction preservation through the paired clockwise sort](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineRoutePrefixOrderedFanSemantics.lean).

The header's selected template atom now [instantiates to the actual raw literal](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms.lean).
The [case-classification lemmas](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics.lean)
preserve auxiliary roles and identify the atom at each active inherited slot.
The [complete auxiliary route-word equality](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryRoutes.lean)
is proved.

The remaining source-word proof must equate the inherited header's selected
slot with the geometric provenance's source literal index. Then combine the
connector and tail lemmas with the
[inherited geometric direction-block theorem](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedRouteDirectionBlock.lean)
Retain the factor-144 tail repetition.

Consume source-word equality in the existing direction-list and polarity
lifts, then in the framed occurrence, contraction, and raster-request
compiler. A coordinate projection alone does not discharge this obligation.

## Final compiler witnesses

All names below are in `LeanTrominoes.PeriodicCNFStripReduction`. Each witness
is uniform in an arbitrary encoded source language and its
`Complexity.DeciderInPolySpace` decider.

| Required witness | Exact type | Consumer |
| --- | --- | --- |
| Affine vertex emission | `DirectSparseAffineTablePhaseFamilies decider` | [directSparseVertexRecordAppenderOfTablePhases](LeanTrominoes/PeriodicCNFStripDirectSparseAffineTablePhaseCompiler.lean) |
| Compact framed route emission and semantic agreement | `DirectSparseCompactContractedRouteRasterSourceCompiler decider` | [directSparseRouteRasterRequestTokenCompilerOfCompactSource](LeanTrominoes/PeriodicCNFStripDirectSparseCompactContractedRouteRasterSourceCompiler.lean) |
| Canonical raster-request emission | `DirectSparseRouteRasterRequestTokenCompiler decider` | [directSparseRouteRecordAppenderOfRasterRequests](LeanTrominoes/PeriodicCNFStripDirectSparseRouteRasterRecordCompiler.lean) |
| Vertex and route appenders for every source decider | `DirectSparseSplitRecordAppenders` | [theorem52_statement_of_directSparseSplitRecordAppenders](LeanTrominoes/Theorem52DirectSparseClosure.lean) |

These final witnesses have not yet been constructed. The five affine
families carry exact output proofs for variable triples,
clause triples, and red/green/blue elements. The compact route compiler
carries an explicit token function, its polynomial-time certificate, and
equality of the fixed bridge's output with the canonical raster requests.
The raster-request row is obtained from the compact-source row, not an
independent additional machine.

Alternative existing appender constructors can bypass the five-family
interface. In either case, instantiate actual witnesses before invoking a
closure theorem. Do not mark the full theorem proved while its proof still
assumes one of these compiler contracts.

## Validation

`lake build` is configured to include every module through the library glob.
Build coverage and proof completion are separate: a successful build of
conditional closure theorems does not prove the unconditional target.

The complete default `lake build` passed on 2026-09-06: all 10,184 build
jobs succeeded, covering the then-existing 7,007 tracked Lean source files.
The subsequent occurrence route, connector, literal-instantiation, and
auxiliary-word lemmas passed a targeted Lake build of 4,800 jobs on
2026-09-07.
