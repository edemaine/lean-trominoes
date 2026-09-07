# Current proof frontier

The target is an unconditional proof of
[`LeanTrominoes.Theorem52.statement`](LeanTrominoes/Theorem52.lean).
The plane conjunct and strip PSPACE membership have proofs. The outstanding
work is the strip hardness reduction. This file tracks witnesses consumed by
the final construction; the old intermediate checklist is in
[PROGRESS_ARCHIVE.md](PROGRESS_ARCHIVE.md).

## Route-word agreement

The generic source-word agreement is proved by
[`OccurrenceWitness.sourceDirectionWord`](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceDirectionWords.lean).
Its [direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSourceWords.lean)
now proves that every direct header/tail pair denotes the final gauged source
direction word at its attached clause/literal index. This discharges the
`sourceWords` premise and proves
`directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata`
without that assumption.

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
The complete [auxiliary](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryRoutes.lean)
and [inherited](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedRoutes.lean)
route-word equalities are proved. The inherited proof uses distinct source
atoms to identify the exact geometric source slot, then combines the
connector and tail equalities with factor-144 repetition.

Next lift the exact metadata words to the actual horizontal routed source,
then prove agreement of the finite endpoint frames, grouped occurrence
bodies, and raster requests. The [exact polarity-list geometry lemma](LeanTrominoes/PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockGeometry.lean)
reduces the metadata-level geometry premise to geometry of genuine source
incidences, which is already available for the final gauged construction.

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
The complete inherited and combined source-word proofs and the exact
polarity-list geometry lemma also passed targeted Lean checks. The direct
stream specialization and unconditional exact metadata word-list equality
passed a targeted Lean check on 2026-09-07 after rebuilding their dependencies.
