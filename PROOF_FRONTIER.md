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

The [horizontal presentation proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPresentedDirectionWords.lean)
now identifies the complete direct word list with the actual computed
horizontal routed source. It also proves that the colored occurrence
compiler consumes those actual route words, surrounded by its compiled
finite endpoint frames. This uses the [exact polarity-list geometry lemma](LeanTrominoes/PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockGeometry.lean)
and the geometry of genuine final gauged incidences.

The endpoint audit found and corrected two orientation errors. Stored routes
run from clause to variable, while occurrence routes run in reverse. Clause
fans now use the opposite stored first direction. Their [direction semantics](LeanTrominoes/PeriodicCNFStripHorizontalRoutedRouteHeaderClauseDirectionSemantics.lean)
prove agreement with the arriving direction of a completed route.
Variable fans now consume [completed occurrence records](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVariableOccurrenceData.lean)
whose direction is the opposite stored last direction, including the dynamic
tail. The [finite-state compiler](LeanTrominoes/PeriodicCNFStripHorizontalRoutedVariableOccurrenceCompiler.lean)
retains only the tail's last symbol; its exactness follows from the
[endpoint summary lemmas](LeanTrominoes/PeriodicCNFStripHorizontalRoutedRouteHeaderEndpointDirections.lean).
The preliminary header projection remains available for identity compilation.
The [direct endpoint-column theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalEndpointDirections.lean)
identifies the variable fan input directions with the actual horizontal route
words. The grouped fan field proofs now use these completed records.
Unused variable-fan directions now use north, matching the horizontal source.
The [inactive-slot lemmas](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVariableFanInactiveDirections.lean)
prove this for both direct enumeration orders. The finite assembler uses an
explicit empty initial state, which also removes a pre-existing Lean code-generation
panic in its derived `Inhabited` instance.

The [clause direction blocks](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseDirectionBlocks.lean)
now agree with the actual horizontal clauses, preserving every clause boundary
and literal index. Their exact arities recover the block boundaries from the
already equal flattened direction columns. The direct clause fans are assembled
from those blocks, and their terminal groups are the actual literal-index groups.
The [semantic fan lookup](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanIndexedDirections.lean)
selects the stored route at that same clause and literal index.
The [generic direction-block lemmas](LeanTrominoes/PeriodicCNFStripHorizontalClauseIncomingDirectionBlocks.lean)
show that positive padding and anchor normalization preserve these blocks, and
recover the semantic fan of every genuine clause from its ordered route words.
Their [horizontal specialization](LeanTrominoes/PeriodicCNFStripHorizontalClauseFanDirectionBlockSemantics.lean)
identifies the computed fan list. The [direct clause-frame theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseFanHorizontalSemantics.lean)
now proves joint agreement of every clause fan and literal terminal group with
the horizontal construction, both block by block and in flattened occurrence order.
The [compiler certificates](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseFanHorizontalCompiler.lean)
now emit these actual horizontal fan and clause-frame field streams in polynomial
time, with their semantic agreement discharged.

The [header literal-index proof](LeanTrominoes/PeriodicCNFStripHorizontalRoutedRouteHeaderLiteralIndexBlocks.lean)
now identifies every output header with its actual literal position. The
[joint occurrence-field theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceFieldsHorizontalSemantics.lean)
proves that kind, polarity, and variable-end direction all belong to that same
incidence in the normalized horizontal source. The [shared field lemmas](LeanTrominoes/PeriodicCNFStripHorizontalPresentedOccurrenceFields.lean)
prove that padding and anchor normalization preserve this complete field stream.
The [occurrence-field compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceFieldsHorizontalCompiler.lean)
emits this actual semantic stream in polynomial time.

The [source-indexed atom decoder](LeanTrominoes/PeriodicOneInThreePolarityNormalizationSourceIndexedAtoms.lean)
recovers the original or fresh atom selected by every polarity operation,
using the exact refined source literal. Its
[direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSourceIndexedAtomsHorizontalSemantics.lean)
identifies the actual horizontal atom column at the same source coordinates
already carried by the route-pair stream.

The [parent descriptor bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseDescriptorSourceSemantics.lean)
identifies the compiled parent list with the actual source descriptors, apart
from ignored variable markers. The [local-code projection](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceLocalAtomCodes.lean)
therefore uses each coherent occurrence's own parent and header.
The [fresh-key proof](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentity.lean)
identifies the parent/prefix key with the global source occurrence, using
canonical finite-prefix reconstruction. The [complete numeric-code proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFreshAtomIdentity.lean)
and [horizontal atom theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFreshAtomHorizontalSemantics.lean)
now prove that every comparison involving a genuine fresh incidence has equal
compiled identities exactly when its actual horizontal atoms are equal. Parity
separates inherited atoms, and the finite local quotient separates original
auxiliary atoms from fresh ones.

The [original-atom transport](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedAtoms.lean)
now preserves the selected instantiated atom through final clockwise ordering,
variable gauging, anchor normalization, and refinement. Its
[direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOriginalAtomHorizontalSemantics.lean)
constructs the occurrence witness at each genuine index and identifies every
original horizontal atom with that witness's instantiated template role.

The [auxiliary identity proof](LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineAuxiliaryIdentity.lean)
uses global first-stage metadata lookups to keep unit-elimination auxiliaries
in distinct parents separate. The [occurrence bounds](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryAtoms.lean)
supply its exact local-index premises. The [atom classification](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAtomClassification.lean)
separates actual inherited variables from auxiliaries. Their
[horizontal specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalAuxiliaryAtomHorizontalSemantics.lean)
now proves numeric identity agreement for every comparison involving an
original auxiliary, including comparisons with inherited and fresh atoms.

Next prove the remaining inherited-to-inherited identity comparisons, then
identify stable occurrence ranks with source order. This will identify the
complete variable fans and grouped occurrence bodies, then the canonical
contracted raster requests. The [canonical degree column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics.lean)
and [clause-incidence body suffix](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics.lean)
already agree with the horizontal construction.

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

The complete default `lake build` passed on 2026-09-07: all 10,231 jobs
succeeded. This includes the actual source-descriptor and local-code bridges,
finite fresh-key reconstruction, and every numeric comparison involving a
fresh atom, including separation from inherited and original auxiliary atoms.
It also includes original-atom transport through all final geometric
normalizations and its actual horizontal specialization. All comparisons
involving original auxiliaries now agree with horizontal atoms, with genuine
first-stage index bounds and inherited/auxiliary constructor separation.
The changed modules' build traces contain no compiler diagnostics.
