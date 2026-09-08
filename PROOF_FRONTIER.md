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

The [presentation-slot proof](LeanTrominoes/PeriodicCNFStripHorizontalRoutedPresentationSlotSemantics.lean)
identifies the inverse clockwise permutation, including tied directions. The
[inherited occurrence witness](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedSourceLiterals.lean)
therefore selects the exact original parent literal and its instantiated atom.
The [common ring-code semantics](LeanTrominoes/PeriodicCNFStripDirectSourceFinalInheritedRingAtomSemantics.lean)
prove that numeric identities separate actual retained source atoms and ring
slots. Copied codes query this semantic candidate column, and cycle codes use
the actual distinct source atoms in their construction order.

The [actual ring-variable code](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRingVariableSemantics.lean)
converts between east-first angular slots and northwest-first compass-variable
indices, keeping the separator distinct. The [copied-atom proof](LeanTrominoes/RetainedAngularOccurrenceCopiedAtomSemantics.lean)
shows that every bounded stable rank selects the actual assigned compass port.
The [direct copied-column semantics](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCopiedRingVariableSemantics.lean)
therefore identify the candidate stream with actual copied literals, and each
compiled query with its own parent literal row. This uses the
[clause-local selection theorem](LeanTrominoes/PeriodicCNFStripHorizontalRoutedCopiedSourceBlockSelection.lean)
and the [coherent occurrence projection](LeanTrominoes/PeriodicCNFStripHorizontalSourceOccurrenceCopiedValues.lean).
The [cycle-table check](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCycleRingLiteralSemantics.lean)
identifies every fixed slot with its actual local cycle literal and proves
that every inherited lookup is active.

The [occurrence-block decomposition](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceBlocks.lean)
preserves parent indices, generated-clause offsets, and consumed tail rows.
Its [direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceBlocks.lean)
identifies the copied and cycle parts of the complete witness stream, including
the common copied-record and inherited-code boundary. The
[global copied-identity proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCopiedInheritedAtomHorizontalSemantics.lean)
now identifies each inherited copied incidence with its witnessed ring literal
and actual horizontal atom. Two inherited copied incidences have equal numeric
identities exactly when their horizontal atoms agree. The
[ring membership proof](LeanTrominoes/PeriodicCNFFormulaShapeRetainedFigureNineRingAtomMembership.lean)
classifies every atom in the complete pre-Figure 9 source as a genuine compass
or separator copy of a represented retained atom, and identifies the actual
cycle literal rows in stable source-atom order.

The [parent value rows](LeanTrominoes/PeriodicCNFStripDirectSourceFinalAtomValueRows.lean)
combine copied and cycle literals in actual parent order, retaining each
phase's unused fallback value at parent-local positions. The
[shared row projection](LeanTrominoes/PeriodicCNFStripHorizontalSourceOccurrenceAtomValueRows.lean)
and [complete code alignment](LeanTrominoes/PeriodicCNFStripDirectSourceFinalAtomValueRowCodes.lean)
identify every inherited-column entry with its coherent occurrence's own row.
The [full inherited proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalInheritedAtomHorizontalSemantics.lean)
therefore covers copied and cycle incidences with one argument. Combined with
the fresh and auxiliary cases, the [complete identity theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalAtomIdentityHorizontalSemantics.lean)
proves that any two compiled identities are equal exactly when their actual
horizontal atoms are equal.

The [partition transport lemmas](LeanTrominoes/StableOccurrenceRanksPartition.lean)
preserve all prefix counts, total multiplicities, and stable ranks under an
exact correspondence of equality classes. Their [direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceStableRankHorizontalSemantics.lean)
identifies the compiled group-size and stable-rank columns with those of the
actual horizontal atom list in clause/literal order.

The [fan rank-query bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFanRankLookup.lean)
now selects the exact presentation index used by the normalized source's
occurrence lookup. [Filtered field lookup](LeanTrominoes/PeriodicCNFStripHorizontalOccurrenceFieldLookup.lean)
retains that same tagged clause and literal. The [active-query semantics](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFanOccurrenceFieldSemantics.lean)
therefore identify the selected connector kind, polarity, and outgoing route
direction with the actual semantic incidence.

The [complete variable-fan theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVariableFanHorizontalSemantics.lean)
now identifies every compiled fan with the actual horizontal fan of its atom,
both pointwise and as a complete clause-major stream. The [shared assembly proof](LeanTrominoes/FinalFanDataSourceSemantics.lean)
covers inactive kind/polarity slots by the same last-occurrence fallback and
inactive directions by north. The [polynomial-time certificate](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVariableFanHorizontalCompiler.lean)
emits this complete actual fan stream with semantic agreement discharged.

The [exact grouping proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedOccurrenceEntryOrder.lean)
identifies the compiled occurrence indices with the canonical source's
atom/slot entry enumeration. Both use last-representative variable order and
increasing active occurrence rank. The [complete grouped fan/slot theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics.lean)
keeps every actual horizontal fan and active slot attached to its own entry;
the [grouped compiler certificate](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalCompiler.lean)
emits this actual semantic stream in polynomial time. The [prefix-body theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixHorizontalSemantics.lean)
then identifies all finite variable prefixes in canonical entry, typed-triple,
and red/green/blue order.

The [joint endpoint-frame proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceFrameHorizontalFields.lean)
now keeps the variable fan, occurrence slot, clause fan, and terminal group
attached to one actual source entry. The [stored-word lookup](LeanTrominoes/PeriodicCNFStripDirectSourceFinalStoredWordOccurrenceSemantics.lean)
selects that same incidence’s header/tail pair. Shared tagged-occurrence
field lookup preserves the clause and literal indices through normalization.
The [specified-block geometry theorem](LeanTrominoes/PeriodicCNFStripHorizontalOccurrenceSpecifiedDirectionBlock.lean)
uses the compiler’s chosen compact block directly: the source, corridor, and
coordinated-route lemmas now expose exact word formulas while retaining
their earlier existential interfaces.

The [complete occurrence-body proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceBodyHorizontalSemantics.lean)
now identifies every compiled red/green/blue body with its actual coordinated
geometric route. A generic renderer lemma combines the coherent endpoint
fields with the selected stored word. The [grouped body theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedOccurrenceBodyHorizontalSemantics.lean)
preserves these complete bodies in canonical atom/slot entry order.

Next assemble the complete variable-incidence bodies from these verified
local bodies and typed prefixes, then obtain the canonical contracted raster
requests. The [canonical degree column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics.lean)
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

The grouped-order integration `lake build` completed on 2026-09-07 with
exit code 0 and 10,272 jobs. A subsequent trace audit found two code-generation
panics reported as informational diagnostics in derived `Inhabited` instances.
Those instances now have explicit defaults preserving the previous values;
both modules pass individual Lean checks with no diagnostics.

The ten new occurrence-field and complete-body modules, plus the three
refactored route geometry modules, pass individual Lean checks with no
diagnostics. The subsequent full rebuild on 2026-09-08 failed on two
library-import reads under memory pressure. Both affected modules passed
individual checks after that build stopped.

Full diagnostic logging also exposed ten older code-generation panics in
seven cached modules. Their derived defaults have been replaced by explicit
instances preserving the selected constructors. All seven modules pass
individual Lean checks without panics; two existing unused-simp warnings
remain in `GadgetPixelFiniteTokens`. A clean full-build result is still pending.
