# Theorem 5.2 proof status

The completed plane proof of Theorem 5.5 has its own
[construction record](THEOREM55_FRONTIER.md). The record below concerns the
completed Theorem 5.2 construction.

The unconditional proof is
[`LeanTrominoes.Theorem52.proved`](LeanTrominoes/Theorem52Proof.lean).
It proves the complete [target statement](LeanTrominoes/Theorem52.lean):
for each tromino, periodic plane tiling is co-r.e.-complete and periodic strip
tiling under the flat encoding is PSPACE-complete. Both source-specific
geometry appenders are constructed; no compiler witness remains assumed.

The construction and validation are recorded below. Earlier development
history is in [PROGRESS_ARCHIVE.md](PROGRESS_ARCHIVE.md).

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

The [complete variable-incidence proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceBodyHorizontalSemantics.lean)
now assembles these local bodies and typed prefixes in canonical triple and
red/green/blue order. Opaque aligned columns keep the finite assembly proof
independent of the full source computation. Exact ordinary and fixed-red
typed-route formulas identify every resulting word with its geometric route.
The [canonical body theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalIncidenceBodyHorizontalSemantics.lean)
combines the variable and clause parts: the complete body list and its
delimited direction-token stream now agree with the canonical horizontal
incidence-tag selector.

The [typed element-code interpretation](LeanTrominoes/PeriodicCNFStripTypedElementCodes.lean)
now gives the structural numeric name of every actual red, green, and blue
element. Its checked enumeration lemmas retain the occurrence-entry prefix
and clause suffix for each color. The actual column and numbered-identity
bridges below now connect this interpretation to the complete compiled codes.

The [stable field-grouping lemma](LeanTrominoes/ListGroupedFieldLookup.lean)
transports numeric index selection to semantic filtering while preserving
presentation order. The [incidence-tag ordering theorem](LeanTrominoes/PeriodicThreeDMIncidenceTagElementOrder.lean)
identifies that filter with the actual per-element incidence list and lifts
the result to arbitrary aligned fields. The actual selected-body theorem
below uses these lemmas to discharge the grouping premise of contraction.

The [typed incidence-code interpretation](LeanTrominoes/PeriodicCNFStripTypedIncidenceElementCodes.lean)
now codes actual triple references and proves the complete clause suffix is
one fixed 27-reference block per clause index. The [successor-index theorem](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMOccurrenceSuccessorIndex.lean)
identifies the assembly’s next slot with modular rank succession. The
[parent-index theorem](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMOccurrenceParentIndex.lean)
recovers each actual occurrence’s parent from the broadcast clause-index
stream; [block-length transport](LeanTrominoes/FiniteBlockIndexShapeSemantics.lean)
allows the compiled stream to use the same result once clause lengths agree.

The [numbered element-code bridge](LeanTrominoes/PeriodicCNFStripTypedElementCodeEncoding.lean)
now transports structural names through the actual natural-number encoding.
It identifies the complete incidence-tag code list with typed references,
recovers each color-major element column, and proves code equality identifies
the same valid colored element when the full code list is duplicate-free.

The [finite variable-selector interpretation](LeanTrominoes/PeriodicCNFStripVariableIncidenceTypedElementCodeSemantics.lean)
now proves that current-occurrence, successor, and parent-clause selectors
name the actual typed references. It covers every genuine local triple and
color, including a cyclic successor equal to the current slot, and lifts
the result to the complete ordered local incidence block.

The [contracted route-token theorem](LeanTrominoes/PeriodicCNFStripHorizontalContractedDirectionTokenSemantics.lean)
now identifies the assembler output of correct incidence blocks with the
complete geometric route-word stream, including every edge delimiter and
canonical edge position. Its checked source-specific specialization and
polynomial-time compiler transport are recorded below.

The [actual occurrence-key interpretation](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceKeyHorizontalSemantics.lean)
now identifies unique compiled keys with the canonical horizontal occurrence
entries, proves injectivity on active entries, and recovers the common atom
identity base plus each slot’s rank. This supplies the current-key field for
the pending complete code-column proofs.

The [actual parent-index bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalParentIndexHorizontalSemantics.lean)
now identifies compiled clause-frame lengths with the normalized source,
proves the broadcast parent stream is exact, and shows that regrouping names
each canonical occurrence’s actual parent clause.

The [actual successor-key bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalNextOccurrenceKeyHorizontalSemantics.lean)
now identifies the numeric cyclic map with the next used occurrence,
including one-occurrence cycles. The [complete clause-incidence code suffix](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeHorizontalSemantics.lean)
now agrees with all actual typed clause references in clause, triple, and
red/green/blue order.

The [complete canonical element-code column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalElementCodeHorizontalSemantics.lean)
now agrees with the actual typed element enumeration for all three colors,
preserving each variable prefix, clause suffix, and color boundary.

The [complete incidence-code column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalIncidenceElementCodeHorizontalSemantics.lean)
now agrees with every actual typed reference in the variable-prefix and
clause-suffix order. It combines the verified fan, current-key, successor-key,
and parent-index fields without additional semantic premises.

The [numbered horizontal identity bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalElementCodeNumberingSemantics.lean)
now identifies both compiled code columns with the actual numbered elements
and incidence tags. Their numeric equality is exactly equality of valid
colored horizontal elements, including across colors.

The [actual selected-body and contracted-edge agreement](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSelectedIncidenceBodyHorizontalSemantics.lean)
now proves that compiled lookup selects precisely the geometric incidence
bodies at each colored element. Together with the verified degree column,
this discharges every premise of the contraction assembler: its complete
edge blocks agree with the canonical horizontal contracted blocks.

The [actual geometric route-token compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalContractedDirectionTokenHorizontalSemantics.lean)
now identifies the complete compiled stream with the geometric direction
word at every canonical contracted edge. It supplies an unconditional
polynomial-time machine for that exact delimited stream.

The [incidence endpoint-summary compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalIncidenceEndpointSummaryHorizontalSemantics.lean)
now extracts each incidence's first and last directions and attaches its
triple's complete RGB starting-direction fan. Its explicit polynomial-time
machine preserves canonical incidence-tag order. The summaries recover the
exact triple endpoint header data and retained-element outward side/color.
The finite endpoint identities are proved separately from the geometric
lookup, avoiding unnecessary unfolding of the source construction.

The [keyed endpoint regrouping compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSelectedIncidenceEndpointSummarySemantics.lean)
now selects exactly the actual endpoint records at each colored element in
canonical incidence order. It reuses the counted occurrence keys directly
with finite-value lookup and emits one record for every contraction role.

The [complete route-header compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalContractedRouteHeaderSemantics.lean)
now pairs the compiled roles and endpoint records and assembles the exact
geometric header for every canonical contracted edge. Degree-two elements
produce one header between triple endpoints; degree-three elements produce
three headers sharing their correctly ordered retained fan.

The [canonical normalization-request compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteDirectionRequestCompiler.lean)
now joins the verified headers and direction words with exact request
boundaries. It constructs the unconditional
`directSparseRouteDirectionRequestTokenCompiler` witness and composes all
three normalization rounds to compile the exact final direction words and
edge delimiters. No source-specific request-emission premise remains.

The [macrocell-coordinate identity](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATMacrocellCoordinates.lean)
now expresses every canonically gauged planar-variable position as its wrapped
drawing-grid point plus its unchanged finite local offset. For crossing
boundaries, the correction is exactly the already compiled ownership quotient;
no separate division at the refined gadget scale is needed.

The [crossing-origin compiler](LeanTrominoes/PeriodicOrthocrossingCarrierCrossingMacroOriginCompiler.lean)
scales the four signed crossing-point columns to physical macrocell origins
and proves their exact global carrier order. Its
[direct-source specialization](LeanTrominoes/PeriodicCNFStripDirectSourceCarrierCrossingMacroOriginCompiler.lean)
is unconditional and proves that these coordinate columns and the existing
normalized source-key words use the same physical node enumeration. Terminal
entries in these crossing-only columns are zero sentinels.

The [terminal affine-coordinate formulas](LeanTrominoes/PeriodicOrthocrossingCarrierPositionAffineTerminalSemantics.lean)
now give both physical coordinates, including directed local port offsets and
whole-period translations. Their finite axis/direction cases and full candidate
order are verified. The
[active-terminal compiler](LeanTrominoes/PeriodicOrthocrossingCarrierPositionActiveTerminalCompiler.lean)
expands each predicate to its eighteen terminal slots and filters away inactive
candidates. The
[complete stream compiler](LeanTrominoes/PeriodicOrthocrossingCarrierPositionActiveTerminalStreamCompiler.lean)
therefore emits exactly the actual endpoints in neighboring-segment order.
Its [direct-source specialization](LeanTrominoes/PeriodicCNFStripDirectSourceTerminalCoordinateCompiler.lean)
constructs all four signed coordinate compilers unconditionally and identifies
their output with the actual geometric terminal positions.

The [original-atom coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceOriginalAtomCoordinateCompiler.lean)
now emits all four signed columns in deduplicated source-variable order. The
[geometric identity](LeanTrominoes/PeriodicOrthocrossingRetainedSourceAtomPosition.lean)
proves that the actual canonically gauged position at index `i` is
`(160 * i + 86, 47)`. The
[aligned key compiler](LeanTrominoes/PeriodicCNFStripDirectSourceOriginalAtomWordCompiler.lean)
emits exactly the existing compact original-atom words, proves their
uniqueness, and supplies one key per coordinate entry. Both compilers are
unconditional; their inputs come from the verified formula-shape compiler.

The [binary-word keyed lookup compiler](LeanTrominoes/DelimitedBinaryWordKeyedValueLookupCompiler.lean)
now selects aligned unary values by literal word equality, preserving repeated
queries and returning zero for missing keys. Its
[semantics](LeanTrominoes/DelimitedBinaryWordKeyedValueLookupSemantics.lean)
recover the exact last matching candidate without converting binary keys into
unary integers. The
[original-atom occurrence-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateCompiler.lean)
uses this lookup to emit all four original-atom contributions in the exact
final five-family occurrence order. The
[key-separation proof](LeanTrominoes/PeriodicCNFStripOriginalAtomCoordinateLookupSemantics.lean)
shows that original keys cannot alias other constructor families, whose
contributions are zero. The
[geometric-case theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateSemantics.lean)
identifies the queries with the actual retained source, proves their validity,
and removes the remaining dictionary-membership test from the coordinate
identity. No source-specific emission or validity premise remains.

The [active terminal-key compiler](LeanTrominoes/PeriodicOrthocrossingActiveTerminalCompactKeyCompiler.lean)
now projects the existing paired source-key emission to one compact key per
physical terminal coordinate. Its
[identity semantics](LeanTrominoes/PeriodicOrthocrossingTerminalCompactKeySemantics.lean)
prove key uniqueness, exclude the other atom constructors, and place every
valid periodic terminal's translation-zero representative in the dictionary.
The [direct terminal-coordinate join](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTerminalCoordinateCompiler.lean)
therefore emits all four signed physical terminal-coordinate contributions
in the exact final occurrence order, with zero for other atom families.
The compiler and its geometric-position identity are unconditional. These
terminal coordinates are before canonical gauging.

The [physical crossing-key compiler](LeanTrominoes/PeriodicOrthocrossingCarrierCrossingCoordinateKeyCompiler.lean)
now retags the existing ranked source-pair words into a dictionary aligned
with the crossing-origin columns. Its
[membership and identity proof](LeanTrominoes/PeriodicOrthocrossingCarrierCrossingCoordinateKeySemantics.lean)
shows that global datum ranking preserves the complete retained node set and
that every valid boundary has a unique physical key. The
[direct boundary-origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalBoundaryCrossingOriginCompiler.lean)
emits all four signed crossing macrocell origins in final occurrence order,
with zero on non-boundary atoms. Its output agrees with each boundary's
actual crossing origin, without source-specific dictionary assumptions.
Local side offsets and canonical gauging are still separate steps.

The [internal crossing dictionary](LeanTrominoes/PeriodicOrthocrossingInternalCrossingCoordinateKeyCompiler.lean)
adds each of the nine internal roles to the physical crossing identity.
Its [lookup theorem](LeanTrominoes/PeriodicOrthocrossingInternalCrossingCoordinateLookupSemantics.lean)
proves exact crossing and role selection for every valid internal occurrence.
The [direct internal-origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalInternalCrossingOriginCompiler.lean)
now emits all four signed physical macrocell-origin columns in final
occurrence order, with zero for other atom families.
The [internal local-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalInternalLocalCoordinateCompiler.lean)
also emits the exact finite gadget offsets, using a general compiler for
fixed internal-role data. Both joins are unconditional and use the same
complete final occurrence presentation. The underlying
[finite-family concatenation closure](LeanTrominoes/FiniteFamilyColumnConcatCompiler.lean)
preserves the alignment of role-major keys and coordinate columns.

The [canonical crossing affine compiler](LeanTrominoes/PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateCompiler.lean)
uses the active slot's already canonical, unshifted crossing point. It
therefore compiles wrapping without a division machine, and adds the finite
side or internal-role offset in the same affine expression. The
[aligned stream](LeanTrominoes/PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateStreamCompiler.lean)
and [generic ranked-value compiler](LeanTrominoes/PeriodicOrthocrossingCarrierSourceKeyRankOrderedValueCompiler.lean)
retain the exact physical dictionary order. The
[final canonical crossing-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalCrossingCoordinateCompiler.lean)
emits all four signed columns separately for boundary and internal
occurrences. Each output agrees with the actual canonically gauged placement,
including its local offset, and contributes zero for other atom families.

The [canonical terminal compiler](LeanTrominoes/PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateCompiler.lean)
subtracts the finite endpoint gauges from the affine terminal expressions.
The gauge identity removes each retained period translate; the existing
activity filter and terminal dictionary preserve the exact occurrence order.
The [final terminal join](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalTerminalCoordinateCompiler.lean)
agrees with the actual canonically gauged terminal placement.

The [complete canonical coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalCoordinateCompiler.lean)
adds the four disjoint atom-family contributions in final occurrence order.
Its four signed columns agree with the actual canonically gauged placement
for every occurrence. This compiler is unconditional, including for an empty
input alphabet.

The [signed affine column compiler](LeanTrominoes/SignedUnaryCoordinateRefinementCompiler.lean)
now scales signed coordinates, adds aligned signed offsets, and normalizes
the result. Its subtraction adapter reuses the existing unary cancellation
machine after interleaving the columns as length-coded word pairs.

The [source-split coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSplitCoordinateCompiler.lean)
combines the factor-1152 source refinement with the finite ring displacement.
Angular slots are converted to compass ports before choosing the displacement:
angular ranks begin at east, while ring indices begin at northwest.
The [copied-literal semantics](LeanTrominoes/PeriodicCNFStripDirectSourceFinalSplitCoordinateSemantics.lean)
identifies the outputs with the actual split placement of every literal in
the copied-clause prefix, in clause and literal order. The compiler is
unconditional, including for an empty input alphabet.

The [identity-coordinate lookup](LeanTrominoes/PeriodicCNFStripDirectSourceFinalIdentityCoordinateCompiler.lean)
retrieves each represented atom's canonical position at its last-index compact
identity. Its generic lookup lemma handles repeated keys whose data agree.
The [cycle coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCycleCoordinateCompiler.lean)
combines those owner positions with the finite ring-slot table at the same
factor 1152. It includes all compass vertices and the separator and preserves
the final cycle occurrence count. The [cycle row semantics](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCycleCoordinateSemantics.lean)
identify its coordinate and identity streams with the same ring copies, and
its parent literal rows with the actual positioned cycle suffix. Every
inherited scope selects an active parent literal. Parent-local rows keep the
inherited column's unused default; their actual auxiliary coordinates still
belong to the Figure 9 stage.

Clause origins now have a simpler construction through existing route words.
The [endpoint-displacement proof](LeanTrominoes/UnitRouteEndpointDisplacement.lean)
shows that signed unit-direction counts recover a route's start from its end.
Its [retained clause specialization](LeanTrominoes/RetainedAngularFanClauseOriginFromDirections.lean)
recovers each canonical clause origin from its first literal's ring-copy
position, first direction, and stored tail. The first literal has zero shift
relative to the incidence anchor, so no period correction is needed.

The [direction-count compiler](LeanTrominoes/DelimitedDirectionDisplacementCompiler.lean)
uses finite scans for opposing cardinal counts and the existing signed unary
difference compiler. The [direct tail compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTailDisplacementCompiler.lean)
produces the exact displacement of every retained header/tail record. The
[first-parent selector](LeanTrominoes/FirstParentInheritedRouteCompiler.lean)
chooses one actual inherited first-literal route per finite parent profile.
Its [selection semantics](LeanTrominoes/FirstParentInheritedRouteSelection.lean)
prove that coordinate-row and tail-row selection retain the identical header.
The [direct parent-route compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFirstParentRouteCompiler.lean)
compiles the aligned selector, first-step fields, and selected displacement
candidates uniformly from source symbols, including empty alphabets.

The [copied-coordinate broadcast](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCopiedCoordinateCompiler.lean)
now reuses the compiled presentation-slot queries. The
[complete inherited-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalInheritedCoordinateCompiler.lean)
appends the cycle suffix and proves agreement with actual parent literal rows
and coherent occurrence lookups. The
[first-parent coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFirstParentCoordinateCompiler.lean)
selects exactly one first-literal coordinate per actual parent clause. Its
output length agrees with the selected route-displacement column. Both
compilers use the shared
[native-list Boolean filter](LeanTrominoes/UnaryFieldBooleanFilterNativeListCompiler.lean),
including its empty-alphabet case and aligned block laws. The
[selected-route geometry](LeanTrominoes/FirstParentInheritedRouteGeometry.lean)
identifies that header's tail with the original first literal's normalized
route, including tied clockwise directions.

The [parent-displacement block proof](LeanTrominoes/FirstParentInheritedRouteDisplacementSemantics.lean)
now tracks each profile beside its selected tail. Its
[direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalFirstParentRouteSemantics.lean)
identifies the selected displacement with the actual normalized route of
literal zero in each original parent clause. The
[clause-origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseOriginCompiler.lean)
subtracts these displacements from the compiled first-literal coordinates
and proves agreement with every actual canonical clause origin, in parent
order. The [zero-anchor proof](LeanTrominoes/RetainedAngularFanFinalClauseAnchors.lean)
shows that these are also the stored clause positions: copied clauses
preserve normalized source anchors, and cycle clauses have zero offsets.

The [source-parent scan](LeanTrominoes/PeriodicCNFStripHorizontalSourceOccurrenceParentIndices.lean)
agrees with the parent index of every coherent occurrence, including the
cycle suffix. The [origin broadcast](LeanTrominoes/PeriodicCNFStripDirectSourceFinalOccurrenceClauseOriginCompiler.lean)
uses these indices to attach each actual stored parent position to its own
occurrence rows. The [clearance compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClearanceClauseOriginCompiler.lean)
applies factor two and identifies each result with that occurrence's actual
metadata source clause.

The [template position proof](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineClausePositionSemantics.lean)
derives all generated clause offsets from the existing template-instantiation
equality. The [finite offset compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTemplateClauseCoordinateCompiler.lean)
selects those positions from each header's exact profile and local clause
index. The [composed origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalComposedClauseOriginCompiler.lean)
adds the offset to the factor-72 clearance origin, accounting for the
factor-twelve Figure 9 stage and factor-six unit elimination. Its lookup
proof uses the same metadata witness for both operands. The shared
[signed refinement lookup](LeanTrominoes/SignedUnaryCoordinateRefinementLookup.lean)
preserves exact pointwise coordinates and the common column length.
The [gauge transport](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceClausePositions.lean)
identifies the same raw stored position with the canonical clause origin
after final clockwise ordering and variable gauging.

The [finite variable-offset compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTemplateVariableCoordinateCompiler.lean)
now uses the same coherent header stream as the clause-offset compiler.
The [auxiliary coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalAuxiliaryCoordinateCompiler.lean)
adds those offsets to the factor-72 clearance parent origin. Its
[occurrence proof](LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryPositions.lean)
identifies the exact instantiated template role, then reuses the existing
physical endpoint and fundamental-square bounds. The shared
[gauge lemma](LeanTrominoes/PeriodicVariablePlacementCanonicalGaugeLiteralPosition.lean)
recovers a variable's canonical representative from any bounded physical
literal occurrence; no modulo compiler is needed.

The [inherited coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalComposedInheritedCoordinateCompiler.lean)
scales the complete ring-coordinate column by 144, accounting for clearance,
Figure 9, and unit elimination. Its source witness retains the same actual
ring atom and parent literal lookup, and the
[inherited gauge proof](LeanTrominoes/PeriodicCNFPlanarRetainedFinalGaugedInheritedPosition.lean)
shows that this natural position is already inside the final period.
The [combined variable compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalComposedVariableCoordinateCompiler.lean)
selects these two columns with the existing atom-scope bits. It has an
unconditional polynomial-time certificate, including empty source alphabets,
and exact final-gauged literal lookup semantics for every original polarity
occurrence.

The [initial-route coordinate lemma](LeanTrominoes/UnitRouteInitialCoordinates.lean)
and its [polarity refinement specialization](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRoutePointAffine.lean)
recover the first two refined points from the source origin and first direction.
The direction comes from the route before polarity normalization; a complement
operation can reverse the output route's first edge. A
[finite header-point compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalHeaderCoordinateCompiler.lean)
supplies these direction offsets, and the
[subdivision coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolaritySubdivisionCoordinateCompiler.lean)
adds them to three times the exact final-gauged clause origin. Its occurrence
proof identifies both actual refined points, including the fresh variable at
point 1 and the complement-clause position at point 2.

The [complete polarity variable compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateCompiler.lean)
selects the fresh point or three times the original variable position for all
four polarity operations. The
[horizontal agreement theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateHorizontalSemantics.lean)
identifies the entire emitted column with actual horizontal routed variable
positions, discharges all source conditions, and gives an unconditional native
polynomial-time certificate. The auxiliary compiler's local finite-instance
name is also distinct from the clause compiler's, allowing both imports together.

The [source-indexed clause-position theorem](LeanTrominoes/PeriodicOneInThreePolarityNormalizationSourceIndexedClausePositions.lean)
identifies every descriptor's canonical clause origin and the complete output
order. The [polarity clause compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateCompiler.lean)
uses one affine refinement: three times the source origin, plus zero for a main
clause or two source-direction steps for a complement clause. Its
[exact lookup proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateSemantics.lean)
recovers genuine refined source members from the actual atom decoder. The
[horizontal agreement theorem](LeanTrominoes/PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateHorizontalSemantics.lean)
discharges every source and decoder premise and supplies an unconditional
native polynomial-time compiler for all actual canonical clause origins,
repeated in clause-major, literal-minor order.

The [gadget-origin geometry proof](LeanTrominoes/PeriodicCNFStripHorizontalGadgetOriginAffineCoordinates.lean)
accounts for doubled padding, zero-anchor clause normalization, and macrocell
placement. Both actual origin columns are affine in the routed endpoints:
factor 256 with offset (20, 64) for variables or (50, 60) for clauses. The
[shared native origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGadgetOriginCoordinateCompiler.lean)
uses the complete endpoint columns and a finite constant-header offset column.
Its certificate emits the actual variable or clause gadget origins in occurrence
order, including empty source alphabets.

The [first-occurrence control proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseFirstOccurrenceBits.lean)
identifies the top-terminal flag with the first literal of each actual clause.
The [clause-origin selector](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseGadgetOriginCompiler.lean)
therefore emits one origin per clause, using the proved binary-or-ternary arity.
The [fixed-table coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseVertexCoordinateCompiler.lean)
translates any finite local vertex table at those origins. Its
[index semantics](LeanTrominoes/PeriodicCNFStripHorizontalClauseGadgetOriginIndexSemantics.lean)
retain the actual clause indices, and the
[clause-triple specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseTripleCoordinateCompiler.lean)
now compiles all four signed coordinate columns of the actual nine-triples-per-clause
suffix, in canonical order, with no source-specific compiler assumptions.
The reusable [signed table expansion](LeanTrominoes/SignedUnaryCoordinateTableExpansion.lean)
composes existing finite scans, fixed copying, and affine arithmetic.

The [grouped variable-origin compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalGroupedVariableOriginCompiler.lean)
uses the existing canonical occurrence-index queries for every signed coordinate
column. Its lookup proof attaches each origin to the same actual atom as the
grouped fan and slot fields, including repeated active slots.

The [metadata-selected signed expansion](LeanTrominoes/SignedUnaryCoordinateIndexedTableExpansion.lean)
now broadcasts each origin over its finite local table using the existing
block-index and value-lookup compilers, then applies signed affine addition.
Its exactness theorem preserves metadata, source, and table order. The
[variable-table geometry proof](LeanTrominoes/PeriodicCNFStripGroupedVariableTriplePositionTable.lean)
identifies the actual connector kind, polarity, and active slot, including an
explicit transport between the geometric and ribbon equality instances.
The [variable-triple compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVariableTripleCoordinateCompiler.lean)
therefore emits the actual variable prefix, with seven positions for fixed-red
connectors and three for either other connector.

The [complete triple-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTripleCoordinateCompiler.lean)
appends the clause suffix and emits all four signed coordinate columns in
canonical triple order. Repeating each position three times gives the RGB
incidence source column. Its
[drawing agreement proof](LeanTrominoes/PeriodicCNFStripDirectSourceFinalIncidenceSourceCoordinateSemantics.lean)
identifies every entry with the actual drawing position of that incidence's
source triple, in the same tag order used by incidence identities and directions.
All these native compiler certificates are unconditional, including empty
source alphabets.

The [shared ranked-index proof](LeanTrominoes/PeriodicCNFStripCountedContractedIncidenceRankedIndexSemantics.lean)
now identifies canonical element/rank lookup with the actual incidence
presentation indices. The existing direction-body theorems are short map
corollaries of that proof. The
[scalar selection compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalIncidenceValueSelection.lean)
reuses the same keys for any compiled natural-number field and proves exact
agreement with the actual element-major incidence groups.

The [source filter](LeanTrominoes/PeriodicCNFStripCountedContractedIncidenceSourceFilter.lean)
keeps all three incidences of each degree-three element and only the first
incidence of each degree-two element. Its proof identifies the resulting
fields with the source tags of the actual contracted edges, in their complete
canonical order. The
[contracted-coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalContractedSourceCoordinateCompiler.lean)
therefore emits all four signed coordinate columns of the actual route starts.
The [raster field bridge](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRasterHorizontalCoordinateCompiler.lean)
provides an unconditional native compiler for the canonical horizontal header
field, and identifies grid reflection of the compiled vertical column with
the canonical vertical-complement field.

The [unit-length broadcast compiler](LeanTrominoes/UnaryFieldUnitLengthBroadcastCompiler.lean)
turns the compiled drawing-grid unit word into one grid-size field per route.
The [vertical-field compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRasterVerticalCoordinateCompiler.lean)
subtracts the source vertical coordinate and one from twice that grid size,
with exact agreement with the canonical raster metadata. The
[color compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRasterColorCompiler.lean)
emits RGB codes per triple, applies the verified incidence ordering and source
filter, and decodes the actual contracted-edge colors.

The [request assembler](LeanTrominoes/GadgetSparseRouteRasterRequestAssemblyCompiler.lean)
joins the three unary fields, finite color field, and normalization batch in
exact edge order. The [direct specialization](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean)
constructs the unconditional raster-request compiler and complete route-record
appender required by the final closure.

The [retained-element coordinate compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRetainedElementCoordinateCompiler.lean)
uses the exact clause arity bits to select three or four local positions per
color and translates them by the compiled clause origins. The
[record compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRetainedElementRecordCompiler.lean)
adds grid reflection and monochromatic cell types. These are all retained
element vertices, in canonical red/green/blue block order.

The [triple cell-type compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTripleCellTypeCompiler.lean)
selects each triple's red incidence summary, which already contains the full
RGB fan, and computes the actual normalized cell type. The
[triple-record compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalTripleRecordCompiler.lean)
combines this finite column with the complete triple coordinates and stable
indices, covering both the variable prefix and clause suffix.

The [shared column joiner](LeanTrominoes/FiniteAlphabetRecordColumnCompiler.lean)
and [affine vertex assembler](LeanTrominoes/GadgetSparseAffineVertexRecordColumnCompiler.lean)
serialize independently compiled fields in their common row order. The
[complete vertex appender](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean)
concatenates the four exact blocks, retains the source word, and applies the
verified affine expansion. All source compiler certificates include empty
source alphabets.

The [canonical degree column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics.lean)
and [clause-incidence body suffix](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics.lean)
already agree with the horizontal construction.

## Final compiler witnesses

All names below are in `LeanTrominoes.PeriodicCNFStripReduction`. Each witness
is uniform in an arbitrary encoded source language and its
`Complexity.DeciderInPolySpace` decider.

| Construction stage | Constructed witness | Module |
| --- | --- | --- |
| Canonical raster-request emission | `directSparseRouteRasterRequestTokenCompiler decider` | [Route compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean) |
| Retained-workspace route appender | `directSparseRouteRecordAppender decider` | Same module |
| Compact vertex requests | `directSparseAffineVertexRequestTokenCompiler decider` | [Vertex compiler](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean) |
| Retained-workspace vertex appender | `directSparseVertexRecordAppender decider` | Same module |
| Uniform split appenders | `directSparseSplitRecordAppenders` | [Complete proof](LeanTrominoes/Theorem52Proof.lean) |
| Complete Theorem 5.2 | `LeanTrominoes.Theorem52.proved` | Same module |

The concrete vertex and route appenders instantiate the
[final closure](LeanTrominoes/Theorem52DirectSparseClosure.lean), which combines
strip membership and hardness with the established plane completeness proof.

## Validation

`lake build` includes every module through the library glob, including the
public theorem interface and the unconditional `Theorem52.proved` declaration.

The four-worker full project build completed on 2026-09-12 with exit code 0,
10,469 jobs, and an elapsed time of 213.265 seconds. Its log is
`tmp/theorem52-complete-full-build.log`. All eight new Lean modules built
without diagnostics. The completed build log and cached project trace files
contain no errors or compiler panics.

A separate public-import audit completed with exit code 0 in 146.108 seconds.
It checks `Theorem52.proved : Theorem52.statement`, the strip projection, and
both universal completeness assertions through `import LeanTrominoes`. Its
source and log are `tmp/Theorem52CompletionAudit.lean` and
`tmp/theorem52-completion-audit.log`.

Both axiom lists contain `propext`, `Classical.choice`, and `Quot.sound`, plus
5,877 generated `native_decide` certificates from the existing construction
and dependencies. There is no `sorryAx` or other axiom in either list. The
proof therefore retains the existing reliance on native evaluation; this is
not an audit restricted to kernel reduction alone.
