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

Next propagate these coordinates through the remaining fixed refinements.
The resulting horizontal origins supply the raster-request metadata and
remaining vertex emitter.
The [canonical degree column](LeanTrominoes/PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics.lean)
and [clause-incidence body suffix](LeanTrominoes/PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics.lean)
already agree with the horizontal construction.

## Final compiler witnesses

All names below are in `LeanTrominoes.PeriodicCNFStripReduction`. Each witness
is uniform in an arbitrary encoded source language and its
`Complexity.DeciderInPolySpace` decider.

| Construction stage | Available sufficient witness | Consumer |
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
The compact-source row is one way to obtain the raster-request row. The
verified geometric route-token compiler also supplies the direction component
for a direct construction of the raster-request emitter.

Alternative existing appender constructors can bypass the five-family
interface. In either case, instantiate actual witnesses before invoking a
closure theorem. Do not mark the full theorem proved while its proof still
assumes one of these compiler contracts.

## Validation

`lake build` includes every module through the library glob. Build coverage
and proof completion are separate: compiling conditional closure theorems
does not prove the unconditional target.

The four-worker full project build completed on 2026-09-08 with exit code 0
and 10,378 jobs. Its log is
`tmp/canonical-terminal-coordinate-full-build.log`. It includes all eleven new
canonical terminal affine, alignment, stream, geometry, and final-lookup
modules, the native-list aligned-addition compiler, and the complete
canonical coordinate compiler. It also includes the previously verified
crossing and original-atom coordinate joins, identities, incidence and
contraction compilers, headers, and normalization requests.

All eleven new modules built without diagnostics.
The completed full-build log and all cached project trace files were checked
for errors and compiler panics; none were found.
