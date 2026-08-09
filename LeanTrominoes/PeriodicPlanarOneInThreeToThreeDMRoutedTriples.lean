import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-!
# Routed terminal triples in the planar 3DM assembly

Each used variable-occurrence module has exactly one incidence of each color
that leaves the local variable gadget and meets its clause terminal.  The
particular triple depends on the connector kind:

* fixed red uses `bottomRight` for red and `auxiliary` for green and blue;
* fixed green uses `first` for green and `auxiliary` for red and blue;
* fixed blue uses `first` for blue and `auxiliary` for red and green.

This file names those three triples uniformly and proves their complete typed
references.  In particular, every routed reference names the clause terminal
selected by the source occurrence and has exactly the reversed source offset.
These equalities are the combinatorial half of the geometric splice.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Forget a routed-CNF incidence down to the tagged-literal representation
used to enumerate variable occurrence slots. -/
def incidenceTaggedOccurrence {Variable : Type*}
    (incidence : CNFIncidence Variable) :
    TaggedOccurrence Variable :=
  (incidence.literal, incidence.clauseIndex, incidence.literalIndex)

/-- CNF incidence metadata and exact-one variable slots enumerate the same
tagged source literals in the same clause-major order. -/
theorem incidencesWithMetadata_map_taggedOccurrence
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (PeriodicCNF.incidencesWithMetadata source).map
        incidenceTaggedOccurrence =
      PeriodicThreeSATThree.taggedLiterals source := by
  unfold PeriodicCNF.incidencesWithMetadata
    PeriodicThreeSATThree.taggedLiterals
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rw [List.map_map]
  rcases taggedClause with ⟨clause, clauseIndex⟩
  rfl

/-- Every tagged source occurrence has corresponding complete CNF incidence
metadata. -/
theorem exists_incidenceWithMetadata_of_tagged_mem
    {Variable : Type*} (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    ∃ incidence ∈ PeriodicCNF.incidencesWithMetadata source,
      incidenceTaggedOccurrence incidence = tagged := by
  rw [← incidencesWithMetadata_map_taggedOccurrence source]
    at taggedMember
  exact List.mem_map.mp taggedMember

/-- Every tagged source occurrence also has a stable flattened route index. -/
theorem exists_taggedIncidence_of_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    ∃ indexed :
        CNFIncidence Variable × Nat,
      indexed ∈
          (PeriodicCNF.incidencesWithMetadata source).zipIdx ∧
        incidenceTaggedOccurrence indexed.1 = tagged := by
  rcases exists_incidenceWithMetadata_of_tagged_mem
      source tagged taggedMember with
    ⟨incidence, incidenceMember, incidenceEq⟩
  let index :=
    (PeriodicCNF.incidencesWithMetadata source).idxOf incidence
  refine ⟨(incidence, index), ?_, incidenceEq⟩
  rw [List.mem_zipIdx_iff_getElem?]
  exact List.getElem?_idxOf incidenceMember

/-- The unique triple in one occurrence module whose selected colored
incidence leaves the variable gadget for the clause terminal. -/
def routedOccurrenceTriple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) : Triple Variable :=
  match occurrenceConnectorKind source atom slot, color with
  | .fixedRed, .red =>
      .fixedRed atom slot .bottomRight
  | .fixedRed, .green =>
      .fixedRed atom slot .auxiliary
  | .fixedRed, .blue =>
      .fixedRed atom slot .auxiliary
  | .fixedGreen, .red =>
      .ordinary atom slot .fixedGreen .auxiliary
  | .fixedGreen, .green =>
      .ordinary atom slot .fixedGreen .auxiliary
  | .fixedGreen, .blue =>
      .ordinary atom slot .fixedGreen .first
  | .fixedBlue, .red =>
      .ordinary atom slot .fixedBlue .auxiliary
  | .fixedBlue, .green =>
      .ordinary atom slot .fixedBlue .auxiliary
  | .fixedBlue, .blue =>
      .ordinary atom slot .fixedBlue .first

/-- Stable natural-number name of one routed variable-side triple. -/
def routedOccurrenceTripleIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) : Nat :=
  (triples source).idxOf
    (routedOccurrenceTriple source atom slot color)

/-- Stable natural-number name of the clause-terminal element reached by one
routed colored incidence. -/
def routedOccurrenceElementIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    WireColor → Nat
  | .red =>
      (redElements source).idxOf
        (redClauseTerminal source atom slot)
  | .green =>
      (greenElements source).idxOf
        (greenClauseTerminal source atom slot)
  | .blue =>
      (blueElements source).idxOf
        (blueClauseTerminal source atom slot)

/-- Numbered terminal reference corresponding to a routed typed incidence. -/
def routedOccurrenceReference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) : PeriodicThreeDMReference :=
  ⟨routedOccurrenceElementIndex source atom slot color,
    occurrenceReverseOffset source atom slot⟩

/-- Every routed colored triple belongs to its local occurrence block. -/
theorem routedOccurrenceTriple_mem_occurrenceTriples
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) :
    routedOccurrenceTriple source atom slot color ∈
      occurrenceTriples source atom slot := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases color <;>
    simp [routedOccurrenceTriple, occurrenceTriples, kindEq,
      allFixedRedTriples, allOrdinaryTriples]

/-- Every routed triple of a used occurrence is present in the complete
typed triple list. -/
theorem routedOccurrenceTriple_mem_triples
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (atomMember : atom ∈ occurringVariables source)
    (slotMember : slot ∈ usedSlots source atom)
    (color : WireColor) :
    routedOccurrenceTriple source atom slot color ∈
      triples source := by
  apply List.mem_append_left
  rw [variableTriples_eq_occurrenceEntries_flatMap]
  apply List.mem_flatMap.mpr
  exact
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩,
      routedOccurrenceTriple_mem_occurrenceTriples
        source atom slot color⟩

/-- The routed red incidence names the occurrence's red clause terminal at
the reversed source offset. -/
theorem routedOccurrenceTriple_red_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (tripleReferences source
      (routedOccurrenceTriple source atom slot .red)).red =
        ⟨redClauseTerminal source atom slot,
          occurrenceReverseOffset source atom slot⟩ := by
  cases kindEq :
      occurrenceConnectorKind source atom slot <;>
    simp [routedOccurrenceTriple, kindEq, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement]

/-- The routed green incidence names the occurrence's green clause terminal
at the reversed source offset. -/
theorem routedOccurrenceTriple_green_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (tripleReferences source
      (routedOccurrenceTriple source atom slot .green)).green =
        ⟨greenClauseTerminal source atom slot,
          occurrenceReverseOffset source atom slot⟩ := by
  cases kindEq :
      occurrenceConnectorKind source atom slot <;>
    simp [routedOccurrenceTriple, kindEq, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryGreenElement, fixedRedGreenElement]

/-- The routed blue incidence names the occurrence's blue clause terminal at
the reversed source offset. -/
theorem routedOccurrenceTriple_blue_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (tripleReferences source
      (routedOccurrenceTriple source atom slot .blue)).blue =
        ⟨blueClauseTerminal source atom slot,
          occurrenceReverseOffset source atom slot⟩ := by
  cases kindEq :
      occurrenceConnectorKind source atom slot <;>
    simp [routedOccurrenceTriple, kindEq, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryBlueElement, fixedRedBlueElement]

/-- Encoding a routed typed triple produces exactly the numbered terminal
reference above, for every color. -/
theorem encodeTriple_routedOccurrence_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) :
    ((problem source).encodeTriple
      (routedOccurrenceTriple source atom slot color)).reference color =
        routedOccurrenceReference source atom slot color := by
  cases color with
  | red =>
      change
        encodeReference (redElements source)
            (tripleReferences source
              (routedOccurrenceTriple source atom slot .red)).red =
          ⟨(redElements source).idxOf
              (redClauseTerminal source atom slot),
            occurrenceReverseOffset source atom slot⟩
      rw [show
        (tripleReferences source
          (routedOccurrenceTriple source atom slot .red)).red =
            ⟨redClauseTerminal source atom slot,
              occurrenceReverseOffset source atom slot⟩ from
        routedOccurrenceTriple_red_reference source atom slot]
      rfl
  | green =>
      change
        encodeReference (greenElements source)
            (tripleReferences source
              (routedOccurrenceTriple source atom slot .green)).green =
          ⟨(greenElements source).idxOf
              (greenClauseTerminal source atom slot),
            occurrenceReverseOffset source atom slot⟩
      rw [show
        (tripleReferences source
          (routedOccurrenceTriple source atom slot .green)).green =
            ⟨greenClauseTerminal source atom slot,
              occurrenceReverseOffset source atom slot⟩ from
        routedOccurrenceTriple_green_reference source atom slot]
      rfl
  | blue =>
      change
        encodeReference (blueElements source)
            (tripleReferences source
              (routedOccurrenceTriple source atom slot .blue)).blue =
          ⟨(blueElements source).idxOf
              (blueClauseTerminal source atom slot),
            occurrenceReverseOffset source atom slot⟩
      rw [show
        (tripleReferences source
          (routedOccurrenceTriple source atom slot .blue)).blue =
            ⟨blueClauseTerminal source atom slot,
              occurrenceReverseOffset source atom slot⟩ from
        routedOccurrenceTriple_blue_reference source atom slot]
      rfl

/-- A routed triple belonging to a used occurrence has an in-range encoded
triple index. -/
theorem routedOccurrenceTripleIndex_lt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (atomMember : atom ∈ occurringVariables source)
    (slotMember : slot ∈ usedSlots source atom)
    (color : WireColor) :
    routedOccurrenceTripleIndex source atom slot color <
      (encodedProblem source).triples.length := by
  simpa [routedOccurrenceTripleIndex, encodedProblem,
    TypedProblem.encode, problem] using
    List.idxOf_lt_length_iff.mpr
      (routedOccurrenceTriple_mem_triples
        source atom slot atomMember slotMember color)

/-- Retrieving the encoded problem at a routed triple's stable index gives
the encoding of that exact typed triple. -/
theorem encodedProblem_routedOccurrenceTriple_getD
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (atomMember : atom ∈ occurringVariables source)
    (slotMember : slot ∈ usedSlots source atom)
    (color : WireColor) :
    (encodedProblem source).triples.getD
        (routedOccurrenceTripleIndex source atom slot color) default =
      (problem source).encodeTriple
        (routedOccurrenceTriple source atom slot color) := by
  have member :=
    routedOccurrenceTriple_mem_triples
      source atom slot atomMember slotMember color
  have lookup :=
    List.getElem?_eq_some_iff.mp (List.getElem?_idxOf member)
  have indexLt :=
    routedOccurrenceTripleIndex_lt
      source atom slot atomMember slotMember color
  rw [List.getD_eq_getElem _ _ indexLt]
  simp only [encodedProblem, TypedProblem.encode,
    List.getElem_map]
  congr 1
  exact lookup.2

/-- Looking up an actual occurrence recovers its literal's reversed offset. -/
theorem occurrenceReverseOffset_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrenceReverseOffset source atom slot =
      PeriodicOneInThreeToThreeDM.reverseOffset tagged.1.offset := by
  simp [occurrenceReverseOffset, lookup]

/-- Looking up an actual occurrence recovers its clause index. -/
theorem occurrenceClauseIndex_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrenceClauseIndex source atom slot = tagged.2.1 := by
  simp [occurrenceClauseIndex, lookup]

/-- Looking up an actual occurrence recovers its literal index. -/
theorem occurrenceLiteralIndex_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrenceLiteralIndex source atom slot = tagged.2.2 := by
  simp [occurrenceLiteralIndex, lookup]

/-- Looking up an actual occurrence recovers its literal polarity. -/
theorem occurrencePolarity_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrencePolarity source atom slot = tagged.1.value := by
  simp [occurrencePolarity, lookup]

/-- A used occurrence slot determines the exact source-incidence metadata and
stable route index that its three colored terminal incidences must follow. -/
theorem exists_taggedIncidence_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    ∃ indexed :
        CNFIncidence Variable × Nat,
      indexed ∈
          (PeriodicCNF.incidencesWithMetadata source).zipIdx ∧
        incidenceTaggedOccurrence indexed.1 = tagged := by
  exact exists_taggedIncidence_of_tagged_mem source tagged
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup).1

/-- A used occurrence entry recovers one certified variable-to-clause route
with endpoints stated directly in the tagged-occurrence language used by the
typed 3DM assembly.  Its three colored terminal references all carry the
same reversed offset as that route. -/
theorem routedOccurrenceSplice
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.PlanarIncidencePresentation placement)
    (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source.erase) :
    ∃ tagged : TaggedOccurrence Variable,
      ∃ indexed : CNFIncidence Variable × Nat,
        ∃ positionedClause : PositionedPeriodicClause Variable,
          occurrenceAt source.erase entry.1 entry.2 = some tagged ∧
          indexed ∈
            (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx ∧
          incidenceTaggedOccurrence indexed.1 = tagged ∧
          (positionedClause, indexed.1.clauseIndex) ∈
            source.clauses.zipIdx ∧
          (presentation.variableToClauseRoute indexed.1).head? =
            some (placement.position tagged.1.atom) ∧
          (presentation.variableToClauseRoute indexed.1).getLast? =
            some (PositionedPeriodicCNF.variableToClauseTarget
              placement positionedClause tagged.1) ∧
          ∀ color,
            (routedOccurrenceReference
              source.erase entry.1 entry.2 color).offset =
              PeriodicOneInThreeToThreeDM.reverseOffset
                tagged.1.offset := by
  rcases occurrenceAt_exists_of_entry_mem
      source.erase entry entryMember with
    ⟨tagged, lookup⟩
  rcases exists_taggedIncidence_of_occurrenceAt
      source.erase entry.1 entry.2 tagged lookup with
    ⟨indexed, indexedMember, metadataEq⟩
  rcases presentation.variableToClauseRoute_endpoints
      indexedMember with
    ⟨positionedClause, literal, clauseMember, literalMember,
      incidenceEq, routeHead, routeLast⟩
  have indexedLiteralEq :
      indexed.1.literal = tagged.1 :=
    congrArg Prod.fst metadataEq
  have endpointLiteralEq : literal = tagged.1 := by
    have fromIncidence :=
      congrArg CNFIncidence.literal incidenceEq
    exact fromIncidence.symm.trans indexedLiteralEq
  subst literal
  refine
    ⟨tagged, indexed, positionedClause, lookup,
      indexedMember, metadataEq, clauseMember, ?_, ?_, ?_⟩
  · simpa [indexedLiteralEq] using routeHead
  · simpa [indexedLiteralEq] using routeLast
  · intro color
    exact occurrenceReverseOffset_of_occurrenceAt
      source.erase entry.1 entry.2 tagged lookup

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
