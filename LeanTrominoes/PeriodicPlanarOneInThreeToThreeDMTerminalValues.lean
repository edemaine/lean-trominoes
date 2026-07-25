import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseSignals

/-!
# Canonical matching values at variable-side clause terminals

The variable-side RGB incidence contributed by a genuine occurrence is
selected exactly when that source literal is true.  This file strengthens
the earlier terminal incidence count to an equality of complete Boolean
value lists.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/- One listed occurrence module contributes its source literal truth value
precisely when it belongs to the requested clause terminal. -/
set_option maxHeartbeats 800000 in
theorem occurrenceBlock_terminalIncidentValues
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    (((occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
      if terminalReferenceMatches
          source color clauseIndex group triple then
        some
          (⟨triple, terminalReferenceOffset source color triple⟩ :
            Incidence Variable)
      else none).map fun incidence =>
        (problem source).incidenceValue
          (matchingOfAssignment source assignment) incidence cell) =
      (((occurrenceAt source entry.1 entry.2).toList.filter fun tagged =>
        tagged.2.1 = clauseIndex ∧
          terminalGroupOfLiteralIndex tagged.2.2 = group).map fun tagged =>
            PeriodicOneInThree.literalTruth assignment cell tagged.1) := by
  rcases occurrenceAt_exists_of_entry_mem
      source entry entryMember with ⟨tagged, lookup⟩
  have atomEq :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source entry.1 entry.2 tagged lookup).2
  by_cases clauseEq : tagged.2.1 = clauseIndex <;>
    by_cases groupEq :
      terminalGroupOfLiteralIndex tagged.2.2 = group <;>
    cases color with
    | red =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, terminalReferenceMatches,
          terminalReferenceOffset, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryRedElement, fixedRedRedElement,
          redClauseTerminal, occurrenceClauseIndex,
          occurrenceLiteralIndex, TypedProblem.incidenceValue,
          matchingOfAssignment, occurrenceSignal, occurrencePolarity,
          variableConnectorLiteralSignal,
          variableOccurrenceSelection, fixedRedConnectorSelection,
          PeriodicOneInThree.literalTruth]
    | green =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, terminalReferenceMatches,
          terminalReferenceOffset, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryGreenElement, fixedRedGreenElement,
          greenClauseTerminal, occurrenceClauseIndex,
          occurrenceLiteralIndex, TypedProblem.incidenceValue,
          matchingOfAssignment, occurrenceSignal, occurrencePolarity,
          variableConnectorLiteralSignal,
          variableOccurrenceSelection, fixedRedConnectorSelection,
          PeriodicOneInThree.literalTruth]
    | blue =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, terminalReferenceMatches,
          terminalReferenceOffset, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryBlueElement, fixedRedBlueElement,
          blueClauseTerminal, occurrenceClauseIndex,
          occurrenceLiteralIndex, TypedProblem.incidenceValue,
          matchingOfAssignment, occurrenceSignal, occurrencePolarity,
          variableConnectorLiteralSignal,
          variableOccurrenceSelection, fixedRedConnectorSelection,
          PeriodicOneInThree.literalTruth]

/-- The value-list correspondence extends over any sublist of occurrence
entries. -/
theorem occurrenceEntries_terminalIncidentValues
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (entries : List (Variable × OccurrenceSlot))
    (entriesSubset :
      ∀ entry ∈ entries, entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    (((entries.flatMap fun entry =>
      occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
        if terminalReferenceMatches
            source color clauseIndex group triple then
          some
            (⟨triple, terminalReferenceOffset source color triple⟩ :
              Incidence Variable)
        else none).map (fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment) incidence cell)) =
      (((entries.filterMap fun entry =>
        occurrenceAt source entry.1 entry.2).filter fun tagged =>
          tagged.2.1 = clauseIndex ∧
            terminalGroupOfLiteralIndex tagged.2.2 = group).map
              (fun tagged =>
                PeriodicOneInThree.literalTruth
                  assignment cell tagged.1)) := by
  induction entries with
  | nil => rfl
  | cons entry rest induction =>
      have entryMember := entriesSubset entry (by simp)
      have restSubset :
          ∀ current ∈ rest, current ∈ occurrenceEntries source :=
        fun current currentMember =>
          entriesSubset current (by simp [currentMember])
      rw [List.flatMap_cons, List.filterMap_append, List.map_append,
        occurrenceBlock_terminalIncidentValues
          source assignment entry entryMember color clauseIndex group cell,
        induction restSubset]
      cases lookup : occurrenceAt source entry.1 entry.2 with
      | none =>
          rcases occurrenceAt_exists_of_entry_mem
              source entry entryMember with ⟨tagged, taggedLookup⟩
          rw [lookup] at taggedLookup
          contradiction
      | some tagged =>
          by_cases terminalMatch :
              tagged.2.1 = clauseIndex ∧
                terminalGroupOfLiteralIndex tagged.2.2 = group
          · simp [lookup, terminalMatch]
          · simp [lookup, terminalMatch]

/-- In the canonical matching, all variable-side incidences at one colored
terminal enumerate exactly the corresponding source literal truth values. -/
theorem variableTerminalIncidentValues
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    ((variableTerminalIncidences
      source color clauseIndex group).map (fun incidence =>
        (problem source).incidenceValue
          (matchingOfAssignment source assignment) incidence cell)) =
      (terminalOccurrenceEnumeration
        source clauseIndex group).map (fun tagged =>
          PeriodicOneInThree.literalTruth assignment cell tagged.1) := by
  unfold variableTerminalIncidences terminalOccurrenceEnumeration
    occurrenceEnumeration
  rw [variableTriples_eq_occurrenceEntries_flatMap]
  exact occurrenceEntries_terminalIncidentValues
    source assignment (occurrenceEntries source) (by simp)
      color clauseIndex group cell

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
