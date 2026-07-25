import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTerminalOccurrenceCounts

/-!
# Variable-side incidences at clause terminals

Each assembled occurrence module contributes exactly one incidence of each
color to the clause terminal selected by its tagged clause/literal position.
This file proves that the global variable-side incidence count at a terminal
is exactly the corresponding assembled occurrence count.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/-- Whether one triple's reference of the selected color names a target
clause terminal. -/
def terminalReferenceMatches {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (color : WireColor)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup)
    (triple : Triple Variable) : Bool :=
  let references := tripleReferences source triple
  match color with
  | .red =>
      references.red.atom ==
        RedElement.clauseTerminal clauseIndex group
  | .green =>
      references.green.atom ==
        GreenElement.clauseTerminal clauseIndex group
  | .blue =>
      references.blue.atom ==
        BlueElement.clauseTerminal clauseIndex group

/-- Offset of the selected colored reference. -/
def terminalReferenceOffset {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (color : WireColor)
    (triple : Triple Variable) : Cell :=
  let references := tripleReferences source triple
  match color with
  | .red => references.red.offset
  | .green => references.green.offset
  | .blue => references.blue.offset

/-- Variable-module incidences at one target colored terminal. -/
def variableTerminalIncidences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    List (Incidence Variable) :=
  (variableTriples source).filterMap fun triple =>
    if terminalReferenceMatches
        source color clauseIndex group triple then
      some ⟨triple, terminalReferenceOffset source color triple⟩
    else none

/- One listed module contributes one RGB incidence precisely when its
tagged occurrence belongs to the target clause terminal. -/
set_option maxHeartbeats 800000 in
theorem occurrenceBlock_terminalIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    ((occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
      if terminalReferenceMatches
          source color clauseIndex group triple then
        some
          (⟨triple, terminalReferenceOffset source color triple⟩ :
            Incidence Variable)
      else none).length =
      (((occurrenceAt source entry.1 entry.2).toList.filter fun tagged =>
        tagged.2.1 = clauseIndex ∧
          terminalGroupOfLiteralIndex tagged.2.2 = group).length) := by
  rcases occurrenceAt_exists_of_entry_mem
      source entry entryMember with ⟨tagged, lookup⟩
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
          occurrenceLiteralIndex]
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
          occurrenceLiteralIndex]
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
          occurrenceLiteralIndex]

/-- A generic list of listed occurrence entries has the same terminal
incidence count as its tagged-occurrence output. -/
theorem occurrenceEntries_terminalIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entries : List (Variable × OccurrenceSlot))
    (entriesSubset :
      ∀ entry ∈ entries, entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    (((entries.flatMap fun entry =>
      occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
        if terminalReferenceMatches
            source color clauseIndex group triple then
          some
            (⟨triple, terminalReferenceOffset source color triple⟩ :
              Incidence Variable)
        else none).length) =
      (((entries.filterMap fun entry =>
        occurrenceAt source entry.1 entry.2).filter fun tagged =>
          tagged.2.1 = clauseIndex ∧
            terminalGroupOfLiteralIndex tagged.2.2 = group).length) := by
  induction entries with
  | nil => rfl
  | cons entry rest induction =>
      have entryMember := entriesSubset entry (by simp)
      have restSubset :
          ∀ current ∈ rest, current ∈ occurrenceEntries source :=
        fun current currentMember =>
          entriesSubset current (by simp [currentMember])
      rw [List.flatMap_cons, List.filterMap_append,
        List.length_append,
        occurrenceBlock_terminalIncidences_length
          source entry entryMember color clauseIndex group,
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
          · simp [lookup, terminalMatch, Nat.add_comm]
          · simp [lookup, terminalMatch]

/-- Variable-side RGB terminal incidence counts are exactly the assembled
terminal occurrence counts. -/
theorem variableTerminalIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    (variableTerminalIncidences
      source color clauseIndex group).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length := by
  unfold variableTerminalIncidences terminalOccurrenceEnumeration
    occurrenceEnumeration
  rw [variableTriples_eq_occurrenceEntries_flatMap]
  exact occurrenceEntries_terminalIncidences_length
    source (occurrenceEntries source) (by simp)
      color clauseIndex group

/-- The ordinary color-specific filters agree with the common RGB
enumerator. -/
theorem variableTriples_redTerminal_filterMap_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup) :
    ((variableTriples source).filterMap fun triple =>
      let reference := (tripleReferences source triple).red
      if reference.atom =
          RedElement.clauseTerminal clauseIndex group then
        some (⟨triple, reference.offset⟩ : Incidence Variable)
      else none).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length := by
  simpa [variableTerminalIncidences, terminalReferenceMatches,
    terminalReferenceOffset] using
      variableTerminalIncidences_length
        source .red clauseIndex group

theorem variableTriples_greenTerminal_filterMap_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup) :
    ((variableTriples source).filterMap fun triple =>
      let reference := (tripleReferences source triple).green
      if reference.atom =
          GreenElement.clauseTerminal clauseIndex group then
        some (⟨triple, reference.offset⟩ : Incidence Variable)
      else none).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length := by
  simpa [variableTerminalIncidences, terminalReferenceMatches,
    terminalReferenceOffset] using
      variableTerminalIncidences_length
        source .green clauseIndex group

theorem variableTriples_blueTerminal_filterMap_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup) :
    ((variableTriples source).filterMap fun triple =>
      let reference := (tripleReferences source triple).blue
      if reference.atom =
          BlueElement.clauseTerminal clauseIndex group then
        some (⟨triple, reference.offset⟩ : Incidence Variable)
      else none).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length := by
  simpa [variableTerminalIncidences, terminalReferenceMatches,
    terminalReferenceOffset] using
      variableTerminalIncidences_length
        source .blue clauseIndex group

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
