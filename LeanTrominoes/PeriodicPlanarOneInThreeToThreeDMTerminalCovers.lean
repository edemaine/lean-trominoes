import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTerminalValues

/-!
# Exact cover of merged clause terminals

Each colored clause-terminal element merges a zero-or-one variable-side
occurrence incidence with its two local Figure 5 incidences.  The canonical
matching covers that merged element exactly once: used terminals reproduce
the clause core's external Boolean, while the unused right terminal of a
binary clause contributes no variable incidence and has external value
`false`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/-- Color-uniform access to an assembled clause terminal's incidences. -/
def problemTerminalIncidences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    List (Incidence Variable) :=
  match color with
  | .red =>
      (problem source).redIncidences
        (.clauseTerminal clauseIndex group)
  | .green =>
      (problem source).greenIncidences
        (.clauseTerminal clauseIndex group)
  | .blue =>
      (problem source).blueIncidences
        (.clauseTerminal clauseIndex group)

/-- A colored terminal's global incidence list is its variable-side list
followed by its two clause-core neighbors. -/
theorem problemTerminalIncidences_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (color : WireColor) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    problemTerminalIncidences source color clauseIndex group =
      variableTerminalIncidences source color clauseIndex group ++
        ((terminalElementForColor color group).neighbors).map fun set =>
          ⟨.clause clauseIndex set, (0, 0)⟩ := by
  cases color with
  | red =>
      change
        (triples source).filterMap
            (fun triple =>
              let reference := (tripleReferences source triple).red
              if reference.atom =
                  RedElement.clauseTerminal clauseIndex group then
                some (⟨triple, reference.offset⟩ : Incidence Variable)
              else none) = _
      rw [triples, List.filterMap_append]
      congr 1
      · simp [variableTerminalIncidences,
          terminalReferenceMatches, terminalReferenceOffset]
      · simpa [terminalReferenceMatches,
          terminalReferenceOffset] using
            clauseTerminalIncidences
              source .red clauseIndex indexLt group
  | green =>
      change
        (triples source).filterMap
            (fun triple =>
              let reference := (tripleReferences source triple).green
              if reference.atom =
                  GreenElement.clauseTerminal clauseIndex group then
                some (⟨triple, reference.offset⟩ : Incidence Variable)
              else none) = _
      rw [triples, List.filterMap_append]
      congr 1
      · simp [variableTerminalIncidences,
          terminalReferenceMatches, terminalReferenceOffset]
      · simpa [terminalReferenceMatches,
          terminalReferenceOffset] using
            clauseTerminalIncidences
              source .green clauseIndex indexLt group
  | blue =>
      change
        (triples source).filterMap
            (fun triple =>
              let reference := (tripleReferences source triple).blue
              if reference.atom =
                  BlueElement.clauseTerminal clauseIndex group then
                some (⟨triple, reference.offset⟩ : Incidence Variable)
              else none) = _
      rw [triples, List.filterMap_append]
      congr 1
      · simp [variableTerminalIncidences,
          terminalReferenceMatches, terminalReferenceOffset]
      · simpa [terminalReferenceMatches,
          terminalReferenceOffset] using
            clauseTerminalIncidences
              source .blue clauseIndex indexLt group

/-- Occurrence-order terminal truth values are a permutation of one copy of
the terminal signal, except at the unused right terminal of a binary clause,
where the list is empty. -/
theorem terminalOccurrenceValues_perm_signal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    List.Perm
      ((terminalOccurrenceEnumeration
        source clauseIndex group).map fun tagged =>
          PeriodicOneInThree.literalTruth assignment cell tagged.1)
      (if clause.length = 2 ∧ group = .right then []
        else
          [sourceTerminalSignal
            source assignment cell clauseIndex group]) := by
  have occurrencePermutation :=
    (terminalOccurrenceEnumeration_perm_source
      source occurrences clauseIndex group).trans
        (sourceTerminalOccurrences_perm_taggedClause_filter
          source clauseIndex clause clauseLookup group)
  have permutation :=
    occurrencePermutation.map
      (fun tagged : TaggedOccurrence Variable =>
        PeriodicOneInThree.literalTruth assignment cell tagged.1)
  rcases arity with lengthTwo | lengthThree
  · rcases List.length_eq_two.mp lengthTwo with
      ⟨first, second, rfl⟩
    cases group <;>
      simpa [PeriodicOneInThreeToThreeDM.taggedClauseOccurrences,
        terminalGroupOfLiteralIndex, sourceTerminalSignal,
        literalAt, literalIndexOfTerminalGroup, clauseLookup] using
          permutation
  · rcases List.length_eq_three.mp lengthThree with
      ⟨first, second, third, rfl⟩
    cases group <;>
      simpa [PeriodicOneInThreeToThreeDM.taggedClauseOccurrences,
        terminalGroupOfLiteralIndex, sourceTerminalSignal,
        literalAt, literalIndexOfTerminalGroup, clauseLookup] using
          permutation

/-- Canonical values on a colored terminal decompose into source occurrence
values followed by the two local clause-core values. -/
theorem problemTerminalIncidentValues_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (color : WireColor) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    ((problemTerminalIncidences
      source color clauseIndex group).map (fun incidence =>
        (problem source).incidenceValue
          (matchingOfAssignment source assignment) incidence cell)) =
      ((terminalOccurrenceEnumeration
        source clauseIndex group).map (fun tagged =>
          PeriodicOneInThree.literalTruth assignment cell tagged.1)) ++
        ((terminalElementForColor color group).neighbors).map (fun set =>
          matchingOfAssignment source assignment
            (.clause clauseIndex set) cell) := by
  rw [problemTerminalIncidences_eq
      source color clauseIndex indexLt group,
    List.map_append, variableTerminalIncidentValues]
  simp [TypedProblem.incidenceValue, Cell.sub]

/-- Every colored terminal of a satisfied source clause is covered exactly
once by the canonical assembled matching. -/
theorem matchingOfAssignment_covers_terminal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment cell clause)
    (color : WireColor) (group : X3CClauseTerminalGroup) :
    PeriodicOneInThree.ExactlyOne
      ((problemTerminalIncidences
        source color clauseIndex group).map fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment) incidence cell) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  rw [problemTerminalIncidentValues_eq
    source assignment color clauseIndex indexLt group cell]
  let terminal := terminalElementForColor color group
  let localValues :=
    terminal.neighbors.map fun set =>
      matchingOfAssignment source assignment
        (.clause clauseIndex set) cell
  have coreHolds :=
    matchingOfAssignment_clause_holds
      source assignment cell clauseIndex
      (sourceTerminalSignals_exactlyOne source assignment cell
        clauseIndex clause clauseLookup arity sourceHolds)
  have terminalExact := coreHolds.2 group terminal.slot
  have terminalEq :
      (⟨group, terminal.slot⟩ : X3CClauseTerminal) = terminal := by
    cases color <;> cases group <;> rfl
  have externalEq :
      x3cClauseExternalAssignment
          (sourceTerminalSignal source assignment cell
            clauseIndex .top)
          (sourceTerminalSignal source assignment cell
            clauseIndex .left)
          (sourceTerminalSignal source assignment cell
            clauseIndex .right) group =
        sourceTerminalSignal source assignment cell
          clauseIndex group := by
    cases group <;> rfl
  change PeriodicOneInThree.ExactlyOne
    (_ ++ localValues)
  change PeriodicOneInThree.ExactlyOne
    (x3cClauseExternalAssignment
        (sourceTerminalSignal source assignment cell clauseIndex .top)
        (sourceTerminalSignal source assignment cell clauseIndex .left)
        (sourceTerminalSignal source assignment cell clauseIndex .right)
        group ::
      (⟨group, terminal.slot⟩ :
        X3CClauseTerminal).neighbors.map fun set =>
          matchingOfAssignment source assignment
            (.clause clauseIndex set) cell) at terminalExact
  rw [terminalEq, externalEq] at terminalExact
  change PeriodicOneInThree.ExactlyOne
    (sourceTerminalSignal source assignment cell clauseIndex group ::
      localValues) at terminalExact
  have occurrencePermutation :=
    terminalOccurrenceValues_perm_signal
      source occurrences assignment cell clauseIndex clause
        clauseLookup arity group
  by_cases unused : clause.length = 2 ∧ group = .right
  · rw [if_pos unused] at occurrencePermutation
    have occurrenceValuesNil :
        (terminalOccurrenceEnumeration
          source clauseIndex group).map (fun tagged =>
            PeriodicOneInThree.literalTruth
              assignment cell tagged.1) = [] := by
      simpa using occurrencePermutation
    rw [occurrenceValuesNil]
    rcases unused with ⟨lengthTwo, rfl⟩
    rcases List.length_eq_two.mp lengthTwo with
      ⟨first, second, rfl⟩
    simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup, clauseLookup,
      PeriodicOneInThree.ExactlyOne,
      List.count_cons] using terminalExact
  · rw [if_neg unused] at occurrencePermutation
    exact
      (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
        (occurrencePermutation.append_right localValues)).mpr
          terminalExact

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
