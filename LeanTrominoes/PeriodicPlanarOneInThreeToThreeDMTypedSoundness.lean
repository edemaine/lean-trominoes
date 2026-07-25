import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTypedCompleteness
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMMatchingTerminalValues

/-!
# Soundness of the typed planar periodic 3DM assembly

An arbitrary perfect matching determines a common Boolean phase around
each variable cycle.  The selected variable-side incidence at every used
clause terminal therefore carries the corresponding recovered source
literal.  Combining that value with the two incident Figure 5 sets turns
the global terminal covers into a valid clause-core cover, which forces
exactly one source literal to be true.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/-- Values at a merged terminal split into the recovered source-occurrence
values followed by the two local clause-core selections. -/
theorem problemTerminalIncidentValues_ofMatching_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (color : WireColor) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    ((problemTerminalIncidences
      source color clauseIndex group).map (fun incidence =>
        (problem source).incidenceValue matching incidence cell)) =
      ((terminalOccurrenceEnumeration
        source clauseIndex group).map (fun tagged =>
          PeriodicOneInThree.literalTruth
            (assignmentOfMatching source matching) cell tagged.1)) ++
        ((terminalElementForColor color group).neighbors).map (fun set =>
          matching (.clause clauseIndex set) cell) := by
  rw [problemTerminalIncidences_eq
      source color clauseIndex indexLt group,
    List.map_append,
    variableTerminalIncidentValues_ofMatching
      source matching satisfies]
  simp [TypedProblem.incidenceValue, Cell.sub]

/-- Exact cover of a merged colored terminal becomes the clause-core
terminal constraint with the recovered source signal as its external
value. -/
theorem terminal_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (color : WireColor) (group : X3CClauseTerminalGroup) :
    PeriodicOneInThree.ExactlyOne
      (sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex group ::
        ((terminalElementForColor color group).neighbors).map
          (fun set => matching (.clause clauseIndex set) cell)) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  have terminalCovered :
      PeriodicOneInThree.ExactlyOne
        ((problemTerminalIncidences
          source color clauseIndex group).map (fun incidence =>
            (problem source).incidenceValue matching incidence cell)) := by
    cases color with
    | red =>
        exact satisfies.1 (.clauseTerminal clauseIndex group)
          (by
            change RedElement.clauseTerminal clauseIndex group ∈
              redElements source
            simpa [clauseRedElement] using
              clauseRedElement_mem source clauseIndex indexLt
                (.terminal ⟨group, .first⟩))
          cell
    | green =>
        exact satisfies.2.1 (.clauseTerminal clauseIndex group)
          (by
            change GreenElement.clauseTerminal clauseIndex group ∈
              greenElements source
            simpa [clauseGreenElement] using
              clauseGreenElement_mem source clauseIndex indexLt
                (.terminal ⟨group, .first⟩))
          cell
    | blue =>
        exact satisfies.2.2 (.clauseTerminal clauseIndex group)
          (by
            change BlueElement.clauseTerminal clauseIndex group ∈
              blueElements source
            simpa [clauseBlueElement] using
              clauseBlueElement_mem source clauseIndex indexLt
                (.terminal ⟨group, .first⟩))
          cell
  rw [problemTerminalIncidentValues_ofMatching_eq
    source matching satisfies color clauseIndex indexLt group cell] at terminalCovered
  let localValues :=
    ((terminalElementForColor color group).neighbors).map
      (fun set => matching (.clause clauseIndex set) cell)
  have occurrencePermutation :=
    terminalOccurrenceValues_perm_signal
      source occurrences (assignmentOfMatching source matching)
        cell clauseIndex clause clauseLookup arity group
  by_cases unused : clause.length = 2 ∧ group = .right
  · rw [if_pos unused] at occurrencePermutation
    have occurrenceValuesNil :
        (terminalOccurrenceEnumeration
          source clauseIndex group).map (fun tagged =>
            PeriodicOneInThree.literalTruth
              (assignmentOfMatching source matching)
              cell tagged.1) = [] := by
      simpa using occurrencePermutation
    rw [occurrenceValuesNil] at terminalCovered
    rcases unused with ⟨lengthTwo, rfl⟩
    rcases List.length_eq_two.mp lengthTwo with
      ⟨first, second, rfl⟩
    simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup, clauseLookup,
      PeriodicOneInThree.ExactlyOne,
      List.count_cons] using terminalCovered
  · rw [if_neg unused] at occurrencePermutation
    exact
      (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
        (occurrencePermutation.append_right localValues)).mp
          terminalCovered

/-- The nine terminal covers and three internal covers of one clause block
form a valid Figure 5 clause-core matching with the recovered source signals
on its boundary. -/
theorem clauseCore_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3) :
    X3CClauseCoreHolds
      (fun set => matching (.clause clauseIndex set) cell)
      (x3cClauseExternalAssignment
        (sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .top)
        (sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .left)
        (sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .right)) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  constructor
  · exact clauseInternal_holds_of_satisfies
      source matching satisfies clauseIndex indexLt cell
  · intro group slot
    let terminal : X3CClauseTerminal := ⟨group, slot⟩
    have terminalHolds :=
      terminal_holds_of_satisfies
        source occurrences matching satisfies cell clauseIndex
          clause clauseLookup arity terminal.color group
    have terminalEq :
        terminalElementForColor terminal.color group = terminal := by
      cases group <;> cases slot <;> rfl
    have externalEq :
        x3cClauseExternalAssignment
            (sourceTerminalSignal source
              (assignmentOfMatching source matching)
              cell clauseIndex .top)
            (sourceTerminalSignal source
              (assignmentOfMatching source matching)
              cell clauseIndex .left)
            (sourceTerminalSignal source
              (assignmentOfMatching source matching)
              cell clauseIndex .right)
            group =
          sourceTerminalSignal source
            (assignmentOfMatching source matching)
            cell clauseIndex group := by
      cases group <;> rfl
    change PeriodicOneInThree.ExactlyOne
      (x3cClauseExternalAssignment
          (sourceTerminalSignal source
            (assignmentOfMatching source matching)
            cell clauseIndex .top)
          (sourceTerminalSignal source
            (assignmentOfMatching source matching)
            cell clauseIndex .left)
          (sourceTerminalSignal source
            (assignmentOfMatching source matching)
            cell clauseIndex .right)
          group ::
        terminal.neighbors.map
          (fun set => matching (.clause clauseIndex set) cell))
    rw [externalEq, ← terminalEq]
    exact terminalHolds

/-- A global perfect matching forces exactly one of the recovered source
signals at every binary or ternary clause to be true. -/
theorem sourceTerminalSignals_exactlyOne_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3) :
    PeriodicOneInThree.ExactlyOne
      [sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .top,
        sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .left,
        sourceTerminalSignal source
          (assignmentOfMatching source matching)
          cell clauseIndex .right] := by
  let external :=
    x3cClauseExternalAssignment
      (sourceTerminalSignal source
        (assignmentOfMatching source matching)
        cell clauseIndex .top)
      (sourceTerminalSignal source
        (assignmentOfMatching source matching)
        cell clauseIndex .left)
      (sourceTerminalSignal source
        (assignmentOfMatching source matching)
        cell clauseIndex .right)
  have coreExists :
      ∃ selected : X3CClauseSet → Bool,
        X3CClauseCoreHolds selected external :=
    ⟨fun set => matching (.clause clauseIndex set) cell,
      clauseCore_holds_of_satisfies
        source occurrences matching satisfies cell clauseIndex
          clause clauseLookup arity⟩
  simpa [external, x3cClauseExternalAssignment] using
    (exists_x3cClauseCoreHolds_iff external).mp coreExists

/-- Conversely to `sourceTerminalSignals_exactlyOne`, exact-one of the
three source-terminal signals is the original binary or ternary source
clause. -/
theorem sourceClause_holds_of_terminalSignals_exactlyOne
    {Variable : Type*} (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (terminalHolds :
      PeriodicOneInThree.ExactlyOne
        [sourceTerminalSignal source assignment
            cell clauseIndex .top,
          sourceTerminalSignal source assignment
            cell clauseIndex .left,
          sourceTerminalSignal source assignment
            cell clauseIndex .right]) :
    PeriodicOneInThree.ClauseHolds assignment cell clause := by
  rcases clause with _ | ⟨first, tail⟩
  · simp at arity
  rcases tail with _ | ⟨second, tail⟩
  · simp at arity
  rcases tail with _ | ⟨third, tail⟩
  · simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup,
      PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.literalTruth,
      PeriodicOneInThree.ExactlyOne,
      List.count_cons,
      clauseLookup] using terminalHolds
  · have tailEmpty : tail = [] := by
      have tailLength : tail.length = 0 := by
        rcases arity with lengthTwo | lengthThree
        · simp at lengthTwo
        · simpa using lengthThree
      exact List.length_eq_zero_iff.mp tailLength
    subst tail
    simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup,
      PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.literalTruth,
      PeriodicOneInThree.ExactlyOne,
      clauseLookup] using terminalHolds

/-- Every perfect matching of the typed planar assembly yields a satisfying
assignment of the source exact-one instance. -/
theorem assignmentOfMatching_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (matching : (problem source).MatchingAssignment)
    (matchingSatisfies : (problem source).Satisfies matching) :
    PeriodicOneInThree.Satisfies source
      (assignmentOfMatching source matching) := by
  intro cell clause clauseMember
  rcases List.mem_iff_getElem?.mp clauseMember with
    ⟨clauseIndex, clauseLookup⟩
  have clauseArity := arity clause clauseMember
  exact sourceClause_holds_of_terminalSignals_exactlyOne
    source (assignmentOfMatching source matching)
      cell clauseIndex clause clauseLookup clauseArity
      (sourceTerminalSignals_exactlyOne_of_satisfies
        source occurrences matching matchingSatisfies
          cell clauseIndex clause clauseLookup clauseArity)

/-- Typed planar periodic 3DM satisfiability implies source exact-one
satisfiability. -/
theorem source_satisfiable_of_problem_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (problemSatisfiable : (problem source).Satisfiable) :
    PeriodicOneInThree.Satisfiable source := by
  rcases problemSatisfiable with ⟨matching, satisfies⟩
  exact
    ⟨assignmentOfMatching source matching,
      assignmentOfMatching_satisfies
        source occurrences arity matching satisfies⟩

/-- The assembled typed planar 3DM presentation is satisfiable exactly when
its occurrence-three, binary-or-ternary exact-one source is satisfiable. -/
theorem problem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (problem source).Satisfiable ↔
      PeriodicOneInThree.Satisfiable source := by
  constructor
  · exact source_satisfiable_of_problem_satisfiable
      source occurrences arity
  · exact problem_satisfiable_of_source_satisfiable
      source occurrences arity

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
