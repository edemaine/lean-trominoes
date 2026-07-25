import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableTerminalIncidences

/-!
# Clause-side incidences at clause terminals

Each colored terminal element has two incidences inside its Figure 5 clause
core.  Combining those with the previously classified variable-side
incidences gives total terminal degree two or three.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/-- The unique terminal element of a selected color in each terminal
group. -/
def terminalElementForColor :
    WireColor → X3CClauseTerminalGroup → X3CClauseTerminal
  | .red, .top => ⟨.top, .third⟩
  | .red, .left => ⟨.left, .third⟩
  | .red, .right => ⟨.right, .second⟩
  | .green, .top => ⟨.top, .first⟩
  | .green, .left => ⟨.left, .second⟩
  | .green, .right => ⟨.right, .third⟩
  | .blue, .top => ⟨.top, .second⟩
  | .blue, .left => ⟨.left, .first⟩
  | .blue, .right => ⟨.right, .first⟩

@[simp]
theorem terminalElementForColor_group
    (color : WireColor) (group : X3CClauseTerminalGroup) :
    (terminalElementForColor color group).group = group := by
  cases color <;> cases group <;> rfl

/-- One clause block contributes exactly the two local neighbors at the
target index and none at another index. -/
theorem clauseBlock_terminalIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (color : WireColor)
    (current target : Nat) (group : X3CClauseTerminalGroup) :
    (allClauseSets.map
      (Triple.clause (Variable := Variable) current)).filterMap
        (fun triple =>
          if terminalReferenceMatches
              source color target group triple then
            some
              (⟨triple, terminalReferenceOffset source color triple⟩ :
                Incidence Variable)
          else none) =
      if current = target then
        ((terminalElementForColor color group).neighbors).map fun set =>
          ⟨.clause target set, (0, 0)⟩
      else [] := by
  by_cases same : current = target
  · subst current
    cases color <;> cases group <;>
      simp [allClauseSets, terminalReferenceMatches,
        terminalReferenceOffset, tripleReferences,
        clauseTripleReferences, clauseRedElement,
        clauseGreenElement, clauseBlueElement,
        X3CClauseSet.coloredReferences,
        terminalElementForColor, X3CClauseTerminal.neighbors]
  · cases color <;> cases group <;>
      simp [allClauseSets, terminalReferenceMatches,
        terminalReferenceOffset, tripleReferences,
        clauseTripleReferences, clauseRedElement,
        clauseGreenElement, clauseBlueElement,
        X3CClauseSet.coloredReferences, same]

/-- The complete clause list contributes exactly two incidences at a valid
colored terminal. -/
theorem clauseTerminalIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (color : WireColor)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    (clauseTriples source).filterMap
        (fun triple =>
          if terminalReferenceMatches
              source color clauseIndex group triple then
            some
              (⟨triple, terminalReferenceOffset source color triple⟩ :
                Incidence Variable)
          else none) =
      ((terminalElementForColor color group).neighbors).map fun set =>
        ⟨.clause clauseIndex set, (0, 0)⟩ := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [clauseBlock_terminalIncidences
    source color _ clauseIndex group]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (List.range source.clauses.length) clauseIndex
      (((terminalElementForColor color group).neighbors).map fun set =>
        (⟨.clause clauseIndex set, (0, 0)⟩ :
          Incidence Variable))
      List.nodup_range (List.mem_range.mpr indexLt)

/-- Total colored terminal degree is the number of attached occurrences plus
the two clause-core incidences. -/
theorem terminalIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (color : WireColor)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    (((triples source).filterMap fun triple =>
      if terminalReferenceMatches
          source color clauseIndex group triple then
        some
          (⟨triple, terminalReferenceOffset source color triple⟩ :
            Incidence Variable)
      else none).length) =
      (terminalOccurrenceEnumeration source clauseIndex group).length + 2 := by
  rw [triples, List.filterMap_append, List.length_append,
    ← variableTerminalIncidences_length
      source color clauseIndex group,
    variableTerminalIncidences,
    clauseTerminalIncidences
      source color clauseIndex indexLt group]
  cases color <;> cases group <;> rfl

theorem problem_redIncidences_clauseTerminal_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    ((problem source).redIncidences
      (.clauseTerminal clauseIndex group)).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length + 2 := by
  simpa [TypedProblem.redIncidences, problem,
    terminalReferenceMatches, terminalReferenceOffset] using
      terminalIncidences_length
        source .red clauseIndex indexLt group

theorem problem_greenIncidences_clauseTerminal_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    ((problem source).greenIncidences
      (.clauseTerminal clauseIndex group)).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length + 2 := by
  simpa [TypedProblem.greenIncidences, problem,
    terminalReferenceMatches, terminalReferenceOffset] using
      terminalIncidences_length
        source .green clauseIndex indexLt group

theorem problem_blueIncidences_clauseTerminal_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (group : X3CClauseTerminalGroup) :
    ((problem source).blueIncidences
      (.clauseTerminal clauseIndex group)).length =
      (terminalOccurrenceEnumeration
        source clauseIndex group).length + 2 := by
  simpa [TypedProblem.blueIncidences, problem,
    terminalReferenceMatches, terminalReferenceOffset] using
      terminalIncidences_length
        source .blue clauseIndex indexLt group

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
