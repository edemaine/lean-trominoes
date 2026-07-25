import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceCorrespondence
import LeanTrominoes.PeriodicOneInThreeToThreeDMClauseOccurrenceValues

/-!
# Source occurrence counts at clause terminals

A two-literal clause uses the top and left terminals; a three-literal clause
also uses the right terminal.  This file derives those counts through the
tagged-occurrence correspondence, in preparation for classifying the shared
clause-terminal incidences.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Filtering globally by clause and terminal is the same as first selecting
the clause occurrences and then selecting the terminal. -/
theorem sourceTerminalOccurrences_eq_clause_filter
    {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup) :
    sourceTerminalOccurrences source clauseIndex group =
      (PeriodicOneInThreeToThreeDM.clauseOccurrences
        source clauseIndex).filter fun tagged =>
          terminalGroupOfLiteralIndex tagged.2.2 = group := by
  unfold sourceTerminalOccurrences
    PeriodicOneInThreeToThreeDM.clauseOccurrences
  rw [List.filter_filter]
  congr 1
  funext tagged
  rw [Bool.decide_and, Bool.and_comm]

/-- At a valid clause index, source terminal occurrences are a permutation
of the explicitly indexed clause literals belonging to that terminal. -/
theorem sourceTerminalOccurrences_perm_taggedClause_filter
    {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (group : X3CClauseTerminalGroup) :
    List.Perm
      (sourceTerminalOccurrences source clauseIndex group)
      ((PeriodicOneInThreeToThreeDM.taggedClauseOccurrences
        clauseIndex clause).filter fun tagged =>
          terminalGroupOfLiteralIndex tagged.2.2 = group) := by
  rw [sourceTerminalOccurrences_eq_clause_filter]
  exact
    (PeriodicOneInThreeToThreeDM.clauseOccurrences_perm_taggedClauseOccurrences
        source clauseIndex clause clauseLookup).filter _

/-- A valid arity-two clause has one occurrence at top and left and none at
right; an arity-three clause has one at every terminal. -/
theorem sourceTerminalOccurrences_length_of_arity
    {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    (sourceTerminalOccurrences
      source clauseIndex group).length =
      if clause.length = 2 ∧ group = .right then 0 else 1 := by
  have lengthEq :=
    (sourceTerminalOccurrences_perm_taggedClause_filter
      source clauseIndex clause clauseLookup group).length_eq
  rcases arity with lengthTwo | lengthThree
  · rcases List.length_eq_two.mp lengthTwo with
      ⟨first, second, rfl⟩
    cases group <;>
      simpa [PeriodicOneInThreeToThreeDM.taggedClauseOccurrences,
        terminalGroupOfLiteralIndex] using lengthEq
  · rcases List.length_eq_three.mp lengthThree with
      ⟨first, second, third, rfl⟩
    cases group <;>
      simpa [PeriodicOneInThreeToThreeDM.taggedClauseOccurrences,
        terminalGroupOfLiteralIndex] using lengthEq

/-- The assembled module order has the same zero-or-one terminal counts. -/
theorem terminalOccurrenceEnumeration_length_of_arity
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    (terminalOccurrenceEnumeration
      source clauseIndex group).length =
      if clause.length = 2 ∧ group = .right then 0 else 1 := by
  rw [(terminalOccurrenceEnumeration_perm_source
    source occurrences clauseIndex group).length_eq]
  exact sourceTerminalOccurrences_length_of_arity
    source clauseIndex clause clauseLookup arity group

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
