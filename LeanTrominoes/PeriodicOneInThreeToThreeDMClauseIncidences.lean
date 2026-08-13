/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMVariableIncidences

/-!
# Clause-core incidences

This file connects the clause-local auxiliary triples in the typed periodic
3DM construction to their common red and green core elements.  Filtering the
global tagged-literal presentation at one clause index preserves the source
literal order, so both core elements see exactly one zero-offset auxiliary
incidence per literal occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Tagged literal occurrences belonging to one source protoclause. -/
def clauseOccurrences {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    List (TaggedOccurrence Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).filter fun tagged =>
    tagged.2.1 = clauseIndex

/-- The zero-offset auxiliary incidences contributed by one protoclause. -/
def clauseAuxiliaryIncidences {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    List (Incidence Variable) :=
  (clauseOccurrences source clauseIndex).map fun tagged =>
    ⟨.clauseAuxiliary clauseIndex tagged.2.2, (0, 0)⟩

/-- Variable-cycle triples never meet a clause-core red element. -/
theorem redVariableTriples_filterMap_clause_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  rw [variableTriples, filterMap_flatMap]
  simp [tripleReferences, variableTripleReferences]

/-- Filtering all clause auxiliaries at one red core gives exactly the
auxiliary incidence list for that clause. -/
theorem redClauseAuxiliaries_filterMap_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      clauseAuxiliaryIncidences source clauseIndex := by
  unfold clauseAuxiliaryTriples clauseAuxiliaryIncidences
    clauseOccurrences
  generalize
    PeriodicThreeSATThree.taggedLiterals source = taggedOccurrences
  induction taggedOccurrences with
  | nil => rfl
  | cons tagged rest induction =>
      simp [List.filterMap_map, tripleReferences,
        clauseAuxiliaryReferences] at induction
      by_cases same : tagged.2.1 = clauseIndex
      · simp [same, induction, tripleReferences,
          clauseAuxiliaryReferences]
      · simp [same, induction, tripleReferences,
          clauseAuxiliaryReferences]

/-- The typed problem exposes one red-core incidence per literal occurrence
of the selected protoclause, in source order. -/
theorem problem_redIncidences_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (problem source).redIncidences (.clause clauseIndex) =
      clauseAuxiliaryIncidences source clauseIndex := by
  rw [TypedPeriodicThreeDM.redIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    redVariableTriples_filterMap_clause_nil,
    redClauseAuxiliaries_filterMap_clause]
  rfl

/-- Variable-cycle triples never meet a clause-core green element. -/
theorem greenVariableTriples_filterMap_clause_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  rw [variableTriples, filterMap_flatMap]
  simp [tripleReferences, variableTripleReferences]

/-- Filtering all clause auxiliaries at one green core gives exactly the
auxiliary incidence list for that clause. -/
theorem greenClauseAuxiliaries_filterMap_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      clauseAuxiliaryIncidences source clauseIndex := by
  unfold clauseAuxiliaryTriples clauseAuxiliaryIncidences
    clauseOccurrences
  generalize
    PeriodicThreeSATThree.taggedLiterals source = taggedOccurrences
  induction taggedOccurrences with
  | nil => rfl
  | cons tagged rest induction =>
      simp [List.filterMap_map, tripleReferences,
        clauseAuxiliaryReferences] at induction
      by_cases same : tagged.2.1 = clauseIndex
      · simp [same, induction, tripleReferences,
          clauseAuxiliaryReferences]
      · simp [same, induction, tripleReferences,
          clauseAuxiliaryReferences]

/-- The typed problem exposes one green-core incidence per literal occurrence
of the selected protoclause, in source order. -/
theorem problem_greenIncidences_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (problem source).greenIncidences (.clause clauseIndex) =
      clauseAuxiliaryIncidences source clauseIndex := by
  rw [TypedPeriodicThreeDM.greenIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clause clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    greenVariableTriples_filterMap_clause_nil,
    greenClauseAuxiliaries_filterMap_clause]
  rfl

/-- The two clause-core colors have the same typed incidence list. -/
theorem problem_clauseCore_incidences_eq {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    (problem source).redIncidences (.clause clauseIndex) =
      (problem source).greenIncidences (.clause clauseIndex) := by
  rw [problem_redIncidences_clause, problem_greenIncidences_clause]

/-- Values seen at the red clause core are the selections of its auxiliary
triples at the same translated cell. -/
theorem problem_redIncidentValues_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (clauseIndex : Nat) (cell : Cell) :
    (problem source).redIncidentValues assignment
        (.clause clauseIndex) cell =
      (clauseOccurrences source clauseIndex).map fun tagged =>
        assignment (.clauseAuxiliary clauseIndex tagged.2.2) cell := by
  rw [TypedPeriodicThreeDM.redIncidentValues,
    problem_redIncidences_clause]
  simp [clauseAuxiliaryIncidences,
    TypedPeriodicThreeDM.incidenceValue, Cell.sub]

/-- Values seen at the green clause core are the same clause-auxiliary
selections. -/
theorem problem_greenIncidentValues_clause {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (clauseIndex : Nat) (cell : Cell) :
    (problem source).greenIncidentValues assignment
        (.clause clauseIndex) cell =
      (clauseOccurrences source clauseIndex).map fun tagged =>
        assignment (.clauseAuxiliary clauseIndex tagged.2.2) cell := by
  rw [TypedPeriodicThreeDM.greenIncidentValues,
    problem_greenIncidences_clause]
  simp [clauseAuxiliaryIncidences,
    TypedPeriodicThreeDM.incidenceValue, Cell.sub]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
