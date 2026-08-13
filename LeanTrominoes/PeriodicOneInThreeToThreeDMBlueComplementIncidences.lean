/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMBlueClauseIncidences

/-!
# Complementary clause-blue incidences

Each literal occurrence has a private blue element joining the opposite port
of its variable occurrence pair to its clause-local auxiliary triple.  The
definitions below preserve the construction's stable enumeration while the
classification theorem identifies both parts of the actual typed incidence
list.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- The possible complementary-port incidence contributed by one variable
slot to a selected clause/literal position. -/
def complementIncidenceAt {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (clauseIndex literalIndex : Nat) :
    List (Incidence Variable) :=
  match occurrenceAt source atom slot with
  | none => []
  | some tagged =>
      if tagged.2.1 = clauseIndex ∧ tagged.2.2 = literalIndex then
        [⟨.variable atom (slot.complementTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩]
      else
        []

/-- Complementary-port incidences from all three slots of one variable. -/
def complementIncidencesForAtom {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (clauseIndex literalIndex : Nat) :
    List (Incidence Variable) :=
  OccurrenceSlot.all.flatMap fun slot =>
    complementIncidenceAt source atom slot clauseIndex literalIndex

/-- Complete variable-port incidence list for one occurrence-specific
complement blue element. -/
def complementVariableIncidences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : List (Incidence Variable) :=
  (occurringVariables source).flatMap fun atom =>
    complementIncidencesForAtom source atom clauseIndex literalIndex

/-- Clause auxiliaries at one selected syntactic occurrence position. -/
def complementAuxiliaryIncidences {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex literalIndex : Nat) :
    List (Incidence Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).filterMap fun tagged =>
    if tagged.2.1 = clauseIndex ∧ tagged.2.2 = literalIndex then
      some
        ⟨.clauseAuxiliary clauseIndex literalIndex,
          (0, 0)⟩
    else
      none

/-- Filtering one complementary port pair at an occurrence-specific blue
element retains exactly the port opposite the source literal's sign. -/
theorem variablePair_filterMap_complement {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (clauseIndex literalIndex : Nat) :
    ((OccurrenceSlot.triples slot).map
        (Triple.variable atom)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.complement clauseIndex literalIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      complementIncidenceAt source atom slot
        clauseIndex literalIndex := by
  cases lookup : occurrenceAt source atom slot with
  | none =>
      cases slot <;>
        simp [OccurrenceSlot.triples, complementIncidenceAt,
          tripleReferences, variableTripleReferences,
          variableBlueElement, variableBlueOffset, lookup]
  | some tagged =>
      rcases tagged with ⟨literal, taggedClauseIndex,
        taggedLiteralIndex⟩
      rcases literal with ⟨literalAtom, offset, value⟩
      cases value <;>
        cases slot <;>
        by_cases sameClause :
          taggedClauseIndex = clauseIndex <;>
        by_cases sameLiteral :
          taggedLiteralIndex = literalIndex <;>
        simp [OccurrenceSlot.triples, complementIncidenceAt,
          OccurrenceSlot.complementTriple, tripleReferences,
          variableTripleReferences, variableBlueElement,
          variableBlueOffset, lookup, sameClause, sameLiteral]

/-- Filtering one six-cycle variable block at a selected complementary blue
element gives its three-slot presentation. -/
theorem variableBlock_filterMap_complement {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (clauseIndex literalIndex : Nat) :
    (allVariableTriples.map (Triple.variable atom)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.complement clauseIndex literalIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      complementIncidencesForAtom source atom
        clauseIndex literalIndex := by
  rw [allVariableTriples_eq_slotTriples, List.map_flatMap,
    filterMap_flatMap]
  simp_rw [variablePair_filterMap_complement]
  rfl

/-- The variable part of an occurrence-specific complement element is exactly
the stable list of opposite ports selected above. -/
theorem blueVariableTriples_filterMap_complement {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.complement clauseIndex literalIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      complementVariableIncidences source clauseIndex literalIndex := by
  rw [variableTriples, filterMap_flatMap]
  simp_rw [variableBlock_filterMap_complement]
  rfl

/-- The clause-auxiliary part of an occurrence-specific complement element is
the filtered tagged-occurrence presentation. -/
theorem blueClauseAuxiliaries_filterMap_complement {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.complement clauseIndex literalIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      complementAuxiliaryIncidences source
        clauseIndex literalIndex := by
  unfold clauseAuxiliaryTriples complementAuxiliaryIncidences
  generalize
    PeriodicThreeSATThree.taggedLiterals source = taggedOccurrences
  induction taggedOccurrences with
  | nil => rfl
  | cons tagged rest induction =>
      simp [List.filterMap_map, tripleReferences,
        clauseAuxiliaryReferences] at induction
      by_cases sameClause : tagged.2.1 = clauseIndex
      · by_cases sameLiteral : tagged.2.2 = literalIndex
        · simp [sameClause, sameLiteral, induction,
            tripleReferences, clauseAuxiliaryReferences]
        · simp [sameClause, sameLiteral, induction,
            tripleReferences, clauseAuxiliaryReferences]
      · simp [sameClause, induction, tripleReferences,
          clauseAuxiliaryReferences]

/-- The actual typed occurrence-specific blue element exposes its opposite
variable ports followed by its clause auxiliary incidences. -/
theorem problem_blueIncidences_complement {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    (problem source).blueIncidences
        (.complement clauseIndex literalIndex) =
      complementVariableIncidences source clauseIndex literalIndex ++
        complementAuxiliaryIncidences source
          clauseIndex literalIndex := by
  rw [TypedPeriodicThreeDM.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.complement clauseIndex literalIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    blueVariableTriples_filterMap_complement,
    blueClauseAuxiliaries_filterMap_complement]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
