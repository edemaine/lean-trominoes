/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordStreamSemantics

/-! # Semantic occurrence slots for direct copied-clause records -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing

/-- Presentation-ordered bounded occurrence slots of one final copied
clause. -/
def retainedFinalDirectClauseOccurrenceSlots
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    RetainedDirectClauseOccurrenceSlots :=
  RetainedDirectClauseOccurrenceSlots.ofList
    (clause.literals.zipIdx.map fun taggedLiteral =>
      retainedFinalCoordinatedOccurrenceSlot
        formula taggedLiteral.1 clauseIndex taggedLiteral.2)

/-- Pair the established finite direction query with exactly the missing
bounded slot tuple. -/
def retainedFinalDirectClauseRouteTailRecordSlotInput
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    RetainedDirectClauseRouteTailRecordSlotInput :=
  (retainedFinalCopiedClauseQuery formula clauseIndex clause,
    retainedFinalDirectClauseOccurrenceSlots formula clauseIndex clause)

private theorem
    retainedFinalDirectRouteTailRecordLiteralQuery_directionQueryItem_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    (retainedFinalDirectRouteTailRecordLiteralQuery
      formula clauseIndex (literal, literalIndex)).directionQueryItem =
      (FormulaShapeDirectionOrdering.literalProfile literal,
        retainedFinalCopiedSourceDirectionQuery
          formula clauseIndex literalIndex literal) := by
  unfold retainedFinalDirectRouteTailRecordLiteralQuery
    retainedFinalCopiedSourceDirectionQuery
  rw [choiceLookup]
  rfl

private theorem
    retainedFinalDirectRouteTailRecordLiteralQuery_slot_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    (retainedFinalDirectRouteTailRecordLiteralQuery
      formula clauseIndex (literal, literalIndex)).tail.slot =
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex := by
  unfold retainedFinalDirectRouteTailRecordLiteralQuery
  rw [choiceLookup]
  rfl

/-- On a genuine nonempty direct clause, erasing the full query recovers
exactly the already-established copied-clause direction query. -/
theorem retainedFinalDirectClauseRouteTailRecordQuery_directionQuery_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseNonempty : clause.literals ≠ [])
    (clauseWidth : clause.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedLiteral ∈ clause.literals.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula clauseIndex taggedLiteral.2 = some choice) :
    (retainedFinalDirectClauseRouteTailRecordQuery
      formula clauseIndex clause).directionQuery =
      retainedFinalCopiedClauseQuery formula clauseIndex clause := by
  let queries := clause.literals.zipIdx.map
    (retainedFinalDirectRouteTailRecordLiteralQuery formula clauseIndex)
  have queriesNonempty : queries ≠ [] := by
    simpa [queries] using clauseNonempty
  have queriesWidth : queries.length ≤ 3 := by
    simpa [queries] using clauseWidth
  have packed :
      (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).literalQueries = queries :=
    RetainedDirectClauseRouteTailRecordQuery.literalQueries_ofList
      queries queriesNonempty queriesWidth
  unfold RetainedDirectClauseRouteTailRecordQuery.directionQuery
    retainedFinalCopiedClauseQuery
    retainedFinalCopiedClauseQueryOfLiterals
  rw [packed]
  apply congrArg RetainedFinalCopiedClauseQuery.ofList
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  rcases choicesSome taggedLiteral taggedLiteralMember with
    ⟨choice, choiceLookup⟩
  exact
    retainedFinalDirectRouteTailRecordLiteralQuery_directionQueryItem_eq
      formula clauseIndex taggedLiteral.1 taggedLiteral.2
      choice choiceLookup

/-- The slot projection of the full query is exactly the semantic occurrence
slot tuple. -/
theorem retainedFinalDirectClauseRouteTailRecordQuery_occurrenceSlots_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseNonempty : clause.literals ≠ [])
    (clauseWidth : clause.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedLiteral ∈ clause.literals.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula clauseIndex taggedLiteral.2 = some choice) :
    (retainedFinalDirectClauseRouteTailRecordQuery
      formula clauseIndex clause).occurrenceSlots =
      retainedFinalDirectClauseOccurrenceSlots
        formula clauseIndex clause := by
  let queries := clause.literals.zipIdx.map
    (retainedFinalDirectRouteTailRecordLiteralQuery formula clauseIndex)
  have queriesNonempty : queries ≠ [] := by
    simpa [queries] using clauseNonempty
  have queriesWidth : queries.length ≤ 3 := by
    simpa [queries] using clauseWidth
  have packed :
      (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).literalQueries = queries :=
    RetainedDirectClauseRouteTailRecordQuery.literalQueries_ofList
      queries queriesNonempty queriesWidth
  have slotsListEq :
      queries.map (fun query => query.tail.slot) =
        clause.literals.zipIdx.map fun taggedLiteral =>
          retainedFinalCoordinatedOccurrenceSlot
            formula taggedLiteral.1 clauseIndex taggedLiteral.2 := by
    rw [List.map_map]
    apply List.map_congr_left
    intro taggedLiteral taggedLiteralMember
    rcases choicesSome taggedLiteral taggedLiteralMember with
      ⟨choice, choiceLookup⟩
    change (retainedFinalDirectRouteTailRecordLiteralQuery
      formula clauseIndex taggedLiteral).tail.slot =
        retainedFinalCoordinatedOccurrenceSlot
          formula taggedLiteral.1 clauseIndex taggedLiteral.2
    unfold retainedFinalDirectRouteTailRecordLiteralQuery
    rw [choiceLookup]
    rfl
  change RetainedDirectClauseOccurrenceSlots.ofList
      ((retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).literalQueries.map
          fun query => query.tail.slot) =
    RetainedDirectClauseOccurrenceSlots.ofList
      (clause.literals.zipIdx.map fun taggedLiteral =>
        retainedFinalCoordinatedOccurrenceSlot
          formula taggedLiteral.1 clauseIndex taggedLiteral.2)
  calc
    _ = RetainedDirectClauseOccurrenceSlots.ofList
          (queries.map fun query => query.tail.slot) := by
      exact congrArg RetainedDirectClauseOccurrenceSlots.ofList
        (congrArg (List.map fun query => query.tail.slot) packed)
    _ = _ := congrArg RetainedDirectClauseOccurrenceSlots.ofList slotsListEq

/-- Therefore attaching the semantic slots to the existing direct query
recovers the full exact tail-record query. -/
theorem retainedDirectClauseRouteTailRecordQueryOfSlotInput_semantic
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseNonempty : clause.literals ≠ [])
    (clauseWidth : clause.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedLiteral ∈ clause.literals.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula clauseIndex taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordQueryOfSlotInput
        (retainedFinalDirectClauseRouteTailRecordSlotInput
          formula clauseIndex clause) =
      some (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause) := by
  rw [show retainedFinalDirectClauseRouteTailRecordSlotInput
      formula clauseIndex clause =
        ((retainedFinalDirectClauseRouteTailRecordQuery
            formula clauseIndex clause).directionQuery,
          (retainedFinalDirectClauseRouteTailRecordQuery
            formula clauseIndex clause).occurrenceSlots) by
    apply Prod.ext
    · exact
        (retainedFinalDirectClauseRouteTailRecordQuery_directionQuery_eq
          formula clauseIndex clause clauseNonempty clauseWidth
          choicesSome).symm
    · exact
        (retainedFinalDirectClauseRouteTailRecordQuery_occurrenceSlots_eq
          formula clauseIndex clause clauseNonempty clauseWidth
          choicesSome).symm]
  exact
    retainedDirectClauseRouteTailRecordQueryOfSlotInput_roundtrip _

/-- Semantic slot inputs for an indexed direct clause family. -/
def retainedFinalDirectClauseRouteTailRecordSlotInputs
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat)) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  taggedClauses.map fun taggedClause =>
    retainedFinalDirectClauseRouteTailRecordSlotInput
      formula taggedClause.2 taggedClause.1

/-- Attaching the semantic slots to a whole successful direct family
recovers exactly the full query family in global clause order. -/
theorem retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_semantic
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClauses : List
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat))
    (clausesNonempty :
      ∀ taggedClause ∈ taggedClauses,
        taggedClause.1.literals ≠ [])
    (clausesWidth :
      ∀ taggedClause ∈ taggedClauses,
        taggedClause.1.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedClause ∈ taggedClauses,
        ∀ taggedLiteral ∈ taggedClause.1.literals.zipIdx,
          ∃ choice,
            retainedFinalDirectSourceRouteChoice?
                formula taggedClause.2 taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (retainedFinalDirectClauseRouteTailRecordSlotInputs
          formula taggedClauses) =
      retainedFinalDirectClauseRouteTailRecordQueries
        formula taggedClauses := by
  induction taggedClauses with
  | nil => rfl
  | cons taggedClause taggedClauses induction =>
      have headNonempty :=
        clausesNonempty taggedClause (by simp)
      have headWidth :=
        clausesWidth taggedClause (by simp)
      have headChoices := fun taggedLiteral taggedLiteralMember =>
        choicesSome taggedClause (by simp)
          taggedLiteral taggedLiteralMember
      have tailNonempty :
          ∀ tailClause ∈ taggedClauses,
            tailClause.1.literals ≠ [] := by
        intro tailClause tailClauseMember
        exact clausesNonempty tailClause (by simp [tailClauseMember])
      have tailWidth :
          ∀ tailClause ∈ taggedClauses,
            tailClause.1.literals.length ≤ 3 := by
        intro tailClause tailClauseMember
        exact clausesWidth tailClause (by simp [tailClauseMember])
      have tailChoices :
          ∀ tailClause ∈ taggedClauses,
            ∀ taggedLiteral ∈ tailClause.1.literals.zipIdx,
              ∃ choice,
                retainedFinalDirectSourceRouteChoice?
                    formula tailClause.2 taggedLiteral.2 = some choice := by
        intro tailClause tailClauseMember taggedLiteral taggedLiteralMember
        exact choicesSome tailClause (by simp [tailClauseMember])
          taggedLiteral taggedLiteralMember
      simp only [retainedFinalDirectClauseRouteTailRecordSlotInputs,
        retainedFinalDirectClauseRouteTailRecordQueries,
        List.map_cons,
        retainedDirectClauseRouteTailRecordQueriesOfSlotInputs,
        List.flatMap_cons]
      rw [retainedDirectClauseRouteTailRecordQueryOfSlotInput_semantic
        formula taggedClause.2 taggedClause.1
        headNonempty headWidth headChoices]
      simp only [Option.toList_some, List.singleton_append,
        List.cons.injEq, true_and]
      exact induction tailNonempty tailWidth tailChoices

end PeriodicEightOccurrenceSplit
end LeanTrominoes
