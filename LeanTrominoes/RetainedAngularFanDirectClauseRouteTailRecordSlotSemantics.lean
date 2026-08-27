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

end PeriodicEightOccurrenceSplit
end LeanTrominoes
