/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailBlocks
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordQuery
import LeanTrominoes.RetainedAngularFanFinalDirectTailDirections

/-! # Exact semantics of finite direct copied-clause records -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Gadget
open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Interpret a finite direct literal query as the semantic annotated-tail
record used by the retained Figure 9 clockwise sorter. -/
def RetainedDirectRouteTailRecordLiteralQuery.annotatedTail
    (query : RetainedDirectRouteTailRecordLiteralQuery) : AnnotatedTail where
  profile := query.profile
  firstDirection := query.firstDirection
  sourceTailDirections := query.tailDirections

@[simp] theorem RetainedDirectRouteTailRecordLiteralQuery.annotatedTail_key
    (query : RetainedDirectRouteTailRecordLiteralQuery) :
    query.annotatedTail.key = query.key := by
  rfl

/-- Total semantic query for one indexed final copied literal. Direct-family
callers prove that the selector takes the `some` branch. -/
def retainedFinalDirectRouteTailRecordLiteralQuery
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (taggedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) × Nat) :
    RetainedDirectRouteTailRecordLiteralQuery :=
  match retainedFinalDirectSourceRouteChoice?
      formula clauseIndex taggedLiteral.2 with
  | none => default
  | some choice =>
      retainedDirectRouteTailRecordLiteralQueryOfIndex
        (FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1)
        choice.kind choice.index
        (retainedFinalCoordinatedOccurrenceSlot
          formula taggedLiteral.1 clauseIndex taggedLiteral.2)

/-- Presentation-ordered finite direct query for one final copied clause. -/
def retainedFinalDirectClauseRouteTailRecordQuery
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    RetainedDirectClauseRouteTailRecordQuery :=
  RetainedDirectClauseRouteTailRecordQuery.ofList
    (clause.literals.zipIdx.map
      (retainedFinalDirectRouteTailRecordLiteralQuery
        formula clauseIndex))

private def retainedCopiedClauseAnnotatedTailsFromSource
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    List AnnotatedTail :=
  clause.literals.zipIdx.map fun taggedLiteral =>
    let route :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex taggedLiteral.2
    { profile :=
        FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1
      firstDirection := AxisDirection.polylineFirstDirection route
      sourceTailDirections := unitSubdivisionDirections route.tail }

private theorem retainedFinalDirectRouteTailRecordLiteralQuery_annotatedTail_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    (retainedFinalDirectRouteTailRecordLiteralQuery
      formula clauseIndex (literal, literalIndex)).annotatedTail =
      { profile := FormulaShapeDirectionOrdering.literalProfile literal
        firstDirection := AxisDirection.polylineFirstDirection
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            formula clauseIndex literalIndex)
        sourceTailDirections := unitSubdivisionDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            formula clauseIndex literalIndex).tail } := by
  have firstDirectionEq :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_direct_firstDirection
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember choiceLookup
  have tailDirectionsEq :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_direct_tailDirections
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember choiceLookup
  unfold retainedFinalDirectRouteTailRecordLiteralQuery
  rw [choiceLookup]
  unfold RetainedDirectRouteTailRecordLiteralQuery.annotatedTail
  rw [retainedDirectRouteTailRecordLiteralQueryOfIndex_firstDirection,
    retainedDirectRouteTailRecordLiteralQueryOfIndex_tailDirections,
    ← firstDirectionEq, ← tailDirectionsEq]
  rfl

private theorem
    retainedFinalDirectClauseLiteralQueries_map_annotatedTail_eq_source
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (choicesSome :
      ∀ taggedLiteral ∈ clause.literals.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula clauseIndex taggedLiteral.2 = some choice) :
    (clause.literals.zipIdx.map
        (retainedFinalDirectRouteTailRecordLiteralQuery
          formula clauseIndex)).map
        RetainedDirectRouteTailRecordLiteralQuery.annotatedTail =
      retainedCopiedClauseAnnotatedTailsFromSource
        formula clauseIndex clause := by
  rw [List.map_map]
  unfold retainedCopiedClauseAnnotatedTailsFromSource
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  rcases choicesSome taggedLiteral taggedLiteralMember with
    ⟨choice, choiceLookup⟩
  exact retainedFinalDirectRouteTailRecordLiteralQuery_annotatedTail_eq
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty clauseMember taggedLiteralMember
    choice choiceLookup

private theorem retainedCopiedClauseAnnotatedTailsFromSource_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    retainedCopiedClauseAnnotatedTailsFromSource
        formula clauseIndex clause =
      annotatedTails
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula)
        clauseIndex
        (copiedOccurrenceClause formula clauseIndex clause) := by
  apply List.ext_getElem
  · simp [retainedCopiedClauseAnnotatedTailsFromSource,
      annotatedTails, copiedOccurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceClause]
  · intro index leftBound rightBound
    simp only [retainedCopiedClauseAnnotatedTailsFromSource,
      annotatedTails, copiedOccurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceLiteral,
      List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rfl

/-- If every literal of a genuine nonempty width-three copied clause has a
successful direct-atlas choice, the finite query emits exactly that clause's
semantic Figure 9 flat record, including the stable clockwise tail order. -/
theorem retainedFinalDirectClauseRouteTailRecordTokens_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (clauseNonempty : clause.literals ≠ [])
    (clauseWidth : clause.literals.length ≤ 3)
    (choicesSome :
      ∀ taggedLiteral ∈ clause.literals.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula clauseIndex taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordTokens
        (retainedFinalDirectClauseRouteTailRecordQuery
          formula clauseIndex clause) =
      HorizontalRoutedRouteTailRecord.clauseRecord
        (routedCopiedClauseProfile formula clauseIndex clause)
        (orderedTailDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            formula)
          clauseIndex
          (copiedOccurrenceClause formula clauseIndex clause)) := by
  let queries := clause.literals.zipIdx.map
    (retainedFinalDirectRouteTailRecordLiteralQuery formula clauseIndex)
  have queriesNonempty : queries ≠ [] := by
    simpa [queries] using clauseNonempty
  have queriesWidth : queries.length ≤ 3 := by
    simpa [queries] using clauseWidth
  have packed :
      (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).literalQueries = queries := by
    exact
      RetainedDirectClauseRouteTailRecordQuery.literalQueries_ofList
        queries queriesNonempty queriesWidth
  have evaluatedEq :
      queries.map
          RetainedDirectRouteTailRecordLiteralQuery.annotatedTail =
        annotatedTails
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            formula)
          clauseIndex
          (copiedOccurrenceClause formula clauseIndex clause) := by
    rw [retainedFinalDirectClauseLiteralQueries_map_annotatedTail_eq_source
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember choicesSome]
    exact retainedCopiedClauseAnnotatedTailsFromSource_eq
      formula clauseIndex clause
  have queryKeysEq :
      queries.map RetainedDirectRouteTailRecordLiteralQuery.key =
        (queries.map
          RetainedDirectRouteTailRecordLiteralQuery.annotatedTail).map
            AnnotatedTail.key := by
    induction queries with
    | nil => rfl
    | cons query queries induction =>
        simp only [List.map_cons]
        rw [query.annotatedTail_key, induction]
  have profileEq :
      (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).directedProfile =
        routedCopiedClauseProfile formula clauseIndex clause := by
    unfold RetainedDirectClauseRouteTailRecordQuery.directedProfile
      routedCopiedClauseProfile
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    rw [packed]
    apply congrArg FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
    calc
      queries.map RetainedDirectRouteTailRecordLiteralQuery.key =
          (queries.map
            RetainedDirectRouteTailRecordLiteralQuery.annotatedTail).map
              AnnotatedTail.key := by
        exact queryKeysEq
      _ = (annotatedTails
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              formula)
            clauseIndex
            (copiedOccurrenceClause formula clauseIndex clause)).map
              AnnotatedTail.key := by
        rw [evaluatedEq]
      _ = FormulaShapeDirectionOrdering.annotatedLiterals
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              formula)
            clauseIndex
            (copiedOccurrenceClause formula clauseIndex clause) := by
        exact annotatedTails_map_key _ _ _
  have tailTableEq :
      (retainedFinalDirectClauseRouteTailRecordQuery
        formula clauseIndex clause).tailTable =
        orderedTailDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            formula)
          clauseIndex
          (copiedOccurrenceClause formula clauseIndex clause) := by
    unfold RetainedDirectClauseRouteTailRecordQuery.tailTable
      orderedTailDirections orderedAnnotatedTails
    rw [packed]
    have mappedSort := List.map_insertionSort
      (r := retainedDirectRouteTailRecordLiteralLE)
      (s := FormulaShapeFigureNineSourceTail.directionLE)
      RetainedDirectRouteTailRecordLiteralQuery.annotatedTail
      queries (by
        intro first _ second _
        rfl)
    calc
      (queries.insertionSort
          retainedDirectRouteTailRecordLiteralLE).map
            RetainedDirectRouteTailRecordLiteralQuery.tailDirections =
          ((queries.insertionSort
            retainedDirectRouteTailRecordLiteralLE).map
              RetainedDirectRouteTailRecordLiteralQuery.annotatedTail).map
                AnnotatedTail.sourceTailDirections := by
        rw [List.map_map]
        rfl
      _ = ((queries.map
            RetainedDirectRouteTailRecordLiteralQuery.annotatedTail).insertionSort
              FormulaShapeFigureNineSourceTail.directionLE).map
                AnnotatedTail.sourceTailDirections := by
        rw [mappedSort]
      _ = ((annotatedTails
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              formula)
            clauseIndex
            (copiedOccurrenceClause formula clauseIndex clause)).insertionSort
              FormulaShapeFigureNineSourceTail.directionLE).map
                AnnotatedTail.sourceTailDirections := by
        rw [evaluatedEq]
  unfold retainedDirectClauseRouteTailRecordTokens
  rw [profileEq, tailTableEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
