/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedDirectionQuery
import LeanTrominoes.RetainedAngularFanFinalCoordinatedNormalizedFirstDirections

/-! # Finite mixed queries for final copied-source directions -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- One finite query for a final copied incidence.  Direct incidences retain
only the stable normalized atlas key; fallback incidences retain the
already-computed scaled source direction. -/
inductive RetainedFinalCopiedSourceDirectionQuery
  | direct (query : RetainedDirectSourceNormalizedDirectionQuery)
  | fallback (direction : AxisDirection)
  deriving DecidableEq, Fintype

/-- Evaluate one mixed copied-source direction query. -/
def retainedFinalCopiedSourceDirectionOfQuery :
    RetainedFinalCopiedSourceDirectionQuery → AxisDirection
  | .direct query => retainedDirectSourceNormalizedDirectionOfQuery query
  | .fallback direction => direction

/-- Turn a successful direct choice into its fixed finite normalized query. -/
def RetainedDirectSourceRouteChoice.normalizedDirectionQuery
    (choice : RetainedDirectSourceRouteChoice) :
    RetainedDirectSourceNormalizedDirectionQuery :=
  retainedDirectSourceNormalizedDirectionQueryOfIndex
    choice.kind choice.index

/-- Exact finite query associated with one final copied-source incidence. -/
def retainedFinalCopiedSourceDirectionQuery
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (_literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    RetainedFinalCopiedSourceDirectionQuery :=
  match retainedFinalDirectSourceRouteChoice?
      formula clauseIndex literalIndex with
  | some choice =>
      .direct choice.normalizedDirectionQuery
  | none =>
      .fallback
        (AxisDirection.polylineFirstDirection
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex)))

/-- Evaluating the mixed finite query recovers the public final copied-source
direction lookup. -/
theorem retainedFinalCopiedSourceDirectionOfQuery_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    retainedFinalCopiedSourceDirectionOfQuery
        (retainedFinalCopiedSourceDirectionQuery
          formula clauseIndex literalIndex literal) =
      retainedFinalCopiedSourceFirstDirection
        formula clauseIndex literalIndex literal := by
  unfold retainedFinalCopiedSourceDirectionQuery
    retainedFinalCopiedSourceFirstDirection
  cases choiceLookup : retainedFinalDirectSourceRouteChoice?
      formula clauseIndex literalIndex with
  | none =>
    simp only [retainedFinalCopiedSourceDirectionOfQuery]
  | some choice =>
    simp only [retainedFinalCopiedSourceDirectionOfQuery,
      RetainedDirectSourceRouteChoice.normalizedDirectionQuery]
    exact retainedDirectSourceNormalizedDirectionOfQuery_index
      choice.kind choice.index
      (retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex)

/-- Presentation-ordered finite queries for all final copied incidences. -/
def retainedFinalCopiedSourceDirectionQueries
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List RetainedFinalCopiedSourceDirectionQuery :=
  (finalCoordinatedSource formula).clauses.zipIdx.flatMap fun taggedClause =>
    taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      retainedFinalCopiedSourceDirectionQuery
        formula taggedClause.2 taggedLiteral.2 taggedLiteral.1

/-- Elementwise evaluator for a mixed finite query stream. -/
def retainedFinalCopiedSourceDirections
    (queries : List RetainedFinalCopiedSourceDirectionQuery) :
    List AxisDirection :=
  queries.flatMap fun query =>
    [retainedFinalCopiedSourceDirectionOfQuery query]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
