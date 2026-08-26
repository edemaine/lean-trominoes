/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedEscapedNormalizedFirstDirections
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOrdinaryNormalizedFirstDirections
import LeanTrominoes.RetainedAngularFanFinalDirectFirstDirections

/-! # Complete copied-source directions of final normalized routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Finite final direction selected for one copied retained source incidence.
Successful direct choices use the normalized atlas table; failed choices use
the direction of the scaled retained source route. -/
def retainedFinalCopiedSourceFirstDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    AxisDirection :=
  match retainedFinalDirectSourceRouteChoice?
      formula clauseIndex literalIndex with
  | some choice =>
      retainedDirectSourceNormalizedFirstDirection
        choice.kind choice.index
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)
  | none =>
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex))

/-- Every genuine copied-source incidence exposes its exact final direction:
a successful direct choice uses the finite normalized atlas table, while a
failed choice preserves the direction of the scaled retained source route. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_copied_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) =
      retainedFinalCopiedSourceFirstDirection
        formula clauseIndex literalIndex literal := by
  unfold retainedFinalCopiedSourceFirstDirection
  cases choiceLookup :
      retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex with
  | none =>
      by_cases singletonPrefix :
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).dropLast.length = 1
      · exact
          retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_escapedFallback_firstDirection
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
            choiceLookup singletonPrefix
      · exact
          retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_ordinaryFallback_firstDirection
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
            choiceLookup singletonPrefix
  | some choice =>
      exact
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_direct_firstDirection
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice clauseMember literalMember choiceLookup

end PeriodicOrthocrossing
end LeanTrominoes
