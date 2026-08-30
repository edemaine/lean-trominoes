/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierFallbackRouteModel
import LeanTrominoes.RetainedAngularFanFinalCarrierPublicFallbackRoute
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily

/-! # Public normalized-route model for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierNormalizedModelThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- At an indexed retained-carrier incidence, the public normalized route is
the normalized carrier-table Figure 7 splice. -/
theorem retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_carrier_eq_model
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    {clause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource
          (PeriodicThreeSATThree.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈ clause.literals.zipIdx) :
    let retained := PeriodicThreeSATThree.formula source
    let localClauseIndex := if taggedLink.2 then 0 else 1
    let route :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes retained clauseIndex literalIndex)
    let terminal :=
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
            (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
          localClauseIndex literalIndex)
    let slot := retainedFinalCoordinatedOccurrenceSlot
      retained literal clauseIndex literalIndex
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        retained clauseIndex literalIndex =
      AxisDirection.normalizeOrthogonalPolyline
        ((CarrierFallbackRouteTailRecords.routeKind
            localClauseIndex literalIndex).splicedOwnFigure7Route
          route terminal slot) := by
  dsimp only
  unfold
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_carrier_eq_fallback
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed clauseMember
      literalIndex literalMember,
    retainedFinalFallbackOccurrenceRoute_carrier_eq_model
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed clauseMember
      literalIndex literalMember]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
