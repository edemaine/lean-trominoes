/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierFallbackKindSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierFallbackRouteTerminalModel

/-! # Indexed fallback-route model for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierFallbackModelThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- An indexed final-carrier fallback is the carrier table's route-kind
splice with the exact semantic terminal datum. -/
theorem retainedFinalFallbackOccurrenceRoute_carrier_eq_model
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
    retainedFinalFallbackOccurrenceRoute
        retained clause literal clauseIndex literalIndex =
      (CarrierFallbackRouteTailRecords.routeKind
          localClauseIndex literalIndex).splicedOwnFigure7Route
        route terminal slot := by
  dsimp only
  rw [retainedFinalFallbackOccurrenceRoute_carrier_eq_terminalModel
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    taggedLink clauseIndex taggedLinkIndexed clauseMember
    literalIndex literalMember]
  change
    (if (finalCoordinatedSourceRoutes
          (PeriodicThreeSATThree.formula source)
          clauseIndex literalIndex).dropLast.length = 1 then
        RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route _ _ _ = _
  rw [finalCoordinatedSourceCarrierRoute_fallbackKind_eq
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    taggedLink clauseIndex taggedLinkIndexed literalIndex]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
