/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalFallbackFigure7Identification

/-! # Terminal-data model of final retained-carrier fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierFallbackTerminalModelThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- An indexed final-carrier fallback uses the exact semantic carrier
terminal datum; its independent singleton-prefix policy is left explicit. -/
theorem retainedFinalFallbackOccurrenceRoute_carrier_eq_terminalModel
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
    let rawRoute :=
      finalCoordinatedSourceRoutes retained clauseIndex literalIndex
    let route :=
      scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
    let terminal :=
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
            (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)
    let slot := retainedFinalCoordinatedOccurrenceSlot
      retained literal clauseIndex literalIndex
    retainedFinalFallbackOccurrenceRoute
        retained clause literal clauseIndex literalIndex =
      (if rawRoute.dropLast.length = 1 then
          RetainedFallbackFanKind.escaped
        else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
        route terminal slot := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let rawRoute :=
    finalCoordinatedSourceRoutes retained clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let slot := retainedFinalCoordinatedOccurrenceSlot
    retained literal clauseIndex literalIndex
  have retainedLocal : retained.IsLocal :=
    PeriodicThreeSATThree.formula_isLocal sourceLocal
  have retainedWidth : retained.WidthAtMost 3 :=
    PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth
  have retainedOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source
  have retainedClausesNonempty :
      ∀ retainedClause ∈ retained.clauses, retainedClause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty
      source sourceClausesNonempty
  have fallbackRouteEq :=
    retainedFinalFallbackOccurrenceRoute_eq_kind_splicedOwnFigure7Route
      retained retainedLocal retainedWidth retainedOccurrences
      retainedClausesNonempty clauseMember literalMember
  have rawTerminalEq :
      rawTerminal =
        carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
            (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex := by
    change
      finalCarrierActualTerminalDataAt source clauseIndex literalIndex = _
    exact finalCarrierTerminalData_eq_explicit
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed literalIndex
  rw [fallbackRouteEq]
  change
    (if rawRoute.dropLast.length = 1 then
        RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
        route
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal)
        slot = _
  rw [rawTerminalEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
