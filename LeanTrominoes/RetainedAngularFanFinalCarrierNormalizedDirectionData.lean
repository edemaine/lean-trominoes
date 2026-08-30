/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData

/-! # Named normalized-direction data for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- The actual scaled terminal datum addressed by a semantic final carrier. -/
abbrev finalCarrierActualScaledTerminalData
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2) : RetainedTerminalData :=
  scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
    (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
      (AxisDirection.axisSpan
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.first)
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.second))
      (if taggedLink.2 then 0 else 1) literalIndex)

/-- The actual scaled prefix word addressed by a semantic final carrier. -/
abbrev finalCarrierActualScaledPrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2) : List AxisDirection :=
  Gadget.repeatDirections 1152
    (carrierLensRoutePrefixDirections taggedLink.1.first.isHorizontal
      (AxisDirection.axisSpan
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.first)
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.second))
      (if taggedLink.2 then 0 else 1) literalIndex)

/-- The normalized direction word of a named semantic final-carrier route. -/
abbrev finalCarrierSemanticDirectionWord
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (terminalData : RetainedTerminalData) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      ((CarrierFallbackRouteTailRecords.routeKind
          (if taggedLink.2 then 0 else 1)
          literalIndex).splicedOwnFigure7Route
        route terminalData slot))

/-- The finite compiler direction word addressed by a semantic final
carrier. -/
def finalCarrierModelDirectionWord
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  CarrierNormalizedFallbackRouteTailRecords.routeDirections
    (finalCarrierRouteGeometryAt source taggedLink nextSlice)
    (finalCarrierLocalClauseIndex taggedLink) literalIndex slot

/-- The exact finite compiler direction claim for a named semantic carrier
route and terminal datum. -/
def finalCarrierNamedSemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (terminalData : RetainedTerminalData) : Prop :=
  finalCarrierSemanticDirectionWord taggedLink literalIndex slot route
      terminalData =
    finalCarrierModelDirectionWord source taggedLink nextSlice literalIndex slot

/-- Compact cross-module request for normalizing an actual semantic carrier
route. -/
structure FinalCarrierActualNormalizationRequest
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell) : Prop where
  spanLarge :
    8 ≤ (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
  routeEvidence : FinalCarrierScaledRouteEvidence route
    (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.second))
        (if taggedLink.2 then 0 else 1) literalIndex))
    (Gadget.repeatDirections 1152
      (carrierLensRoutePrefixDirections taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.second))
        (if taggedLink.2 then 0 else 1) literalIndex))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
