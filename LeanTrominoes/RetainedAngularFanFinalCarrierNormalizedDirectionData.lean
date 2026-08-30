/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData

/-! # Named normalized-direction claims for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

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
  Gadget.unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        ((CarrierFallbackRouteTailRecords.routeKind
            (if taggedLink.2 then 0 else 1)
            literalIndex).splicedOwnFigure7Route
          route terminalData slot)) =
    CarrierNormalizedFallbackRouteTailRecords.routeDirections
      (finalCarrierRouteGeometryAt source taggedLink nextSlice)
      (finalCarrierLocalClauseIndex taggedLink) literalIndex slot

/-- Route evidence aligned with the semantic carrier terminal datum. -/
structure FinalCarrierTerminalNormalizationEvidence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2)
    (route : List Cell)
    (terminalData : RetainedTerminalData)
    (prefixDirections : List AxisDirection) : Prop where
  routeEvidence : FinalCarrierScaledRouteEvidence
    route terminalData prefixDirections
  terminalEq : terminalData =
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.second))
        (if taggedLink.2 then 0 else 1) literalIndex)
/-- Route evidence aligned with both semantic carrier terminal and prefix
data. -/
structure FinalCarrierNormalizationEvidence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Fin 2)
    (route : List Cell)
    (terminalData : RetainedTerminalData)
    (prefixDirections : List AxisDirection) : Prop where
  terminalEvidence : FinalCarrierTerminalNormalizationEvidence
    source taggedLink literalIndex route terminalData prefixDirections
  prefixEq : prefixDirections =
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

/-- Compact cross-module request containing aligned route evidence and the
finite carrier span bound. -/
structure FinalCarrierNormalizationRequest
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (terminalData : RetainedTerminalData)
    (prefixDirections : List AxisDirection) : Prop where
  spanLarge :
    8 ≤ (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
  normalizationEvidence : FinalCarrierNormalizationEvidence
    source taggedLink literalIndex route terminalData prefixDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
