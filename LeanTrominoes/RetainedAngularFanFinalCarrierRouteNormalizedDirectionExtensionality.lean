/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierRouteNormalizedDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedDirectionData
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData

/-! # Directional extensionality for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- A final carrier source route may expose its prefix using the actual
integral endpoint span; the finite geometry equality transports that word to
the canonical compiler model before normalization. -/
theorem finalCarrierRoute_normalized_fallback_directions_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (routeLength : 2 ≤ route.length)
    (routeClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex)))
    (routeOrthogonal : OrthogonalPolyline route)
    (routePrefixDirections :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections
            taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              (finalCarrierLocalClauseIndex taggedLink)
              literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData
                (finalCarrierRouteGeometryAt
                  source taggedLink nextSlice).horizontal
                (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
                (finalCarrierLocalClauseIndex taggedLink) literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (finalCarrierRouteGeometryAt source taggedLink nextSlice)
        (finalCarrierLocalClauseIndex taggedLink) literalIndex slot := by
  have routeClassifiedGeometry := routeClassified
  rw [carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    source taggedLink nextSlice literalIndex] at routeClassifiedGeometry
  apply carrierRoute_normalized_fallback_directions_eq
    (finalCarrierRouteGeometryAt source taggedLink nextSlice)
    spanLarge (finalCarrierLocalClauseIndex taggedLink) literalIndex slot route
    routeLength routeClassifiedGeometry routeOrthogonal
  exact routePrefixDirections.trans
    (repeatCarrierLensRoutePrefixDirections_finalCarrierRouteGeometryAt
      source taggedLink nextSlice literalIndex)

/-- The four packaged source-route facts specialize final-carrier
extensionality in one step. -/
theorem FinalCarrierScaledRouteEvidence.normalizedDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (evidence : FinalCarrierScaledRouteEvidence
      route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
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
          (if taggedLink.2 then 0 else 1) literalIndex))) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              (finalCarrierLocalClauseIndex taggedLink)
              literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData
                (finalCarrierRouteGeometryAt
                  source taggedLink nextSlice).horizontal
                (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
                (finalCarrierLocalClauseIndex taggedLink) literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (finalCarrierRouteGeometryAt source taggedLink nextSlice)
        (finalCarrierLocalClauseIndex taggedLink) literalIndex slot :=
  finalCarrierRoute_normalized_fallback_directions_eq
    source taggedLink nextSlice spanLarge literalIndex slot route
    evidence.routeLength evidence.routeClassified
    evidence.routeOrthogonal evidence.routePrefixDirections

/-- The packaged direction theorem in the semantic axis-span coordinates
used by the public fallback route model. -/
theorem FinalCarrierScaledRouteEvidence.normalizedSemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (evidence : FinalCarrierScaledRouteEvidence
      route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
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
          (if taggedLink.2 then 0 else 1) literalIndex))) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              (if taggedLink.2 then 0 else 1)
              literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData
                taggedLink.1.first.isHorizontal
                (AxisDirection.axisSpan
                  (CarrierNode.position
                    (PeriodicThreeSATThree.formula source).incidenceGraph
                    taggedLink.1.first)
                  (CarrierNode.position
                    (PeriodicThreeSATThree.formula source).incidenceGraph
                    taggedLink.1.second))
                (if taggedLink.2 then 0 else 1) literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (finalCarrierRouteGeometryAt source taggedLink nextSlice)
        (finalCarrierLocalClauseIndex taggedLink) literalIndex slot := by
  rw [carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    source taggedLink nextSlice literalIndex]
  simpa only [finalCarrierLocalClauseIndex_val] using
    evidence.normalizedDirections
      source taggedLink nextSlice spanLarge literalIndex slot route

/-- A named terminal datum and prefix word can be transported to the
semantic carrier model by explicit equalities, avoiding eager unfolding of
large addressed route expressions. -/
theorem FinalCarrierScaledRouteEvidence.normalizedNamedSemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (terminalData : RetainedTerminalData)
    (prefixDirections : List AxisDirection)
    (evidence : FinalCarrierScaledRouteEvidence
      route terminalData prefixDirections)
    (terminalEq : terminalData =
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
          (if taggedLink.2 then 0 else 1) literalIndex))
    (prefixEq : prefixDirections =
      Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)) :
    finalCarrierNamedSemanticModelDirections source taggedLink nextSlice
      literalIndex slot route terminalData := by
  unfold finalCarrierNamedSemanticModelDirections
  subst terminalData
  subst prefixDirections
  exact evidence.normalizedSemanticModelDirections
    source taggedLink nextSlice spanLarge literalIndex slot route

/-- Evidence already indexed by the actual semantic terminal and prefix data
proves the shared named carrier-direction claim directly. -/
theorem FinalCarrierScaledRouteEvidence.normalizedActualSemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (evidence : FinalCarrierScaledRouteEvidence
      route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
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
          (if taggedLink.2 then 0 else 1) literalIndex))) :
    finalCarrierNamedSemanticModelDirections source taggedLink nextSlice
      literalIndex slot route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)) := by
  unfold finalCarrierNamedSemanticModelDirections
  exact evidence.normalizedSemanticModelDirections
    source taggedLink nextSlice spanLarge literalIndex slot route

/-- Consume the named normalized-direction proof without asking a downstream
module to match its expanded indexed result against an expected type. -/
theorem FinalCarrierScaledRouteEvidence.withNormalizedActualSemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (evidence : FinalCarrierScaledRouteEvidence
      route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
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
          (if taggedLink.2 then 0 else 1) literalIndex)))
    {P : Prop}
    (consume : finalCarrierNamedSemanticModelDirections
      source taggedLink nextSlice literalIndex slot route
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)) → P) :
    P :=
  consume (evidence.normalizedActualSemanticModelDirections
    source taggedLink nextSlice spanLarge literalIndex slot route)

/-- A compact actual-normalization request exposes its named compiler
direction proof. -/
theorem FinalCarrierNormalizationRequest.directions
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {nextSlice : Bool}
    {literalIndex : Fin 2}
    {slot : RetainedTerminalSlot}
    {route : List Cell}
    {terminalData : RetainedTerminalData}
    {prefixDirections : List AxisDirection}
    (request : FinalCarrierNormalizationRequest source taggedLink
      nextSlice literalIndex slot route terminalData prefixDirections) :
    finalCarrierNamedSemanticModelDirections source taggedLink nextSlice
      literalIndex slot route terminalData :=
  request.normalizationEvidence.terminalEvidence.routeEvidence.normalizedNamedSemanticModelDirections
    source taggedLink nextSlice request.spanLarge literalIndex slot route
    terminalData prefixDirections
    request.normalizationEvidence.terminalEvidence.terminalEq
    request.normalizationEvidence.prefixEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
