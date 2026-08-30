/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData

/-! # Scaled final-carrier prefixes in finite geometry coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- A route's prefix directions in finite carrier geometry coordinates. -/
structure FinalCarrierGeometryPrefixDirections
    (route : List Cell)
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (localClauseIndex literalIndex : Fin 2) : Prop where
  prefixDirections :
    Gadget.unitSubdivisionDirections (retainedFallbackSourcePrefix route) =
      Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections geometry.horizontal geometry.span
          localClauseIndex literalIndex)

/-- Transport actual final-carrier prefix directions into a named finite
geometry certificate. -/
theorem finalCarrierGeometryPrefixDirections_of_actual
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (route : List Cell)
    (prefixDirections :
      Gadget.unitSubdivisionDirections (retainedFallbackSourcePrefix route) =
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
    FinalCarrierGeometryPrefixDirections route
      (finalCarrierRouteGeometryAt source taggedLink nextSlice)
      (finalCarrierLocalClauseIndex taggedLink) literalIndex :=
  ⟨prefixDirections.trans
    (repeatCarrierLensRoutePrefixDirections_finalCarrierRouteGeometryAt
      source taggedLink nextSlice literalIndex)⟩

/-- A scaled-route evidence package exposes its finite-geometry prefix
directions without expanding that equality downstream. -/
theorem FinalCarrierScaledRouteEvidence.geometryPrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    {route : List Cell}
    {terminalData : RetainedTerminalData}
    (evidence : FinalCarrierScaledRouteEvidence route terminalData
      (Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections
          taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex))) :
    FinalCarrierGeometryPrefixDirections route
      (finalCarrierRouteGeometryAt source taggedLink nextSlice)
      (finalCarrierLocalClauseIndex taggedLink) literalIndex :=
  finalCarrierGeometryPrefixDirections_of_actual source taggedLink nextSlice
    literalIndex route evidence.routePrefixDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
