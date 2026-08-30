/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-! # Scaled final-carrier terminals in finite geometry coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- Scaling and wrapping in `some` preserve the actual-to-finite carrier
terminal equality. -/
theorem some_scaledCarrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Nat) :
    some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.second))
        (if taggedLink.2 then 0 else 1) literalIndex)) =
      some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData
          (finalCarrierRouteGeometryAt source taggedLink nextSlice).horizontal
          (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
          (finalCarrierLocalClauseIndex taggedLink) literalIndex)) :=
  congrArg some (congrArg
    (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor)
    (carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
      source taggedLink nextSlice literalIndex))

/-- Transport any classification ending in the actual scaled terminal to
the finite-geometry scaled terminal. -/
theorem eq_some_scaledCarrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Nat)
    {value : Option RetainedTerminalData}
    (classified : value =
      some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex))) :
    value =
      some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData
          (finalCarrierRouteGeometryAt source taggedLink nextSlice).horizontal
          (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
          (finalCarrierLocalClauseIndex taggedLink) literalIndex)) :=
  classified.trans
    (some_scaledCarrierLensRouteTerminalData_finalCarrierRouteGeometryAt
      source taggedLink nextSlice literalIndex)

/-- A route's terminal classification in finite carrier geometry
coordinates. -/
structure FinalCarrierGeometryClassification
    (route : List Cell)
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (localClauseIndex literalIndex : Fin 2) : Prop where
  classified :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector route) =
      some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData geometry.horizontal geometry.span
          localClauseIndex literalIndex))

/-- Transport an actual final-carrier classification into a named finite
geometry certificate. -/
theorem finalCarrierGeometryClassification_of_actual
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Fin 2)
    (route : List Cell)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex))) :
  FinalCarrierGeometryClassification route
      (finalCarrierRouteGeometryAt source taggedLink nextSlice)
      (finalCarrierLocalClauseIndex taggedLink) literalIndex :=
  ⟨eq_some_scaledCarrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    source taggedLink nextSlice literalIndex
    (value := retainedTerminalDirectionClassify
      (PeriodicThreeSATThree.routeTerminalVector route)) classified⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
