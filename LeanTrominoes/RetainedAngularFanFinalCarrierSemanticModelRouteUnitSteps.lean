/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierNormalizedFallbackRouteUnitSteps
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry

/-! # Unit steps of named final-carrier semantic models -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Transport the generic normalized carrier unit-step theorem from finite
geometry coordinates to a named final carrier's actual integral span. -/
theorem FinalCarrierScaledRouteEvidence.finalCarrierSemanticModelRouteUnitSteps
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (prefixDirections : List AxisDirection)
    (evidence : FinalCarrierScaledRouteEvidence route
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
      prefixDirections) :
    (AxisDirection.normalizeOrthogonalPolyline
      ((CarrierFallbackRouteTailRecords.routeKind
          (if taggedLink.2 then 0 else 1)
          literalIndex).splicedOwnFigure7Route
        route
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
        slot)).IsChain AxisDirection.IsUnitAxisStep := by
  let geometry := finalCarrierRouteGeometryAt source taggedLink nextSlice
  let localClauseIndex : Fin 2 := if taggedLink.2 then 0 else 1
  let terminal := scaleRetainedTerminalData
    retainedAngularFanSourceClearanceFactor
    (carrierLensRouteTerminalData geometry.horizontal geometry.span
      localClauseIndex literalIndex)
  have terminalEq :
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex) =
        terminal := by
    apply congrArg
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor)
    simpa [geometry, localClauseIndex, finalCarrierLocalClauseIndex] using
      carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
        source taggedLink nextSlice literalIndex
  rw [terminalEq] at evidence ⊢
  rcases taggedLink with ⟨link, forward⟩
  cases forward <;>
    simpa [localClauseIndex, terminal] using
      evidence.normalizedCarrierRouteUnitSteps geometry spanLarge
        localClauseIndex literalIndex slot route prefixDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
