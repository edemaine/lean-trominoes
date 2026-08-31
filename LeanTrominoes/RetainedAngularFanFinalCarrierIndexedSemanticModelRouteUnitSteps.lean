/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedRouteDirections
import LeanTrominoes.RetainedAngularFanFinalCarrierSemanticModelRouteUnitSteps

/-! # Unit steps of indexed final-carrier semantic models -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  drawingOrderedThreeOccurrenceVariableInstDecidableEq

/-- The semantic fallback model at an indexed final carrier is a unit-step
normalized route. -/
theorem FinalCarrierIndexedOccurrence.semanticFallbackRouteUnitSteps
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) :
    (AxisDirection.normalizeOrthogonalPolyline
      ((CarrierFallbackRouteTailRecords.routeKind
          (if occurrence.taggedLink.2 then 0 else 1)
          occurrence.literalIndex).splicedOwnFigure7Route
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            (PeriodicThreeSATThree.formula occurrence.source)
            occurrence.clauseIndex occurrence.literalIndex))
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData
            occurrence.taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula
                  occurrence.source).incidenceGraph
                occurrence.taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula
                  occurrence.source).incidenceGraph
                occurrence.taggedLink.1.second))
            (if occurrence.taggedLink.2 then 0 else 1)
            occurrence.literalIndex))
        (retainedFinalCoordinatedOccurrenceSlot
          (PeriodicThreeSATThree.formula occurrence.source)
          occurrence.literal occurrence.clauseIndex
          occurrence.literalIndex))).IsChain
      AxisDirection.IsUnitAxisStep := by
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  have evidence := occurrence.scaledRouteEvidence
  unfold FinalCarrierIndexedOccurrence.ScaledRouteEvidence at evidence
  rw [decEq] at evidence
  exact FinalCarrierScaledRouteEvidence.finalCarrierSemanticModelRouteUnitSteps
    occurrence.source occurrence.taggedLink nextSlice
    (occurrence.spanLarge nextSlice) occurrence.literalIndex
    (retainedFinalCoordinatedOccurrenceSlot
      (PeriodicThreeSATThree.formula occurrence.source)
      occurrence.literal occurrence.clauseIndex occurrence.literalIndex)
    (scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes
        (PeriodicThreeSATThree.formula occurrence.source)
        occurrence.clauseIndex occurrence.literalIndex))
    (Gadget.repeatDirections 1152
      (carrierLensRoutePrefixDirections
        occurrence.taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
            occurrence.taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
            occurrence.taggedLink.1.second))
        (if occurrence.taggedLink.2 then 0 else 1)
        occurrence.literalIndex)) evidence

end PeriodicEightOccurrenceSplit
end LeanTrominoes
