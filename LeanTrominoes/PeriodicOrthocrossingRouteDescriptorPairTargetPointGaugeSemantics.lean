/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeQuotientSemantics

/-! # Period gauges of affine target-fanout points -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The fixed target-tail gauge list is exact on every descriptor satisfying
the numeric coordinate bounds. -/
theorem FanoutShape.targetTail_forall₂_targetTailPointGauges
    (shape : FanoutShape) (coreShape : CoreShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂ (Point.HasPeriodGauge pair)
      (shape.targetTail coreShape .first)
      (shape.targetTailPointGauges coreShape) := by
  have targetCenterZero :
      vertexX pair.1.targetVertexIndex / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.targetCenter
  have targetCenterPlus :
      (vertexX pair.1.targetVertexIndex + pair.1.gridSize) /
          pair.1.gridSize = 1 :=
    pair.1.coordinate_add_gridSize_ediv_eq_one bounds.targetCenter
  have targetCenterMinus :
      (vertexX pair.1.targetVertexIndex - pair.1.gridSize) /
          pair.1.gridSize = -1 :=
    pair.1.coordinate_sub_gridSize_ediv_eq_neg_one bounds.targetCenter
  have targetPortZero :
      descriptorPortX pair.1.targetVertexIndex pair.1.targetPortRank /
          pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.targetPort
  have targetPortPlus :
      (descriptorPortX pair.1.targetVertexIndex pair.1.targetPortRank +
          pair.1.gridSize) / pair.1.gridSize = 1 :=
    pair.1.coordinate_add_gridSize_ediv_eq_one bounds.targetPort
  have targetPortMinus :
      (descriptorPortX pair.1.targetVertexIndex pair.1.targetPortRank -
          pair.1.gridSize) / pair.1.gridSize = -1 :=
    pair.1.coordinate_sub_gridSize_ediv_eq_neg_one bounds.targetPort
  have twoBounds : pair.1.CoordinateInPeriod (2 : Int) := by
    constructor
    · omega
    · simp [RouteDescriptor.gridSize]
      omega
  have twoZero : (2 : Int) / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero twoBounds
  have twoPlus :
      ((2 : Int) + pair.1.gridSize) / pair.1.gridSize = 1 :=
    pair.1.coordinate_add_gridSize_ediv_eq_one twoBounds
  have twoMinus :
      ((2 : Int) - pair.1.gridSize) / pair.1.gridSize = -1 :=
    pair.1.coordinate_sub_gridSize_ediv_eq_neg_one twoBounds
  cases shape <;> cases coreShape <;>
    simp [FanoutShape.targetTail, FanoutShape.targetTailPointGauges,
      CoreShape.translatePoint, CoreShape.periodGauge,
      Point.HasPeriodGauge, drawingPointGaugeAtPeriod,
      Point.evalPair_point,
      evalPair_targetCenterX, evalPair_targetPortX, evalPair_gridSize,
      descriptorAt, targetCenterZero, targetCenterPlus,
      targetCenterMinus, targetPortZero, targetPortPlus,
      targetPortMinus, twoZero, twoPlus, twoMinus]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
