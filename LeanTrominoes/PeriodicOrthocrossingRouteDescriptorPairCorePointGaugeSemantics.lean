/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeQuotientSemantics

/-! # Period gauges of affine route-core points -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The fixed core gauge list is exact on every descriptor satisfying the
numeric coordinate bounds. -/
theorem CoreShape.points_forall₂_pointGauges
    (shape : CoreShape) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂ (Point.HasPeriodGauge pair)
      (shape.points .first) shape.pointGauges := by
  have sourcePortZero :
      descriptorPortX pair.1.sourceVertexIndex pair.1.sourcePortRank /
          pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.sourcePort
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
  have lowZero : edgeTrack pair.1.edgeIndex / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.lowTrack
  have lowPlus :
      (edgeTrack pair.1.edgeIndex + pair.1.gridSize) /
          pair.1.gridSize = 1 :=
    pair.1.coordinate_add_gridSize_ediv_eq_one bounds.lowTrack
  have highZero :
      (edgeTrack pair.1.edgeIndex + 1) / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.highTrack
  have highMinus :
      (edgeTrack pair.1.edgeIndex + 1 - pair.1.gridSize) /
          pair.1.gridSize = -1 :=
    pair.1.coordinate_sub_gridSize_ediv_eq_neg_one bounds.highTrack
  have gateZero :
      (8 * (pair.1.vertexCount : Int) + 4 + 2 * pair.1.edgeIndex) /
          pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.gate
  have threeBounds : pair.1.CoordinateInPeriod (3 : Int) := by
    constructor
    · omega
    · simp [RouteDescriptor.gridSize]
      omega
  have threeZero : (3 : Int) / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero threeBounds
  have threePlus :
      ((3 : Int) + pair.1.gridSize) / pair.1.gridSize = 1 :=
    pair.1.coordinate_add_gridSize_ediv_eq_one threeBounds
  have periodPlusThree :
      ((pair.1.gridSize : Int) + 3) / pair.1.gridSize = 1 := by
    simpa [add_comm] using threePlus
  have threeMinus :
      ((3 : Int) - pair.1.gridSize) / pair.1.gridSize = -1 :=
    pair.1.coordinate_sub_gridSize_ediv_eq_neg_one threeBounds
  have zeroQuotient : (0 : Int) / pair.1.gridSize = 0 := by simp
  have periodQuotient :
      (pair.1.gridSize : Int) / pair.1.gridSize = 1 := by
    exact Int.ediv_self (by exact_mod_cast pair.1.gridSize_positive.ne')
  cases shape <;>
    simp [CoreShape.points, CoreShape.pointGauges,
      Point.HasPeriodGauge, drawingPointGaugeAtPeriod,
      evalPair_sourcePortX, evalPair_targetPortX, evalPair_lowTrack,
      evalPair_highTrack, evalPair_gateX, evalPair_gridSize, descriptorAt,
      sourcePortZero, targetPortZero, targetPortPlus, targetPortMinus,
      lowZero, lowPlus, highZero, highMinus, gateZero, threeZero,
      periodPlusThree, threeMinus, zeroQuotient,
      periodQuotient]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
