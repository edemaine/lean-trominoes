/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeQuotientSemantics

/-! # Period gauges of affine source-fanout points -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The fixed source-fanout gauge list is exact on every descriptor satisfying
the numeric coordinate bounds. -/
theorem FanoutShape.sourcePoints_forall₂_sourcePointGauges
    (shape : FanoutShape) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂ (Point.HasPeriodGauge pair)
      (shape.sourcePoints .first) shape.sourcePointGauges := by
  have sourceCenterQuotient :
      vertexX pair.1.sourceVertexIndex / pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.sourceCenter
  have sourcePortQuotient :
      descriptorPortX pair.1.sourceVertexIndex pair.1.sourcePortRank /
          pair.1.gridSize = 0 :=
    pair.1.coordinate_ediv_gridSize_eq_zero bounds.sourcePort
  have twoQuotient : (2 : Int) / pair.1.gridSize = 0 :=
    pair.1.smallNonnegative_ediv_gridSize_eq_zero (by omega) (by omega)
  have threeQuotient : (3 : Int) / pair.1.gridSize = 0 :=
    pair.1.smallNonnegative_ediv_gridSize_eq_zero (by omega) (by omega)
  cases shape <;>
    simp [FanoutShape.sourcePoints, FanoutShape.sourcePointGauges,
      Point.HasPeriodGauge, drawingPointGaugeAtPeriod,
      evalPair_sourceCenterX, evalPair_sourcePortX, descriptorAt,
      sourceCenterQuotient, sourcePortQuotient, twoQuotient,
      threeQuotient]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
