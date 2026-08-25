/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCorePointGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourcePointGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairTargetPointGaugeSemantics
import LeanTrominoes.ListForall2Append

/-! # Exact period gauges of complete affine routes -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

theorem forall₂_tail
    {First Second : Type} {relation : First → Second → Prop}
    {first : List First} {second : List Second}
    (aligned : List.Forall₂ relation first second) :
    List.Forall₂ relation first.tail second.tail := by
  cases aligned with
  | nil => exact List.Forall₂.nil
  | cons _ remaining => exact remaining

/-- The complete route-point gauge list is exact on every descriptor satisfying
the numeric coordinate bounds. -/
theorem RouteShape.points_forall₂_pointGauges
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂ (Point.HasPeriodGauge pair)
      (shape.points .first) shape.pointGauges := by
  have sourceAligned :=
    shape.source.sourcePoints_forall₂_sourcePointGauges pair bounds
  have coreAligned :=
    shape.core.points_forall₂_pointGauges pair bounds
  have coreTailAligned :
      List.Forall₂ (Point.HasPeriodGauge pair)
        (shape.core.points .first).tail shape.core.pointGauges.tail := by
    exact forall₂_tail coreAligned
  have targetAligned :=
    shape.target.targetTail_forall₂_targetTailPointGauges
      shape.core pair bounds
  unfold RouteShape.points RouteShape.pointGauges routePoints
    routePointGauges
  exact List.Forall₂.append
    (List.Forall₂.append sourceAligned coreTailAligned)
    targetAligned

/-- Both endpoint gauges stored on a gauged segment are exact. -/
def GaugedSegment.HasPeriodGauges
    (pair : RouteDescriptor × RouteDescriptor)
    (gauged : GaugedSegment) : Prop :=
  gauged.segment.start.HasPeriodGauge pair gauged.startGauge ∧
    gauged.segment.finish.HasPeriodGauge pair gauged.finishGauge

theorem gaugedSegments_forall_of_points_forall₂
    (pair : RouteDescriptor × RouteDescriptor)
    {points : List Point} {gauges : List Cell}
    (aligned : List.Forall₂ (Point.HasPeriodGauge pair) points gauges) :
    ∀ gauged ∈ gaugedSegments points gauges,
      gauged.HasPeriodGauges pair := by
  induction aligned with
  | nil => simp [gaugedSegments]
  | cons firstCorrect remainingAligned induction =>
      cases remainingAligned with
      | nil => simp [gaugedSegments]
      | cons secondCorrect restAligned =>
          simp only [gaugedSegments, List.mem_cons]
          intro gauged gaugedMember
          rcases gaugedMember with rfl | gaugedMember
          · exact ⟨firstCorrect, secondCorrect⟩
          · exact induction gauged gaugedMember

/-- Gauged route segments erase to the original affine segment list. -/
theorem RouteShape.gaugedSegments_map_segment
    (shape : RouteShape) :
    (shape.gaugedSegments .first).map GaugedSegment.segment =
      shape.segments .first := by
  rcases shape with ⟨source, core, target⟩
  cases source <;> cases core <;> cases target <;> rfl

/-- Every gauged segment of a bounded route shape stores its exact two
endpoint quotients. -/
theorem RouteShape.gaugedSegments_forall_hasPeriodGauges
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    ∀ gauged ∈ shape.gaugedSegments .first,
      gauged.HasPeriodGauges pair := by
  exact gaugedSegments_forall_of_points_forall₂ pair
    (shape.points_forall₂_pointGauges pair bounds)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
