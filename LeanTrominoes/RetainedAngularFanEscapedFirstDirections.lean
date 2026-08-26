/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceEscapedSingletonSplice
import LeanTrominoes.RetainedRayRasterizationFirstDirections

/-! # Clause-side directions of singleton escaped fallbacks

A singleton fallback replaces the source route's only edge by the fixed
64-block escaped inward ray.  Terminal classification makes that ray point
in exactly the original clause-to-variable direction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => rfl

private theorem polylineFirstDirection_isGenuine_of_orthogonal
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (AxisDirection.polylineFirstDirection points).IsGenuine := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          exact AxisDirection.between_isGenuine_of_axisAligned
            (List.isChain_cons_cons.mp orthogonal).1

private theorem two_le_length_of_firstDirection_isGenuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

/-- On an axis-aligned two-point source route, the escaped ray selected by
the backwards terminal classifier rasterizes in the original forward
direction. -/
theorem retainedTerminalFanOuterSourceEscapeRay_firstDirection_pair
    (first second gate : Cell)
    (terminal : RetainedTerminalData)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector [first, second]) =
        some terminal)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    AxisDirection.polylineFirstDirection
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate) =
      AxisDirection.polylineFirstDirection [first, second] := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases gate with ⟨gateX, gateY⟩
  rcases terminal with ⟨direction, length⟩
  have lengthPositive :=
    (retainedTerminalDirectionClassify_sound classified).1
  have vectorEq :=
    (retainedTerminalDirectionClassify_sound classified).2
  simp only [routeTerminalVector_pair, Cell.sub,
    Prod.mk.injEq, Cell.scale] at vectorEq
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  cases direction with
  | compass port =>
      cases port with
      | northwest =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> simp_all
      | north =>
          simp [retainedTerminalFanOuterSourceEscapeRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterSourceEscapeLength,
            RetainedRay.rasterize, oppositePort, compassRay,
            Port.unitVector, AxisDirection.polylineFirstDirection,
            AxisDirection.between, Cell.add, Cell.scale,
            RetainedTerminalDirection.primitive] at vectorEq ⊢
          rcases aligned with ⟨sameY, differentX⟩ |
              ⟨sameX, differentY⟩
          · omega
          · have firstLt : firstY < secondY := by omega
            simp [sameX, differentY, firstLt]
      | northeast =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | east =>
          simp [retainedTerminalFanOuterSourceEscapeRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterSourceEscapeLength,
            RetainedRay.rasterize, oppositePort, compassRay,
            Port.unitVector, AxisDirection.polylineFirstDirection,
            AxisDirection.between, Cell.add, Cell.scale,
            RetainedTerminalDirection.primitive] at vectorEq ⊢
          rcases aligned with ⟨sameY, differentX⟩ |
              ⟨sameX, differentY⟩
          · have secondLt : secondX < firstX := by omega
            simp [sameY, secondLt,
              not_lt_of_ge secondLt.le]
          · omega
      | southeast =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | south =>
          simp [retainedTerminalFanOuterSourceEscapeRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterSourceEscapeLength,
            RetainedRay.rasterize, oppositePort, compassRay,
            Port.unitVector, AxisDirection.polylineFirstDirection,
            AxisDirection.between, Cell.add, Cell.scale,
            RetainedTerminalDirection.primitive] at vectorEq ⊢
          rcases aligned with ⟨sameY, differentX⟩ |
              ⟨sameX, differentY⟩
          · omega
          · have secondLt : secondY < firstY := by omega
            simp [sameX, differentY, secondLt,
              not_lt_of_ge secondLt.le]
      | southwest =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | west =>
          simp [retainedTerminalFanOuterSourceEscapeRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterSourceEscapeLength,
            RetainedRay.rasterize, oppositePort, compassRay,
            Port.unitVector, AxisDirection.polylineFirstDirection,
            AxisDirection.between, Cell.add, Cell.scale,
            RetainedTerminalDirection.primitive] at vectorEq ⊢
          rcases aligned with ⟨sameY, differentX⟩ |
              ⟨sameX, differentY⟩
          · have firstLt : firstX < secondX := by omega
            simp [sameY, firstLt]
          · omega
  | routedClause arm =>
      cases arm <;>
        exfalso <;>
        simp [RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive, Cell.sub] at vectorEq <;>
        rcases aligned with aligned | aligned <;> omega

/-- The complete escaped fan starts in the direction of its fixed source
escape ray; all lane shifts and local Figure 7 routing occur later. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_firstDirection
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    AxisDirection.polylineFirstDirection
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot) =
      AxisDirection.polylineFirstDirection
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          (retainedAngularFanOuterDemand center terminal slot).gate) := by
  let escape :=
    (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
      (retainedAngularFanOuterDemand center terminal slot).gate
  have escapeGenuine :
      (AxisDirection.polylineFirstDirection escape).IsGenuine := by
    apply RetainedRay.rasterize_firstDirection_isGenuine
    rcases terminal with ⟨direction, length⟩
    cases direction <;>
      simp [retainedTerminalFanOuterSourceEscapeRay,
        retainedTerminalFanOuterInwardRayOfLength,
        retainedTerminalFanOuterSourceEscapeLength]
  have radialDirection :
      AxisDirection.polylineFirstDirection
          (retainedTerminalFanOuterEscapedRadialRoute
            center terminal slot) =
        AxisDirection.polylineFirstDirection escape := by
    unfold retainedTerminalFanOuterEscapedRadialRoute
    exact polylineFirstDirection_joinAtEndpoint_of_genuine escapeGenuine
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  rw [polylineFirstDirection_joinAtEndpoint_of_genuine]
  · exact radialDirection
  · rw [radialDirection]
    exact escapeGenuine

/-- A singleton source prefix makes the fixed escaped ray inherit the
original route's unique first direction. -/
theorem retainedTerminalFanOuterSourceEscapeRay_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (gate : Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (singletonPrefix : route.dropLast.length = 1) :
    AxisDirection.polylineFirstDirection
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate) =
      AxisDirection.polylineFirstDirection route := by
  have routeLengthEq : route.length = 2 := by
    rw [List.length_dropLast] at singletonPrefix
    omega
  cases route with
  | nil => simp at routeLength
  | cons first tail =>
      cases tail with
      | nil => simp at routeLength
      | cons second rest =>
          have restLength : rest.length = 0 := by
            change (first :: second :: rest).length = 2 at routeLengthEq
            simp only [List.length_cons] at routeLengthEq
            omega
          have restEmpty : rest = [] :=
            List.length_eq_zero_iff.mp restLength
          subst rest
          exact
            retainedTerminalFanOuterSourceEscapeRay_firstDirection_pair
              first second gate terminal classified
              (List.isChain_cons_cons.mp routeOrthogonal).1

/-- The rasterized singleton escaped boundary exposes the unique source
edge's first direction. -/
theorem retainedAngularFanEscapedSplicedBoundaryRoute_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (singletonPrefix : route.dropLast.length = 1) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanEscapedSplicedBoundaryRoute
          route terminal slot) =
      AxisDirection.polylineFirstDirection route := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let outerRoute :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escape :=
    (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate
  have boundaryEq :
      retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot =
        outerRoute := by
    simpa [center, outerRoute] using
      retainedAngularFanEscapedSplicedBoundaryPolyline_eq_outerCompleteRoute_of_singletonPrefix
        route terminal slot routeLength classified singletonPrefix
  have terminalPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have outerOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline outerRoute := by
    simpa [outerRoute] using
      retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
        center terminal slot terminalPositive escapeFits
  have outerDirection :
      AxisDirection.polylineFirstDirection outerRoute =
        AxisDirection.polylineFirstDirection escape := by
    simpa [outerRoute, escape, gate] using
      retainedTerminalFanOuterEscapedCompleteRoute_firstDirection
        center terminal slot
  have escapeGenuine :
      (AxisDirection.polylineFirstDirection escape).IsGenuine := by
    apply RetainedRay.rasterize_firstDirection_isGenuine
    rcases terminal with ⟨direction, length⟩
    cases direction <;>
      simp [retainedTerminalFanOuterSourceEscapeRay,
        retainedTerminalFanOuterInwardRayOfLength,
        retainedTerminalFanOuterSourceEscapeLength]
  have outerGenuine :
      (AxisDirection.polylineFirstDirection outerRoute).IsGenuine := by
    rw [outerDirection]
    exact escapeGenuine
  have outerLength : 2 ≤ outerRoute.length :=
    two_le_length_of_firstDirection_isGenuine outerGenuine
  have outerRetained : RetainedRayPolyline outerRoute :=
    RetainedRayPolyline.of_orthogonal outerOrthogonal
  unfold retainedAngularFanEscapedSplicedBoundaryRoute
  rw [boundaryEq,
    rasterizeRetainedPolyline_firstDirection_eq
      outerLength outerOrthogonal outerRetained,
    outerDirection]
  exact
    retainedTerminalFanOuterSourceEscapeRay_firstDirection
      route terminal gate routeLength classified routeOrthogonal
      singletonPrefix

/-- Appending any suffix to a singleton escaped fallback preserves the
source route's first direction. -/
theorem
    retainedAngularFanEscapedSplicedBoundaryRoute_joinAtEndpoint_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (suffix : List Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (singletonPrefix : route.dropLast.length = 1) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint
          (retainedAngularFanEscapedSplicedBoundaryRoute
            route terminal slot)
          suffix) =
      AxisDirection.polylineFirstDirection route := by
  rw [polylineFirstDirection_joinAtEndpoint_of_genuine]
  · exact
      retainedAngularFanEscapedSplicedBoundaryRoute_firstDirection
        route terminal slot routeLength classified routeOrthogonal
        escapeFits singletonPrefix
  · rw [
      retainedAngularFanEscapedSplicedBoundaryRoute_firstDirection
        route terminal slot routeLength classified routeOrthogonal
        escapeFits singletonPrefix]
    exact
      polylineFirstDirection_isGenuine_of_orthogonal
        routeLength routeOrthogonal

end PeriodicEightOccurrenceSplit
end LeanTrominoes
