/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateRadialSeparation
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections

/-! # Cardinal gate-tangent/fallback-suffix contact localization -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A positive cardinal backward tangent is an orthogonal two-point route. -/
theorem retainedTerminalFanCardinalBackwardTangentRoute_orthogonal
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (distancePositive : 0 < distance) :
    OrthogonalPolyline
      (retainedTerminalFanCardinalBackwardTangentRoute
        center port length slot distance) := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  change OrthogonalPolyline
    [Cell.add gate
      (Cell.scale (-(distance : Int))
        (retainedTerminalFanOuterLaneStep (.compass port))), gate]
  rcases gate with ⟨gateX, gateY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [OrthogonalPolyline,
      retainedTerminalFanOuterLaneStep,
      GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      Cell.add, Cell.scale] <;>
    omega

/-- For a cardinal terminal of length at least two, a positive source
segment immediately behind the gate meets the complete ordinary fallback
suffix only at that gate. -/
theorem retainedTerminalFanCardinalBackwardTangentRoute_only_common_suffix
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (distancePositive : 0 < distance) :
    ∀ point,
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalBackwardTangentRoute
          center port length slot distance) →
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center (.compass port, length) slot) →
      point =
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let tangent := retainedTerminalFanCardinalBackwardTangentRoute
    center port length slot distance
  let radial := retainedTerminalFanOuterRadialRoute
    center terminal slot
  let localRoute := retainedTerminalFanOuterLocalRouteAt
    center terminal.1 slot
  let outer := retainedTerminalFanOuterCompleteRoute
    center terminal slot
  let spoke := retainedTerminalFanFigure7SpokeRouteAt center slot
  have lengthPositive : 0 < terminal.2 := by
    simpa [terminal] using (show 0 < length by omega)
  have tangentOrthogonal : OrthogonalPolyline tangent :=
    retainedTerminalFanCardinalBackwardTangentRoute_orthogonal
      center port length slot distance cardinal distancePositive
  have radialHead := retainedTerminalFanOuterRadialRoute_head?
    center terminal slot
  have radialNonempty : radial ≠ [] := by
    intro empty
    change radial.head? = _ at radialHead
    rw [empty] at radialHead
    simp at radialHead
  have radialLast := retainedTerminalFanOuterRadialRoute_getLast?
    center terminal slot lengthPositive
  have localHead := retainedTerminalFanOuterLocalRouteAt_head?
    center terminal.1 slot
  have localOrthogonal : OrthogonalPolyline localRoute :=
    retainedTerminalFanOuterLocalRouteAt_orthogonal
      center terminal.1 slot
  have outerHead := retainedTerminalFanOuterCompleteRoute_head?
    center terminal slot
  have outerNonempty : outer ≠ [] := by
    intro empty
    change outer.head? = _ at outerHead
    rw [empty] at outerHead
    simp at outerHead
  have outerLast := retainedTerminalFanOuterCompleteRoute_getLast?
    center terminal slot lengthPositive
  have spokeHead := retainedTerminalFanFigure7SpokeRouteAt_head?
    center slot
  have spokeOrthogonal : OrthogonalPolyline spoke :=
    retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  have localDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline localRoute)
        (AxisDirection.unitSubdividePolyline tangent) :=
    (retainedTerminalFanOuterLocalRouteAt_strictlyAvoids_cardinalBackwardTangent
      center port length slot distance cardinal lengthLarge
    ).unitSubdividePolyline_disjoint localOrthogonal tangentOrthogonal
  have spokeDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline spoke)
        (AxisDirection.unitSubdividePolyline tangent) :=
    (retainedTerminalFanFigure7SpokeRouteAt_strictlyAvoids_cardinalBackwardTangent
      center port length slot distance cardinal lengthLarge
    ).unitSubdividePolyline_disjoint spokeOrthogonal tangentOrthogonal
  intro point tangentMember suffixMember
  change point ∈ AxisDirection.unitSubdividePolyline
    (joinAtEndpoint outer spoke) at suffixMember
  rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
    outerNonempty outerLast spokeHead] at suffixMember
  rcases mem_joinAtEndpoint suffixMember with outerMember | spokeMember
  · change point ∈ AxisDirection.unitSubdividePolyline
      (joinAtEndpoint radial localRoute) at outerMember
    rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
      radialNonempty radialLast localHead] at outerMember
    rcases mem_joinAtEndpoint outerMember with radialMember | localMember
    · exact
        retainedTerminalFanCardinalBackwardTangentRoute_only_common_radial
          center port length slot distance cardinal lengthLarge
          distancePositive point tangentMember radialMember
    · exact (localDisjoint localMember tangentMember).elim
  · exact (spokeDisjoint spokeMember tangentMember).elim

end PeriodicEightOccurrenceSplit
end LeanTrominoes
