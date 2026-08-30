/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateTangentData

/-! # Cardinal source segments ahead of retained-fan gates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A two-point source segment ending at a cardinal fan gate from the same
side as the fan's clockwise occurrence-lane shift. -/
def retainedTerminalFanCardinalForwardTangentRoute
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  [Cell.add gate
      (Cell.scale distance
        (retainedTerminalFanOuterLaneStep (.compass port))),
    gate]

@[simp]
theorem retainedTerminalFanCardinalForwardTangentRoute_head?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) :
    (retainedTerminalFanCardinalForwardTangentRoute
      center port length slot distance).head? =
      some
        (Cell.add
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
  rfl

@[simp]
theorem retainedTerminalFanCardinalForwardTangentRoute_getLast?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) :
    (retainedTerminalFanCardinalForwardTangentRoute
      center port length slot distance).getLast? =
      some
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  rfl

/-- A positive cardinal forward tangent is an orthogonal two-point route. -/
theorem retainedTerminalFanCardinalForwardTangentRoute_orthogonal
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
      (retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  change OrthogonalPolyline
    [Cell.add gate
      (Cell.scale distance
        (retainedTerminalFanOuterLaneStep (.compass port))), gate]
  rcases gate with ⟨gateX, gateY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [OrthogonalPolyline,
      retainedTerminalFanOuterLaneStep,
      GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      Cell.add, Cell.scale] at distancePositive ⊢ <;>
    omega

/-- Every listed point on a cardinal forward tangent has the gate's exact
outward coordinate. -/
theorem retainedTerminalFanCardinalForwardTangentRoute_side_value
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) point =
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  unfold retainedTerminalFanCardinalForwardTangentRoute at pointMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pointMember
  rcases pointMember with rfl | rfl
  · rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [retainedTerminalFanOuterSideNormal,
        retainedTerminalFanOuterLaneStep,
        Cell.linearValue, Cell.add, Cell.scale]
  · rfl

/-- The finite local fan adapter strictly avoids every cardinal forward
tangent at a terminal of length at least two. -/
theorem retainedTerminalFanOuterLocalRouteAt_strictlyAvoids_cardinalForwardTangent
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center (.compass port) slot)
      (retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterSideNormal (.compass port))
    (Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) center + 288)
  · intro point pointMember
    exact retainedTerminalFanOuterLocalRouteAt_side_upper
      center (.compass port) (.compass port) slot point pointMember
  · intro point pointMember
    rw [retainedTerminalFanCardinalForwardTangentRoute_side_value
      center port length slot distance cardinal point pointMember]
    exact retainedTerminalFanOuterDemand_cardinal_side_lower
      center port length slot cardinal lengthLarge

/-- The matching Figure 7 spoke strictly avoids every cardinal forward
tangent at a terminal of length at least two. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_strictlyAvoids_cardinalForwardTangent
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanFigure7SpokeRouteAt center slot)
      (retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterSideNormal (.compass port))
    (Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) center + 96)
  · intro point pointMember
    exact retainedTerminalFanFigure7SpokeRouteAt_side_upper
      center (.compass port) slot point pointMember
  · intro point pointMember
    rw [retainedTerminalFanCardinalForwardTangentRoute_side_value
      center port length slot distance cardinal point pointMember]
    have gateLower := retainedTerminalFanOuterDemand_cardinal_side_lower
      center port length slot cardinal lengthLarge
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
