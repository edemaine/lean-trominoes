/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLinearSeparation
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterRadialPrefixes

/-! # Cardinal source segments behind retained-fan gates

An ordinary carrier enters its fallback gate tangentially to the retained
interface square.  This file names the segment immediately behind that gate
and separates it from the finite local fan and Figure 7 spoke.  The radial
lane starting at the gate is handled separately.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A two-point source segment of the given length ending at a cardinal fan
gate, opposite to the fan's clockwise tangential lane direction. -/
def retainedTerminalFanCardinalBackwardTangentRoute
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  [Cell.add gate
      (Cell.scale (-(distance : Int))
        (retainedTerminalFanOuterLaneStep (.compass port))),
    gate]

/-- Every point listed on a cardinal backward tangent has the gate's exact
outward coordinate. -/
theorem retainedTerminalFanCardinalBackwardTangentRoute_side_value
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
      point ∈ retainedTerminalFanCardinalBackwardTangentRoute
        center port length slot distance) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) point =
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  unfold retainedTerminalFanCardinalBackwardTangentRoute at pointMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pointMember
  rcases pointMember with rfl | rfl
  · rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [retainedTerminalFanOuterSideNormal,
        retainedTerminalFanOuterLaneStep,
        Cell.linearValue, Cell.add, Cell.scale]
  · rfl

/-- A cardinal gate for a terminal of length at least two lies strictly
outside the radius-288 supporting line of the local fan. -/
theorem retainedTerminalFanOuterDemand_cardinal_side_lower
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal (.compass port)) center +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  rcases center with ⟨centerX, centerY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalFanOuterSideNormal,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive,
      Port.unitVector, Cell.linearValue, Cell.add, Cell.scale] <;>
    omega

/-- A positioned Figure 7 spoke lies on the weak inner side of every
retained terminal direction's radius-96 supporting line. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_side_upper
    (center : Cell)
    (sideDirection : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanFigure7SpokeRouteAt center slot) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal sideDirection) point ≤
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal sideDirection) center +
        96 := by
  rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨offset, offsetMember, rfl⟩
  have upper := retainedTerminalFanCenteredFigure7Spoke_side_upper
    sideDirection slot offset offsetMember
  rcases center with ⟨centerX, centerY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases sideDirection with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterSideNormal,
      Cell.linearValue, Cell.add] at upper ⊢ <;>
    omega

/-- The complete finite local adapter is contact-free from every positive
length cardinal source segment immediately behind its gate. -/
theorem retainedTerminalFanOuterLocalRouteAt_strictlyAvoids_cardinalBackwardTangent
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
      (retainedTerminalFanCardinalBackwardTangentRoute
        center port length slot distance) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterSideNormal (.compass port))
    (Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) center + 288)
  · intro point pointMember
    exact retainedTerminalFanOuterLocalRouteAt_side_upper
      center (.compass port) (.compass port) slot point pointMember
  · intro point pointMember
    rw [retainedTerminalFanCardinalBackwardTangentRoute_side_value
      center port length slot distance cardinal point pointMember]
    exact retainedTerminalFanOuterDemand_cardinal_side_lower
      center port length slot cardinal lengthLarge

/-- The matching Figure 7 spoke is contact-free from every positive-length
cardinal source segment immediately behind its gate. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_strictlyAvoids_cardinalBackwardTangent
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
      (retainedTerminalFanCardinalBackwardTangentRoute
        center port length slot distance) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterSideNormal (.compass port))
    (Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) center + 96)
  · intro point pointMember
    exact retainedTerminalFanFigure7SpokeRouteAt_side_upper
      center (.compass port) slot point pointMember
  · intro point pointMember
    rw [retainedTerminalFanCardinalBackwardTangentRoute_side_value
      center port length slot distance cardinal point pointMember]
    have gateLower := retainedTerminalFanOuterDemand_cardinal_side_lower
      center port length slot cardinal lengthLarge
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
