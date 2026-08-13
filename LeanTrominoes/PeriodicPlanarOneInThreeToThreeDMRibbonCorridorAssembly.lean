/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells

/-!
# Assembly of ribbon macrocells along a unit source route

An interior source lattice point determines one half-edge tile from its
incoming direction to its outgoing direction.  This file joins those tiles
along a unit-step source polyline.  The only additional local condition is
that the source route never immediately reverses direction; under it, every
tile is a certified straight or quarter-turn case.

Endpoint fans are a separate layer.  Accordingly, the core assembled here
starts at the boundary between the first two source points and ends at the
boundary between the final two.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Every interior vertex of a source route is straight or a quarter turn,
never an immediate reversal. -/
abbrev SourceRouteHasNoImmediateReversal :=
  AxisDirection.HasNoImmediateReversal

/-- Join one translated half-edge tile for every interior source point. -/
def ribbonCorridorCore
    (color : WireColor) : List Cell → List Cell
  | first :: second :: [] =>
      [ribbonMacrocellExit first
        (AxisDirection.between first second) color]
  | first :: center :: next :: [] =>
      ribbonMacrocellRoute center
        (AxisDirection.between first center)
        (AxisDirection.between center next) color
  | first :: center :: next :: fourth :: rest =>
      joinAtEndpoint
        (ribbonMacrocellRoute center
          (AxisDirection.between first center)
          (AxisDirection.between center next) color)
        (ribbonCorridorCore color
          (center :: next :: fourth :: rest))
  | _ => []
termination_by points => points.length

/-- Advertised variable-side boundary point of every nondegenerate core. -/
def ribbonCorridorCoreStart
    (color : WireColor) (first second : Cell) : Cell :=
  ribbonMacrocellExit first
    (AxisDirection.between first second) color

/-- Final advertised boundary point of a nonempty corridor core. -/
def ribbonCorridorCoreFinish
    (color : WireColor) :
    (first center next : Cell) → List Cell → Cell
  | _, center, next, [] =>
      ribbonMacrocellExit center
        (AxisDirection.between center next) color
  | _, center, next, fourth :: rest =>
      ribbonCorridorCoreFinish color
        center next fourth rest

/-- A one-edge source route has a one-point core at the common half-edge
boundary of its two endpoint macrocells. -/
@[simp]
theorem ribbonCorridorCore_pair
    (color : WireColor) (first second : Cell) :
    ribbonCorridorCore color [first, second] =
      [ribbonCorridorCoreStart color first second] := by
  simp [ribbonCorridorCore, ribbonCorridorCoreStart]

/-- The core begins on the first source edge's macrocell boundary. -/
theorem ribbonCorridorCore_head?
    (color : WireColor)
    (first center next : Cell) (rest : List Cell) :
    (ribbonCorridorCore color
      (first :: center :: next :: rest)).head? =
        some (ribbonMacrocellEntry center
          (AxisDirection.between first center) color) := by
  cases rest with
  | nil =>
      simp [ribbonCorridorCore]
  | cons fourth rest =>
      rw [ribbonCorridorCore]
      exact joinAtEndpoint_head?
        (ribbonMacrocellRoute_head? center
          (AxisDirection.between first center)
          (AxisDirection.between center next) color)

/-- Unit-step chains expose the first two source steps and the remaining
unit-step suffix. -/
theorem unitSteps_cons_cons_cons
    {first center next : Cell} {rest : List Cell}
    (unitSteps :
      (first :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep) :
    AxisDirection.IsUnitAxisStep first center ∧
      AxisDirection.IsUnitAxisStep center next ∧
      (center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep := by
  have firstParts := List.isChain_cons_cons.mp unitSteps
  have secondParts :=
    List.isChain_cons_cons.mp firstParts.2
  exact ⟨firstParts.1, secondParts.1, firstParts.2⟩

/-- The assembled core reaches the final source edge's macrocell boundary. -/
theorem ribbonCorridorCore_getLast?
    (color : WireColor)
    (first center next : Cell) (rest : List Cell)
    (unitSteps :
      (first :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep) :
    (ribbonCorridorCore color
      (first :: center :: next :: rest)).getLast? =
        some (ribbonCorridorCoreFinish color
          first center next rest) := by
  induction rest generalizing first center next with
  | nil =>
      simp [ribbonCorridorCore, ribbonCorridorCoreFinish]
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have parts :=
        unitSteps_cons_cons_cons unitSteps
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 color
      apply joinAtEndpoint_getLast?
        (middle := ribbonMacrocellExit center
          (AxisDirection.between center next) color)
      · exact ribbonMacrocellRoute_getLast? center
          (AxisDirection.between first center)
          (AxisDirection.between center next) color
      · rw [shared]
        exact ribbonCorridorCore_head? color
          center next fourth rest
      · simpa [ribbonCorridorCoreFinish] using
          tailInduction center next fourth parts.2.2

/-- The assembled colored corridor core is rectilinear. -/
theorem ribbonCorridorCore_orthogonal
    (color : WireColor)
    (first center next : Cell) (rest : List Cell)
    (unitSteps :
      (first :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (first :: center :: next :: rest)) :
    OrthogonalPolyline
      (ribbonCorridorCore color
        (first :: center :: next :: rest)) := by
  induction rest generalizing first center next with
  | nil =>
      rw [ribbonCorridorCore]
      have parts :=
        unitSteps_cons_cons_cons unitSteps
      apply ribbonMacrocellRoute_orthogonal
      · exact
          AxisDirection.between_isGenuine_of_unitAxisStep
            parts.1
      · exact
          AxisDirection.between_isGenuine_of_unitAxisStep
            parts.2.1
      · exact noReversal.1
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have parts :=
        unitSteps_cons_cons_cons unitSteps
      have firstOrthogonal :=
        ribbonMacrocellRoute_orthogonal center
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.2.1)
          noReversal.1 color
      have tailOrthogonal :=
        tailInduction center next fourth
          parts.2.2 noReversal.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 color
      apply firstOrthogonal.joinAtEndpoint
        tailOrthogonal
        (ribbonMacrocellRoute_getLast? center
          (AxisDirection.between first center)
          (AxisDirection.between center next) color)
      rw [shared]
      exact ribbonCorridorCore_head? color
        center next fourth rest

/-- Total final boundary point for a source route with at least two points. -/
def ribbonCorridorCoreEnd
    (color : WireColor)
    (first second : Cell) : List Cell → Cell
  | [] =>
      ribbonCorridorCoreStart color first second
  | next :: rest =>
      ribbonCorridorCoreFinish color
        first second next rest

/-- Exact endpoints of every unit-step core with at least two source points. -/
theorem ribbonCorridorCore_endpoints
    (color : WireColor)
    (first second : Cell) (rest : List Cell)
    (unitSteps :
      (first :: second :: rest).IsChain
        AxisDirection.IsUnitAxisStep) :
    (ribbonCorridorCore color
        (first :: second :: rest)).head? =
        some (ribbonCorridorCoreStart color first second) ∧
      (ribbonCorridorCore color
        (first :: second :: rest)).getLast? =
        some (ribbonCorridorCoreEnd color
          first second rest) := by
  cases rest with
  | nil =>
      simp [ribbonCorridorCoreStart,
        ribbonCorridorCoreEnd]
  | cons next rest =>
      have firstStep :=
        (List.isChain_cons_cons.mp unitSteps).1
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          firstStep color
      constructor
      · rw [ribbonCorridorCore_head?]
        exact congrArg some shared.symm
      · simpa [ribbonCorridorCoreEnd] using
          ribbonCorridorCore_getLast? color
            first second next rest unitSteps

/-- Every certified unit-step source route with at least two points has a
rectilinear colored core, including the one-edge case. -/
theorem ribbonCorridorCore_orthogonal_of_cons_cons
    (color : WireColor)
    (first second : Cell) (rest : List Cell)
    (unitSteps :
      (first :: second :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (first :: second :: rest)) :
    OrthogonalPolyline
      (ribbonCorridorCore color
        (first :: second :: rest)) := by
  cases rest with
  | nil =>
      simp [OrthogonalPolyline]
  | cons next rest =>
      exact ribbonCorridorCore_orthogonal color
        first second next rest unitSteps noReversal

/-- Total advertised first boundary point of a source route. -/
def ribbonCorridorRouteStart
    (color : WireColor) : List Cell → Cell
  | first :: second :: _ =>
      ribbonCorridorCoreStart color first second
  | _ => (0, 0)

/-- Total advertised final boundary point of a source route. -/
def ribbonCorridorRouteEnd
    (color : WireColor) : List Cell → Cell
  | first :: second :: rest =>
      ribbonCorridorCoreEnd color first second rest
  | _ => (0, 0)

/-- Exact endpoints of every nondegenerate unit-step source route. -/
theorem ribbonCorridorCore_endpoints_of_length_ge_two
    (color : WireColor) {points : List Cell}
    (length : 2 ≤ points.length)
    (unitSteps :
      points.IsChain AxisDirection.IsUnitAxisStep) :
    (ribbonCorridorCore color points).head? =
        some (ribbonCorridorRouteStart color points) ∧
      (ribbonCorridorCore color points).getLast? =
        some (ribbonCorridorRouteEnd color points) := by
  cases points with
  | nil =>
      simp at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp at length
      | cons second rest =>
          simpa [ribbonCorridorRouteStart,
            ribbonCorridorRouteEnd] using
            ribbonCorridorCore_endpoints color
              first second rest unitSteps

/-- Rectilinearity of every nondegenerate certified unit-step source route. -/
theorem ribbonCorridorCore_orthogonal_of_length_ge_two
    (color : WireColor) {points : List Cell}
    (length : 2 ≤ points.length)
    (unitSteps :
      points.IsChain AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal points) :
    OrthogonalPolyline (ribbonCorridorCore color points) := by
  cases points with
  | nil =>
      simp at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp at length
      | cons second rest =>
          exact
            ribbonCorridorCore_orthogonal_of_cons_cons
              color first second rest unitSteps noReversal

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
