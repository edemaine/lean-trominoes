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
def SourceRouteHasNoImmediateReversal : List Cell → Prop
  | first :: center :: next :: rest =>
      AxisDirection.between center next ≠
          (AxisDirection.between first center).opposite ∧
        SourceRouteHasNoImmediateReversal
          (center :: next :: rest)
  | _ => True

/-- Join one translated half-edge tile for every interior source point. -/
def ribbonCorridorCore
    (color : WireColor) : List Cell → List Cell
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

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
