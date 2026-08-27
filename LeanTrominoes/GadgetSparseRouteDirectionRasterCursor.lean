/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteTripleCursor
import LeanTrominoes.PeriodicThreeDMNormalizationStripDirectionStep

/-! # Raster-coordinate cursor for finite route directions

The geometric route cursor retains an unbounded lattice point and rasterizes
each emitted internal cell.  This equivalent cursor instead retains the
already-rasterized location.  Its transition uses only the common strip
period and one finite cardinal direction.
-/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Routing-cell classification from the forward direction entering the
current cell and the forward direction leaving it. -/
def routingCellTypeFromForwardDirections
    (incoming outgoing : AxisDirection) (color : WireColor) :
    OrthogonalCellType :=
  PeriodicThreeDM.routingCellType
    (PeriodicThreeDM.Side.ofAxisDirection incoming.opposite)
    (PeriodicThreeDM.Side.ofAxisDirection outgoing)
    color

/-- Two forward steps determine the same total routing-cell classification
as their three geometric lattice points, including the invalid fallback. -/
theorem routingCellTypeAt_add_steps
    (before : Cell) (incoming outgoing : AxisDirection)
    (color : WireColor) :
    PeriodicThreeDM.routingCellTypeAt before
        (Cell.add before incoming.step)
        (Cell.add (Cell.add before incoming.step) outgoing.step)
        color =
      routingCellTypeFromForwardDirections incoming outgoing color := by
  rcases before with ⟨horizontal, vertical⟩
  cases incoming <;> cases outgoing <;>
    simp [PeriodicThreeDM.routingCellTypeAt,
      routingCellTypeFromForwardDirections, AxisDirection.between,
      AxisDirection.step, AxisDirection.opposite, Cell.add]

/-- Emit canonical sparse assignment records while retaining only the
already-rasterized predecessor location. -/
def sparseRouteRecordBlocksFromRasterDirections
    (period : Nat) (color : WireColor) (beforeLocation : Cell) :
    List AxisDirection → List GadgetSparseAssignmentTokens.Token
  | incoming :: outgoing :: directions =>
      let currentLocation :=
        PeriodicThreeDM.advanceStripLocation period beforeLocation incoming
      GadgetSparseAssignmentTokens.assignmentTokens
          (currentLocation,
            routingCellTypeFromForwardDirections incoming outgoing color) ++
        sparseRouteRecordBlocksFromRasterDirections period color
          currentLocation (outgoing :: directions)
  | _ => []
termination_by directions => directions.length

/-- Starting at the rasterized first route point, the raster cursor emits
exactly the records of the geometric direction cursor. -/
theorem sparseRouteRecordBlocksFromRasterDirections_eq
    (period : Nat) (color : WireColor) (before : Cell)
    (directions : List AxisDirection) :
    sparseRouteRecordBlocksFromRasterDirections period color
        (PeriodicThreeDM.stripRasterLocation period before) directions =
      sparseRouteRecordBlocksFromDirections period color before
        directions := by
  induction directions using List.twoStepInduction generalizing before with
  | nil =>
      simp [sparseRouteRecordBlocksFromRasterDirections,
        sparseRouteRecordBlocksFromDirections,
        sparseRouteTriplesFromDirections]
  | singleton direction =>
      simp [sparseRouteRecordBlocksFromRasterDirections,
        sparseRouteRecordBlocksFromDirections,
        sparseRouteTriplesFromDirections]
  | cons_cons incoming outgoing directions _ induction =>
      simp only [sparseRouteRecordBlocksFromRasterDirections,
        sparseRouteRecordBlocksFromDirections,
        sparseRouteTriplesFromDirections, List.flatMap_cons]
      have currentLocation :
          PeriodicThreeDM.advanceStripLocation period
              (PeriodicThreeDM.stripRasterLocation period before) incoming =
            PeriodicThreeDM.stripRasterLocation period
              (Cell.add before incoming.step) :=
        (PeriodicThreeDM.stripRasterLocation_add_directionStep
          period before incoming).symm
      rw [currentLocation]
      unfold sparseRouteTripleRecordBlock sparseRouteTripleAssignment
      rw [routingCellTypeAt_add_steps before incoming outgoing color]
      rw [induction outgoing (Cell.add before incoming.step)]
      rfl

end PeriodicCNFStripReduction
end LeanTrominoes
