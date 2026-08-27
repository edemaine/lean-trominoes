/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRecordData

/-! # Constant-state cursors for sparse route triples -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Stream the consecutive triples of a route while retaining only the cell
before the next direction. -/
def sparseRouteTriplesFromDirections (before : Cell) :
    List AxisDirection → List SparseRouteTriple
  | firstDirection :: secondDirection :: directions =>
      let current := Cell.add before firstDirection.step
      let after := Cell.add current secondDirection.step
      ⟨before, current, after⟩ ::
        sparseRouteTriplesFromDirections current
          (secondDirection :: directions)
  | _ => []
termination_by directions => directions.length

/-- Rebuilding the route and then taking triples agrees with the streaming
cursor, for every direction word. -/
theorem sparseRouteTriplesFromDirections_eq
    (before : Cell) (directions : List AxisDirection) :
    sparseRouteTriplesFromDirections before directions =
      sparseRouteTriples (rebuildRoute before directions) := by
  induction directions generalizing before with
  | nil =>
      simp [sparseRouteTriplesFromDirections, rebuildRoute,
        sparseRouteTriples]
  | cons firstDirection directions induction =>
      cases directions with
      | nil =>
          simp [sparseRouteTriplesFromDirections, rebuildRoute,
            sparseRouteTriples]
      | cons secondDirection directions =>
          cases directions with
          | nil =>
              simp [sparseRouteTriplesFromDirections, rebuildRoute,
                sparseRouteTriples]
          | cons thirdDirection directions =>
              simp only [sparseRouteTriplesFromDirections, rebuildRoute,
                sparseRouteTriples, List.cons.injEq, true_and]
              simpa only [sparseRouteTriplesFromDirections, rebuildRoute,
                sparseRouteTriples] using
                induction (Cell.add before firstDirection.step)

/-- Consequently a nonempty unit route's canonical triples can be streamed
directly from its first cell and computed directions. -/
theorem sparseRouteTriples_eq_from_stepDirections
    (first : Cell) (rest : List Cell)
    (unitSteps :
      (first :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    sparseRouteTriples (first :: rest) =
      sparseRouteTriplesFromDirections first
        (routeStepDirections (first :: rest)) := by
  rw [sparseRouteTriplesFromDirections_eq]
  rw [rebuildRoute_routeStepDirections first rest unitSteps]

/-- Canonical assignment-record blocks emitted by the same constant-state
route cursor. -/
def sparseRouteRecordBlocksFromDirections
    (period : Nat) (color : WireColor) (before : Cell)
    (directions : List AxisDirection) :
    List GadgetSparseAssignmentTokens.Token :=
  (sparseRouteTriplesFromDirections before directions).flatMap
    (sparseRouteTripleRecordBlock period color)

theorem sparseRouteRecordBlocks_eq_from_stepDirections
    (period : Nat) (color : WireColor)
    (first : Cell) (rest : List Cell)
    (unitSteps :
      (first :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    (sparseRouteTriples (first :: rest)).flatMap
        (sparseRouteTripleRecordBlock period color) =
      sparseRouteRecordBlocksFromDirections period color first
        (routeStepDirections (first :: rest)) := by
  unfold sparseRouteRecordBlocksFromDirections
  rw [sparseRouteTriples_eq_from_stepDirections first rest unitSteps]

end PeriodicCNFStripReduction
end LeanTrominoes
