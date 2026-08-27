/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineAdvanceExecution

/-! # Route-loop data for the complement-counter machine -/

namespace LeanTrominoes

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

/-- Tokens remaining after the machine consumes the first nondirection
terminator. -/
def stopTail : List InputToken → List InputToken
  | [] => []
  | _ :: tokens => tokens

/-- Finite state retained on entry to output reversal. -/
def stopState : List InputToken → State
  | [] => none
  | token :: _ => inputState token

/-- A suffix at which the maximal direction scan must stop. -/
def StopsDirections : List InputToken → Prop
  | [] => True
  | token :: _ => isDirectionState (inputState token) = false

/-- Canonical records still to emit after `incoming` has already advanced
the location and the machine is waiting for its outgoing lookahead. -/
def outgoingBlocks (color : Gadget.WireColor) :
    ComplementLocation → AxisDirection → List AxisDirection →
      List OutputToken
  | _, _, [] => []
  | current, incoming, outgoing :: directions =>
      GadgetSparseAssignmentTokens.assignmentTokens
          (current.toNatHorizontal.toCell,
            routingCellTypeFromForwardDirections incoming outgoing color) ++
        outgoingBlocks color (advanceComplementLocation current outgoing)
          outgoing directions

/-- The lookahead recurrence is exactly the original complement-cursor
stream once the incoming transition has been taken. -/
theorem outgoingBlocks_eq_sparseRouteRecordBlocks
    (color : Gadget.WireColor) (before : ComplementLocation)
    (incoming : AxisDirection) (directions : List AxisDirection) :
    outgoingBlocks color (advanceComplementLocation before incoming)
        incoming directions =
      sparseRouteRecordBlocksFromComplementDirections color before
        (incoming :: directions) := by
  induction directions generalizing before incoming with
  | nil =>
      simp [outgoingBlocks,
        sparseRouteRecordBlocksFromComplementDirections]
  | cons outgoing directions induction =>
      simp only [outgoingBlocks,
        sparseRouteRecordBlocksFromComplementDirections]
      rw [induction (advanceComplementLocation before incoming) outgoing]

/-- Cost of copying one current coordinate into an assignment record. -/
def recordTime (location : ComplementLocation) : Nat :=
  2 * location.horizontal +
    2 * signedPositive location.vertical + 5

/-- Exact allowance from an outgoing-lookahead configuration to reversal. -/
def outgoingTime : ComplementLocation → List AxisDirection → Nat
  | _, [] => 1
  | location, outgoing :: directions =>
      1 + recordTime location + advanceTime location outgoing +
        outgoingTime (advanceComplementLocation location outgoing) directions

/-- Exact allowance from the initial incoming-direction scan to reversal. -/
def routeTime : ComplementLocation → List AxisDirection → Nat
  | _, [] => 1
  | before, incoming :: directions =>
      1 + advanceTime before incoming +
        outgoingTime (advanceComplementLocation before incoming) directions

/-- The coordinate-copy contribution is the reverse of the exact semantic
assignment record at the current complement location. -/
theorem location_recordReverse_eq (location : ComplementLocation)
    (cellType : Gadget.OrthogonalCellType) :
    verticalReverse (signedPositive location.vertical) cellType ++
        horizontalReverse location.horizontal =
      (GadgetSparseAssignmentTokens.assignmentTokens
        (location.toNatHorizontal.toCell, cellType)).reverse := by
  rcases location with ⟨horizontal, complement, vertical⟩
  unfold signedPositive NatHorizontalLocation.toCell
    ComplementLocation.toNatHorizontal
    GadgetSparseAssignmentTokens.assignmentTokens
    verticalReverse horizontalReverse
  simp [List.append_assoc]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
