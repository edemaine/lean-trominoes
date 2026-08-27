/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineRouteData

/-! # Exact direction-loop execution of the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

def directionInput (directions : List AxisDirection)
    (stop : List InputToken) : List InputToken :=
  directions.map (fun direction =>
    GadgetSparseRouteRasterNormalizedTokens.Token.direction direction) ++ stop

/-- Semantic location after a finite direction suffix. -/
def advanceDirections : ComplementLocation → List AxisDirection →
    ComplementLocation
  | location, [] => location
  | location, direction :: directions =>
      advanceDirections (advanceComplementLocation location direction)
        directions

/-- Specialize the generic copy loops to a semantic complement location. -/
def recordAtLocation_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (input : List InputToken) (location : ComplementLocation)
    (outputReverse output : List OutputToken) :
    let record := GadgetSparseAssignmentTokens.assignmentTokens
      (location.toNatHorizontal.toCell,
        routingCellTypeFromForwardDirections incoming outgoing color)
    EvalsToInTime (TM2.step program)
      (beginRecordCfg color incoming outgoing (inputState (.direction outgoing))
        (locationData input location outputReverse output))
      (some (advanceCfg color outgoing none
        (locationData input location (record.reverse ++ outputReverse) output)))
      (recordTime location) := by
  dsimp only
  let horizontal := List.replicate location.horizontal ()
  let positive := List.replicate (signedPositive location.vertical) ()
  have execution := record_evalsInTime color incoming outgoing
    horizontal positive (locationData input location outputReverse output)
    (by simp [horizontal, locationData])
    (by simp [positive, locationData]) (by simp [locationData])
  convert execution using 1
  · simp [locationData, horizontal, positive,
      location_recordReverse_eq]
  · simp [recordTime, horizontal, positive]

/-- Exact execution after the incoming direction has already advanced the
location and the machine is waiting for its outgoing lookahead. -/
def outgoing_evalsInTime (color : Gadget.WireColor)
    (current : ComplementLocation) (incoming : AxisDirection)
    (directions : List AxisDirection) (stop : List InputToken)
    (outputReverse output : List OutputToken)
    (stops : StopsDirections stop) :
    EvalsToInTime (TM2.step program)
      (scanOutgoingCfg color incoming
        (locationData (directionInput directions stop) current
          outputReverse output))
      (some (cfg .reverseOutput (stopState stop)
        (locationData (stopTail stop)
          (advanceDirections current directions)
          ((outgoingBlocks color current incoming directions).reverse ++
            outputReverse) output)))
      (outgoingTime current directions) := by
  induction directions generalizing current incoming outputReverse with
  | nil =>
      cases stop with
      | nil =>
          have step := oneStep (step_scanOutgoing_nil
            (locationData [] current outputReverse output)
            color incoming (by simp [locationData]))
          convert step using 1 <;>
            simp [directionInput, stopState, stopTail, outgoingBlocks,
              outgoingTime, advanceDirections, locationData,
              reverseOutputCfg, labelCfg]
      | cons token tokens =>
          have notDirection :
              isDirectionState (inputState token) = false := stops
          have step := oneStep (step_scanOutgoing_other
            (locationData (token :: tokens) current outputReverse output)
            color incoming token tokens (by
              simp [locationData]) notDirection)
          convert step using 1 <;>
            simp [directionInput, stopState, stopTail, outgoingBlocks,
              outgoingTime, advanceDirections, locationData]
  | cons outgoing directions induction =>
      let remainingInput := directionInput directions stop
      let initial := locationData
        (.direction outgoing :: remainingInput) current outputReverse output
      let afterScan := locationData remainingInput current outputReverse output
      let cellType := routingCellTypeFromForwardDirections
        incoming outgoing color
      let record := GadgetSparseAssignmentTokens.assignmentTokens
        (current.toNatHorizontal.toCell, cellType)
      let afterRecord := locationData remainingInput current
        (record.reverse ++ outputReverse) output
      let next := advanceComplementLocation current outgoing
      have scanned := oneStep (step_scanOutgoing_direction initial color
        incoming outgoing remainingInput (by
          simp [initial, locationData]))
      have recorded := recordAtLocation_evalsInTime color incoming outgoing
        remainingInput current outputReverse output
      have advanced := advance_evalsInTime color outgoing none
        remainingInput current (record.reverse ++ outputReverse) output
      have rest := induction next outgoing
        (record.reverse ++ outputReverse)
      have throughRecord := EvalsToInTime.trans (TM2.step program)
        1 (recordTime current)
        (scanOutgoingCfg color incoming initial)
        (beginRecordCfg color incoming outgoing (inputState (.direction outgoing))
          afterScan)
        (some (advanceCfg color outgoing none afterRecord))
        (by simpa [initial, afterScan, locationData] using scanned)
        (by simpa [afterRecord, record, cellType] using recorded)
      have throughAdvance := EvalsToInTime.trans (TM2.step program)
        (recordTime current + 1) (advanceTime current outgoing)
        (scanOutgoingCfg color incoming initial)
        (advanceCfg color outgoing none afterRecord)
        (some (scanOutgoingCfg color outgoing
          (locationData remainingInput next
            (record.reverse ++ outputReverse) output)))
        (by simpa [Nat.add_comm] using throughRecord)
        (by simpa [afterRecord, next] using advanced)
      have whole := EvalsToInTime.trans (TM2.step program)
        (advanceTime current outgoing + (recordTime current + 1))
        (outgoingTime next directions)
        (scanOutgoingCfg color incoming initial)
        (scanOutgoingCfg color outgoing
          (locationData remainingInput next
            (record.reverse ++ outputReverse) output))
        (some (cfg .reverseOutput (stopState stop)
          (locationData (stopTail stop)
            (advanceDirections next directions)
            ((outgoingBlocks color next outgoing directions).reverse ++
              (record.reverse ++ outputReverse)) output)))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          throughAdvance)
        (by simpa [next] using rest)
      convert whole using 1
      · simp only [initial, remainingInput, directionInput, List.map_cons,
          List.cons_append]
      · simp [outgoingBlocks, advanceDirections, next, record, cellType,
          List.reverse_append, List.append_assoc]
      · simp [outgoingTime, recordTime, next]
        omega

/-- Exact execution of a maximal direction prefix from the initial incoming
scan to output reversal. -/
def route_evalsInTime (color : Gadget.WireColor)
    (state : State)
    (before : ComplementLocation) (directions : List AxisDirection)
    (stop : List InputToken) (outputReverse output : List OutputToken)
    (stops : StopsDirections stop) :
    EvalsToInTime (TM2.step program)
      (cfg (.scanIncoming color) state
        (locationData (directionInput directions stop) before
          outputReverse output))
      (some (cfg .reverseOutput (stopState stop)
        (locationData (stopTail stop)
          (advanceDirections before directions)
          ((sparseRouteRecordBlocksFromComplementDirections
              color before directions).reverse ++ outputReverse) output)))
      (routeTime before directions) := by
  cases directions with
  | nil =>
      cases stop with
      | nil =>
          have step := oneStep (step_scanIncoming_nil state
            (locationData [] before outputReverse output) color (by
              simp [locationData]))
          convert step using 1 <;>
            simp [directionInput, stopState, stopTail, routeTime,
              advanceDirections,
              sparseRouteRecordBlocksFromComplementDirections,
              locationData, reverseOutputCfg, labelCfg]
      | cons token tokens =>
          have notDirection :
              isDirectionState (inputState token) = false := stops
          have step := oneStep (step_scanIncoming_other state
            (locationData (token :: tokens) before outputReverse output)
            color token tokens (by simp [locationData])
            notDirection)
          convert step using 1 <;>
            simp [directionInput, stopState, stopTail, routeTime,
              advanceDirections,
              sparseRouteRecordBlocksFromComplementDirections,
              locationData]
  | cons incoming directions =>
      let remainingInput := directionInput directions stop
      let afterScan := locationData remainingInput before outputReverse output
      let current := advanceComplementLocation before incoming
      have scanned := oneStep (step_scanIncoming_direction state
        (locationData (.direction incoming :: remainingInput)
          before outputReverse output)
        color incoming remainingInput (by simp [locationData]))
      have advanced := advance_evalsInTime color incoming
        (inputState (.direction incoming)) remainingInput before
        outputReverse output
      have rest := outgoing_evalsInTime color current incoming
        directions stop outputReverse output stops
      have throughAdvance := EvalsToInTime.trans (TM2.step program)
        1 (advanceTime before incoming)
        (cfg (.scanIncoming color) state
          (locationData (.direction incoming :: remainingInput)
            before outputReverse output))
        (advanceCfg color incoming (inputState (.direction incoming))
          afterScan)
        (some (scanOutgoingCfg color incoming
          (locationData remainingInput current outputReverse output)))
        (by simpa [afterScan, locationData] using scanned)
        (by simpa [afterScan, current] using advanced)
      have whole := EvalsToInTime.trans (TM2.step program)
        (advanceTime before incoming + 1)
        (outgoingTime current directions)
        (cfg (.scanIncoming color) state
          (locationData (.direction incoming :: remainingInput)
            before outputReverse output))
        (scanOutgoingCfg color incoming
          (locationData remainingInput current outputReverse output))
        (some (cfg .reverseOutput (stopState stop)
          (locationData (stopTail stop)
            (advanceDirections current directions)
            ((outgoingBlocks color current incoming directions).reverse ++
              outputReverse) output)))
        (by simpa [Nat.add_comm] using throughAdvance)
        (by simpa [current] using rest)
      convert whole using 1
      · simp only [remainingInput, directionInput, List.map_cons,
          List.cons_append]
      · simp [advanceDirections, current,
          outgoingBlocks_eq_sparseRouteRecordBlocks]
      · simp [routeTime, current]
        omega

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
