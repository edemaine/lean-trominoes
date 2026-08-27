/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionRequestCompiler
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Compiler for compact routed horizontal occurrence requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalOccurrenceRoutedRequest

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Finite frame alphabet retained while the routed source word is compiled. -/
inductive FrameToken
  | leading (query : HorizontalFiniteIncidenceDirectionQuery)
  | lane (color : Gadget.WireColor)
  | trailing (query : HorizontalFiniteIncidenceDirectionQuery)
  deriving DecidableEq, Fintype

instance : Inhabited FrameToken := ⟨.lane .red⟩

def frameBlock : Token → List FrameToken
  | .leading query => [.leading query]
  | .lane color => [.lane color]
  | .routed _ => []
  | .trailing query => [.trailing query]

def routeBlock : Token → List HorizontalRoutedRouteDirectionRequest.Token
  | .routed token => [token]
  | _ => []

def frameTokens (input : List Token) : List FrameToken :=
  input.flatMap frameBlock

def routeTokens (input : List Token) :
    List HorizontalRoutedRouteDirectionRequest.Token :=
  input.flatMap routeBlock

@[simp] theorem frameTokens_tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (route : HorizontalRoutedRouteDirectionBlock)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    frameTokens (tokens leading lane route trailing) =
      [.leading leading, .lane lane, .trailing trailing] := by
  simp [frameTokens, tokens, frameBlock, List.flatMap_map]

@[simp] theorem routeTokens_tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (route : HorizontalRoutedRouteDirectionBlock)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    routeTokens (tokens leading lane route trailing) =
      HorizontalRoutedRouteDirectionRequest.tokens route := by
  simp [routeTokens, tokens, routeBlock, List.flatMap_map]

noncomputable def frameTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id frameTokens := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap frameBlock)
  exact FiniteBlockTransducer.computableInPolyTime frameBlock

noncomputable def routeTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id routeTokens := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap routeBlock)
  exact FiniteBlockTransducer.computableInPolyTime routeBlock

def routeDirections (input : List Token) : List AxisDirection :=
  HorizontalRoutedRouteDirectionRequest.output (routeTokens input)

noncomputable def routeDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id routeDirections := by
  let complete := TM2CompositionMachine.computableInPolyTime
    routeTokensComputableInPolyTime
    HorizontalRoutedRouteDirectionRequest.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => HorizontalRoutedRouteDirectionRequest.output
      (routeTokens input))
  exact complete

/-- Finite control stores the complete frame while scanning the separated
frame/direction pair. -/
structure State where
  leading : HorizontalFiniteIncidenceDirectionQuery
  lane : Gadget.WireColor
  trailing : HorizontalFiniteIncidenceDirectionQuery
  deriving DecidableEq, Fintype

instance : Inhabited State := ⟨⟨default, .red, default⟩⟩

def initial : State := ⟨default, .red, default⟩

abbrev SeparatedToken :=
  SeparatedProductEncoding.Token FrameToken AxisDirection

def transition (state : State) : SeparatedToken →
    State × List HorizontalOccurrenceDirectionRequest.Token
  | .left (.leading query) => (⟨query, state.lane, state.trailing⟩, [])
  | .left (.lane color) => (⟨state.leading, color, state.trailing⟩, [])
  | .left (.trailing query) => (⟨state.leading, state.lane, query⟩, [])
  | .separator =>
      (state, [.finite state.leading, .lane state.lane])
  | .right direction => (state, [.direction direction])

def finish (state : State) :
    List HorizontalOccurrenceDirectionRequest.Token :=
  [.finite state.trailing]

def preparedOutput (input : List SeparatedToken) :
    List HorizontalOccurrenceDirectionRequest.Token :=
  FiniteStateTransducer.output initial transition finish input

@[simp] theorem scan_right (state : State)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition state
        (directions.map SeparatedProductEncoding.Token.right) =
      (state,
        directions.map HorizontalOccurrenceDirectionRequest.Token.direction) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

@[simp] theorem preparedOutput_encode
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (directions : List AxisDirection)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    preparedOutput
        (SeparatedProductEncoding.encode id id
          ([FrameToken.leading leading, .lane lane, .trailing trailing],
            directions)) =
      HorizontalOccurrenceDirectionRequest.tokens
        leading lane directions trailing := by
  unfold preparedOutput HorizontalOccurrenceDirectionRequest.tokens
    SeparatedProductEncoding.encode FiniteStateTransducer.output
  simp [FiniteStateTransducer.scan, transition, finish, initial]

noncomputable def preparedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedOutput :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

noncomputable def preparedPairComputableInPolyTime :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode id id) id
      (fun pair : List FrameToken × List AxisDirection =>
        preparedOutput (SeparatedProductEncoding.encode id id pair)) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode id id)
    preparedOutputComputableInPolyTime
    (fun _ => rfl)
    (fun _ => rfl)

def prepared (input : List Token) :
    List HorizontalOccurrenceDirectionRequest.Token :=
  preparedOutput (SeparatedProductEncoding.encode id id
    (frameTokens input, routeDirections input))

noncomputable def preparedComputableInPolyTime :
    TM2ComputableInPolyTime id id prepared := by
  let forked := TM2ForkMachine.computableInPolyTime
    frameTokensComputableInPolyTime routeDirectionsComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime forked
    preparedPairComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => preparedOutput (SeparatedProductEncoding.encode id id
      (frameTokens input, routeDirections input)))
  exact complete

def output (input : List Token) : List AxisDirection :=
  HorizontalOccurrenceDirectionRequest.output (prepared input)

@[simp] theorem output_tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (route : HorizontalRoutedRouteDirectionBlock)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    output (tokens leading lane route trailing) =
      HorizontalOccurrenceDirectionRequest.requestedOutput leading lane
        (horizontalOccurrenceSourceDirections route) trailing := by
  unfold output prepared routeDirections
  rw [frameTokens_tokens, routeTokens_tokens,
    HorizontalRoutedRouteDirectionRequest.output_tokens,
    preparedOutput_encode,
    HorizontalOccurrenceDirectionRequest.output_tokens]

/-- Canonical finite frame surrounding one classified routed block at its
actual horizontal occurrence query. -/
def semanticTokens
    (input : HorizontalOccurrenceColoredRouteInput)
    (route : HorizontalRoutedRouteDirectionBlock) : List Token :=
  tokens
    (.variableStub
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).1
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.1
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.2)
    (horizontalOccurrenceRibbonLaneComputed input)
    route
    (.clauseStub
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).1
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.1
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.2)

/-- The compact routed request compiles to the exact complete coordinated
occurrence direction word. -/
@[simp] theorem output_semanticTokens
    (input : HorizontalOccurrenceColoredRouteInput)
    (route : HorizontalRoutedRouteDirectionBlock) :
    output (semanticTokens input route) =
      horizontalOccurrenceCoordinatedDirections input route := by
  unfold semanticTokens
  rw [output_tokens]
  unfold HorizontalOccurrenceDirectionRequest.requestedOutput
    horizontalOccurrenceCoordinatedDirections
  rw [HorizontalFiniteIncidenceDirectionQuery.directions_variableStub_input,
    HorizontalFiniteIncidenceDirectionQuery.directions_clauseStub_input]
  rfl

/-- The fixed frame fork, routed-word compiler, joiner, and occurrence scan
form one polynomial-time compiler. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  let complete := TM2CompositionMachine.computableInPolyTime
    preparedComputableInPolyTime
    HorizontalOccurrenceDirectionRequest.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => HorizontalOccurrenceDirectionRequest.output
      (prepared input))
  exact complete

end HorizontalOccurrenceRoutedRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
