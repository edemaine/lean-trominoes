/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestRoundCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Complete dynamic three-round direction compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Computability Turing
open NormalizationCompiler

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Apply the same physical retained-request machine for all three rounds. -/
def threeRoundTokenOutput (tokens : List Token) : List Token :=
  roundTokenOutput .final
    (roundTokenOutput .second (roundTokenOutput .first tokens))

theorem threeRoundTokenOutput_request (input : Request) :
    threeRoundTokenOutput input.tokens =
      (normalizeThreeRounds input).tokens := by
  unfold threeRoundTokenOutput normalizeThreeRounds
  rw [roundTokenOutput_request .first input]
  rw [roundTokenOutput_request .second (normalizeRound .first input)]
  rw [roundTokenOutput_request .final
    (normalizeRound .second (normalizeRound .first input))]

noncomputable def threeRoundTokenOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id threeRoundTokenOutput := by
  let first := roundTokenOutputComputableInPolyTime .first
  let second := TM2CompositionMachine.computableInPolyTime first
    (roundTokenOutputComputableInPolyTime .second)
  let final := TM2CompositionMachine.computableInPolyTime second
    (roundTokenOutputComputableInPolyTime .final)
  change TM2ComputableInPolyTime id id
    (fun tokens => roundTokenOutput .final
      (roundTokenOutput .second (roundTokenOutput .first tokens)))
  exact final

def directionBlock : Token → List AxisDirection
  | .direction direction => [direction]
  | _ => []

def projectedDirections (tokens : List Token) : List AxisDirection :=
  tokens.flatMap directionBlock

@[simp]
theorem projectedDirections_request (input : Request) :
    projectedDirections input.tokens = input.directions := by
  unfold projectedDirections Request.tokens Header.tokens
  simp [directionBlock, List.flatMap_map]

noncomputable def projectedDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id projectedDirections := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap directionBlock)
  exact FiniteBlockTransducer.computableInPolyTime directionBlock

def threeRoundDirectionsOutput (tokens : List Token) :
    List AxisDirection :=
  projectedDirections (threeRoundTokenOutput tokens)

theorem threeRoundDirectionsOutput_request (input : Request) :
    threeRoundDirectionsOutput input.tokens =
      (normalizeThreeRounds input).directions := by
  unfold threeRoundDirectionsOutput
  rw [threeRoundTokenOutput_request, projectedDirections_request]

noncomputable def threeRoundDirectionsOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id threeRoundDirectionsOutput := by
  change TM2ComputableInPolyTime id id
    (fun tokens => projectedDirections (threeRoundTokenOutput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    threeRoundTokenOutputComputableInPolyTime
    projectedDirectionsComputableInPolyTime

/-- A canonical finite request is compiled to its complete normalized
direction stream in polynomial time. -/
noncomputable def normalizeThreeRoundsDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime Request.tokens id
      (fun input => (normalizeThreeRounds input).directions) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    Request.tokens threeRoundDirectionsOutputComputableInPolyTime
    (fun _ => rfl) threeRoundDirectionsOutput_request

/-- Specialization to the exact request associated with a data-only edge. -/
noncomputable def finalNormalizationRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun input : NormalizationCompiler.Input × ContractedEdge =>
        (ofEdge input.1 input.2).tokens)
      id
      (fun input => finalNormalizationRouteDirections input.1 input.2) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    (fun input : NormalizationCompiler.Input × ContractedEdge =>
      ofEdge input.1 input.2)
    normalizeThreeRoundsDirectionsComputableInPolyTime
    (fun _ => rfl)
    (fun input => normalizeThreeRounds_ofEdge_directions input.1 input.2)

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
