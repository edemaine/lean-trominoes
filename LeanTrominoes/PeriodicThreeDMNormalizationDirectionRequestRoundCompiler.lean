/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestDropFirstCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestDropLastCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestExpansionCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestWrapperCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # One complete dynamic normalization round -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Computability Turing
open Gadget

/-- List-level endpoint trimming fact used between expansion and wrapping. -/
theorem drop_first_last_eq_trimThreeDirections
    (directions : List AxisDirection) :
    (directions.drop 3).take ((directions.drop 3).length - 3) =
      trimThreeDirections directions := by
  rw [← DirectionTrim.transducerOutput_eq_trimThreeDirections directions]
  unfold DirectionTrim.transducerOutput
  rw [DirectionTrim.DropFirstThree.output_eq_drop,
    DirectionTrim.DropLastThree.output_eq_take]

/-- Semantic request obtained by the four physical passes. -/
def physicalRoundRequest (round : Round) (input : Request) : Request :=
  Wrapper.request round
    (DropLast.request (DropFirst.request (expandRequest input)))

theorem physicalRoundRequest_eq_normalizeRound
    (round : Round) (input : Request) :
    physicalRoundRequest round input = normalizeRound round input := by
  rcases input with ⟨header, directions⟩
  unfold physicalRoundRequest Wrapper.request DropLast.request
      DropFirst.request expandRequest normalizeRound
      normalizationDirectionWord
  congr 1
  rw [drop_first_last_eq_trimThreeDirections]

/-- Total physical token function for one round. -/
def roundTokenOutput (round : Round) (tokens : List Token) : List Token :=
  Wrapper.output round
    (DropLast.output (DropFirst.output (expandDirectionTokens tokens)))

theorem roundTokenOutput_request (round : Round) (input : Request) :
    roundTokenOutput round input.tokens =
      (normalizeRound round input).tokens := by
  unfold roundTokenOutput
  rw [expandDirectionTokens_request]
  rw [DropFirst.output_request]
  rw [DropLast.output_request]
  rw [Wrapper.output_request]
  change (physicalRoundRequest round input).tokens =
    (normalizeRound round input).tokens
  rw [physicalRoundRequest_eq_normalizeRound]

/-- One round on an arbitrary retained token stream is polynomial-time. -/
noncomputable def roundTokenOutputComputableInPolyTime (round : Round) :
    TM2ComputableInPolyTime id id (roundTokenOutput round) := by
  let expanded := expandDirectionTokensComputableInPolyTime
  let droppedFirst := TM2CompositionMachine.computableInPolyTime expanded
    DropFirst.outputComputableInPolyTime
  let droppedLast := TM2CompositionMachine.computableInPolyTime droppedFirst
    DropLast.outputComputableInPolyTime
  let wrapped := TM2CompositionMachine.computableInPolyTime droppedLast
    (Wrapper.outputComputableInPolyTime round)
  change TM2ComputableInPolyTime id id
    (fun tokens => Wrapper.output round
      (DropLast.output (DropFirst.output
        (expandDirectionTokens tokens))))
  exact wrapped

/-- On canonical request encodings, the physical round computes the exact
dynamically selected semantic round. -/
noncomputable def normalizeRoundTokensComputableInPolyTime (round : Round) :
    TM2ComputableInPolyTime Request.tokens id
      (fun input => (normalizeRound round input).tokens) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    Request.tokens (roundTokenOutputComputableInPolyTime round)
    (fun _ => rfl) (roundTokenOutput_request round)

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
