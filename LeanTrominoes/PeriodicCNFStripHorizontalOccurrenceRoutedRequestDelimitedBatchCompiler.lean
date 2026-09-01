/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestBatchCompiler
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # End-delimited batched routed horizontal occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace HorizontalOccurrenceRoutedRequest
namespace DelimitedBatch

open Computability Turing

abbrev InputToken := Batch.Token
abbrev Token :=
  FiniteAlphabetDelimitedBlockJoin.Token AxisDirection

instance : Inhabited Token := ⟨.blockEnd⟩

def directionToken (direction : AxisDirection) : List Token :=
  [.value direction]

/-- Compile one request block and retain one explicit delimiter after its
complete direction word. -/
def innerOutput (block : List InputToken) : List Token :=
  FiniteAlphabetDelimitedBlockJoin.block (Batch.innerOutput block)

/-- Compile every input block independently while preserving its boundary. -/
def output (input : List InputToken) : List Token :=
  TM2EndDelimitedBlockMap.mappedOutput Batch.isEnd innerOutput input

noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  let tagged := TM2CompositionMachine.computableInPolyTime
    Batch.innerOutputComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime directionToken)
  let appended := TM2CompositionMachine.computableInPolyTime tagged
    (TM2ListAppend.appendFixedComputableInPolyTime [.blockEnd])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    fun block => by
      unfold innerOutput FiniteAlphabetDelimitedBlockJoin.block
        TM2ListAppend.appendFixedWords directionToken
      rw [← List.map_eq_flatMap]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime Batch.isEnd

/-- The delimiter-preserving batch compiler emits one complete output block
for every complete input request block. -/
@[simp] theorem output_blocks
    (bodies : List (List HorizontalOccurrenceRoutedRequest.Token)) :
    output (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (bodies.map HorizontalOccurrenceRoutedRequest.output) := by
  unfold output TM2EndDelimitedBlockMap.mappedOutput
  rw [Batch.blocks_blocks, List.flatMap_map]
  unfold FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro body _
  simp [innerOutput]

end DelimitedBatch
end HorizontalOccurrenceRoutedRequest
end LeanTrominoes.PeriodicCNFStripReduction

end
