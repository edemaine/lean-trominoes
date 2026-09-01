/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Batched compact routed horizontal occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace HorizontalOccurrenceRoutedRequest
namespace Batch

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

abbrev Token :=
  FiniteAlphabetDelimitedBlockJoin.Token
    HorizontalOccurrenceRoutedRequest.Token

def isEnd : Token → Bool
  | .blockEnd => true
  | .value _ => false

def untagBlock : Token → List HorizontalOccurrenceRoutedRequest.Token
  | .value token => [token]
  | .blockEnd => []

def untagged (block : List Token) :
    List HorizontalOccurrenceRoutedRequest.Token :=
  block.flatMap untagBlock

def innerOutput (block : List Token) : List AxisDirection :=
  HorizontalOccurrenceRoutedRequest.output (untagged block)

def output (input : List Token) : List AxisDirection :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput input

@[simp] theorem untagged_block
    (body : List HorizontalOccurrenceRoutedRequest.Token) :
    untagged (FiniteAlphabetDelimitedBlockJoin.block body) = body := by
  unfold untagged FiniteAlphabetDelimitedBlockJoin.block
  rw [List.flatMap_append, List.flatMap_map]
  simp only [untagBlock, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [← List.map_eq_flatMap]
  exact List.map_id body

theorem body_continues
    (body : List HorizontalOccurrenceRoutedRequest.Token) :
    ∀ token ∈ body.map
        (FiniteAlphabetDelimitedBlockJoin.Token.value :
          HorizontalOccurrenceRoutedRequest.Token → Token),
      isEnd token = false := by
  intro token member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem blocksAux_append_blockEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (body ++ .blockEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.blockEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux, isEnd]
  | cons token body induction =>
      have tokenContinues := continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

theorem blocksAux_block_append
    (reverseBlock : List Token)
    (body : List HorizontalOccurrenceRoutedRequest.Token)
    (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (FiniteAlphabetDelimitedBlockJoin.block body ++ rest) =
      (reverseBlock.reverse ++
          FiniteAlphabetDelimitedBlockJoin.block body) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  unfold FiniteAlphabetDelimitedBlockJoin.block
  rw [List.append_assoc]
  simpa [List.append_assoc] using
    blocksAux_append_blockEnd reverseBlock
      (body.map
        (FiniteAlphabetDelimitedBlockJoin.Token.value :
          HorizontalOccurrenceRoutedRequest.Token → Token))
      rest (body_continues body)

@[simp] theorem blocks_blocks
    (bodies : List (List HorizontalOccurrenceRoutedRequest.Token)) :
    TM2EndDelimitedBlockMap.blocks isEnd
        (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      bodies.map FiniteAlphabetDelimitedBlockJoin.block := by
  unfold TM2EndDelimitedBlockMap.blocks
    FiniteAlphabetDelimitedBlockJoin.blocks
  induction bodies with
  | nil => rfl
  | cons body bodies induction =>
      rw [List.flatMap_cons, blocksAux_block_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]

@[simp] theorem innerOutput_block
    (body : List HorizontalOccurrenceRoutedRequest.Token) :
    innerOutput (FiniteAlphabetDelimitedBlockJoin.block body) =
      HorizontalOccurrenceRoutedRequest.output body := by
  simp [innerOutput]

/-- Batched execution is exactly the concatenation of independent occurrence
compiler outputs. -/
@[simp] theorem output_blocks
    (bodies : List (List HorizontalOccurrenceRoutedRequest.Token)) :
    output (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      bodies.flatMap HorizontalOccurrenceRoutedRequest.output := by
  unfold output TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro body _
  exact innerOutput_block body

noncomputable def untaggedComputableInPolyTime :
    TM2ComputableInPolyTime id id untagged :=
  FiniteBlockTransducer.computableInPolyTime untagBlock

noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  let complete := TM2CompositionMachine.computableInPolyTime
    untaggedComputableInPolyTime
    HorizontalOccurrenceRoutedRequest.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun _ => rfl)

/-- Run the verified compact occurrence compiler independently on every
end-delimited aligned request. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime isEnd

end Batch
end HorizontalOccurrenceRoutedRequest
end LeanTrominoes.PeriodicCNFStripReduction

end
