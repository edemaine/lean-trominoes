/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerCompiler

/-! # Independently assembling contracted incidence words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedDirectionAssembler

open Computability Turing
open NormalizationDirectionRequest.Batch

/-- Apply the fixed role-tagged assembler to every complete incidence word. -/
def output (tokens : List Token) : List NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd blockOutput tokens

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    blockOutputComputableInPolyTime isEnd

private theorem blocksAux_directionSuffix
    (reversePrefix : List Token)
    (word : List AxisDirection) (input : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reversePrefix
        (word.map Token.direction ++ .incidenceEnd :: input) =
      (reversePrefix.reverse ++
          word.map Token.direction ++ [.incidenceEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] input := by
  induction word generalizing reversePrefix with
  | nil =>
      simp [TM2EndDelimitedBlockMap.blocksAux, isEnd]
  | cons direction word induction =>
      simp only [List.map_cons, List.cons_append]
      rw [TM2EndDelimitedBlockMap.blocksAux]
      simp only [isEnd, Bool.false_eq_true, ↓reduceIte]
      have rest := induction (.direction direction :: reversePrefix)
      rw [rest]
      simp [List.reverse_cons, List.append_assoc]

private theorem blocksAux_roleBlock
    (reversePrefix : List Token) (role : Role)
    (word : List AxisDirection) (input : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reversePrefix
        (roleBlock role word ++ input) =
      (reversePrefix.reverse ++ roleBlock role word) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] input := by
  unfold roleBlock
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [TM2EndDelimitedBlockMap.blocksAux]
  simp only [isEnd, Bool.false_eq_true, ↓reduceIte]
  have rest := blocksAux_directionSuffix
    (.role role :: reversePrefix) word input
  rw [rest]
  simp [List.reverse_cons, List.append_assoc]

@[simp] theorem blocks_roleBlock_append
    (role : Role) (word : List AxisDirection) (input : List Token) :
    TM2EndDelimitedBlockMap.blocks isEnd
        (roleBlock role word ++ input) =
      roleBlock role word ::
        TM2EndDelimitedBlockMap.blocks isEnd input := by
  unfold TM2EndDelimitedBlockMap.blocks
  simpa using blocksAux_roleBlock [] role word input

/-- The one or two independently delimited incidence words of an edge. -/
def EdgeBlock.roleBlocks : EdgeBlock → List (List Token)
  | .retained route => [roleBlock .retained route]
  | .through first second =>
      [roleBlock .throughFirst first,
        roleBlock .throughSecond second]

@[simp] theorem blocks_inputTokens (edgeBlocks : List EdgeBlock) :
    TM2EndDelimitedBlockMap.blocks isEnd (inputTokens edgeBlocks) =
      edgeBlocks.flatMap EdgeBlock.roleBlocks := by
  induction edgeBlocks with
  | nil => rfl
  | cons edge edgeBlocks induction =>
      rw [show inputTokens (edge :: edgeBlocks) =
        EdgeBlock.inputTokens edge ++ inputTokens edgeBlocks by rfl]
      cases edge with
      | retained route =>
          rw [show EdgeBlock.inputTokens (.retained route) =
            roleBlock .retained route by rfl]
          rw [blocks_roleBlock_append, induction]
          rfl
      | through first second =>
          rw [show EdgeBlock.inputTokens (.through first second) =
            roleBlock .throughFirst first ++
              roleBlock .throughSecond second by rfl]
          rw [List.append_assoc, blocks_roleBlock_append,
            blocks_roleBlock_append, induction]
          rfl

@[simp] theorem EdgeBlock.flatMap_blockOutput_roleBlocks
    (edgeBlock : EdgeBlock) :
    edgeBlock.roleBlocks.flatMap blockOutput =
      DelimitedReversal.routeBlock edgeBlock.directions := by
  cases edgeBlock with
  | retained route => simp [EdgeBlock.roleBlocks, EdgeBlock.directions]
  | through first second =>
      simp [EdgeBlock.roleBlocks, EdgeBlock.directions,
        DelimitedReversal.routeBlock, List.map_append,
        List.append_assoc]

/-- Canonical retained and through edge blocks assemble to exactly their
contracted route words, with one final route delimiter per edge. -/
@[simp] theorem output_inputTokens (edgeBlocks : List EdgeBlock) :
    output (inputTokens edgeBlocks) = outputTokens edgeBlocks := by
  unfold output TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_inputTokens]
  induction edgeBlocks with
  | nil => rfl
  | cons edgeBlock edgeBlocks induction =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [EdgeBlock.flatMap_blockOutput_roleBlocks, induction]
      rfl

end ContractedDirectionAssembler
end PeriodicThreeDM
end LeanTrominoes

end
