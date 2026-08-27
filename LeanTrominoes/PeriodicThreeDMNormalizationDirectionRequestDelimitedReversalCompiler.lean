/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionReversalCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Reversing delimiter-separated route direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Batch

open Computability Turing

local instance delimitedReversalAxisDirectionInhabited :
    Inhabited AxisDirection :=
  ⟨.invalid⟩

/-- Discard a route delimiter while retaining its direction payload. -/
def DelimitedReversal.directionBlock : NormalizedToken → List AxisDirection
  | .direction direction => [direction]
  | .routeEnd => []

def DelimitedReversal.directions (tokens : List NormalizedToken) :
    List AxisDirection :=
  tokens.flatMap DelimitedReversal.directionBlock

noncomputable def DelimitedReversal.directionsComputableInPolyTime :
    TM2ComputableInPolyTime id id DelimitedReversal.directions :=
  FiniteBlockTransducer.computableInPolyTime
    DelimitedReversal.directionBlock

/-- Reverse one collected route word and restore exactly one delimiter. -/
def DelimitedReversal.blockOutput
    (tokens : List NormalizedToken) : List NormalizedToken :=
  Finalizer.output
    (Gadget.reverseDirections (DelimitedReversal.directions tokens))

noncomputable def DelimitedReversal.blockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id DelimitedReversal.blockOutput := by
  let extracted := DelimitedReversal.directionsComputableInPolyTime
  let reversed := TM2CompositionMachine.computableInPolyTime extracted
    Gadget.reverseDirectionsComputableInPolyTime
  let finalized := TM2CompositionMachine.computableInPolyTime reversed
    Finalizer.computableInPolyTime
  exact finalized

def DelimitedReversal.isRouteEnd : NormalizedToken → Bool
  | .direction _ => false
  | .routeEnd => true

/-- Reverse every complete delimiter-terminated route independently. -/
def DelimitedReversal.output (tokens : List NormalizedToken) :
    List NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput
    DelimitedReversal.isRouteEnd DelimitedReversal.blockOutput tokens

noncomputable def DelimitedReversal.outputComputableInPolyTime :
    TM2ComputableInPolyTime id id DelimitedReversal.output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    DelimitedReversal.blockOutputComputableInPolyTime
    DelimitedReversal.isRouteEnd

def DelimitedReversal.routeBlock
    (directions : List AxisDirection) : List NormalizedToken :=
  directions.map .direction ++ [.routeEnd]

@[simp] theorem DelimitedReversal.directions_routeBlock
    (directions : List AxisDirection) :
    DelimitedReversal.directions
        (DelimitedReversal.routeBlock directions) =
      directions := by
  simp [DelimitedReversal.directions,
    DelimitedReversal.directionBlock,
    DelimitedReversal.routeBlock, List.flatMap_map]

@[simp] theorem DelimitedReversal.blockOutput_routeBlock
    (directions : List AxisDirection) :
    DelimitedReversal.blockOutput
        (DelimitedReversal.routeBlock directions) =
      DelimitedReversal.routeBlock
        (Gadget.reverseDirections directions) := by
  unfold DelimitedReversal.blockOutput
  rw [DelimitedReversal.directions_routeBlock, Finalizer.output_eq]
  rfl

private theorem DelimitedReversal.blocksAux_routeBlock
    (reversePrefix : List NormalizedToken)
    (directions : List AxisDirection) (input : List NormalizedToken) :
    TM2EndDelimitedBlockMap.blocksAux DelimitedReversal.isRouteEnd
        reversePrefix
        (DelimitedReversal.routeBlock directions ++ input) =
      (reversePrefix.reverse ++
          DelimitedReversal.routeBlock directions) ::
        TM2EndDelimitedBlockMap.blocksAux
          DelimitedReversal.isRouteEnd [] input := by
  induction directions generalizing reversePrefix with
  | nil =>
      simp [DelimitedReversal.routeBlock,
        TM2EndDelimitedBlockMap.blocksAux,
        DelimitedReversal.isRouteEnd]
  | cons direction directions induction =>
      simp only [DelimitedReversal.routeBlock, List.map_cons,
        List.cons_append]
      rw [TM2EndDelimitedBlockMap.blocksAux]
      simp only [DelimitedReversal.isRouteEnd, Bool.false_eq_true,
        ↓reduceIte]
      have rest := induction
        (NormalizedToken.direction direction :: reversePrefix)
      unfold DelimitedReversal.routeBlock at rest
      rw [rest]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem DelimitedReversal.blocks_routeBlock_append
    (directions : List AxisDirection) (input : List NormalizedToken) :
    TM2EndDelimitedBlockMap.blocks DelimitedReversal.isRouteEnd
        (DelimitedReversal.routeBlock directions ++ input) =
      DelimitedReversal.routeBlock directions ::
        TM2EndDelimitedBlockMap.blocks
          DelimitedReversal.isRouteEnd input := by
  unfold TM2EndDelimitedBlockMap.blocks
  simpa using DelimitedReversal.blocksAux_routeBlock
    [] directions input

@[simp] theorem DelimitedReversal.blocks_routeBlocks
    (blocks : List (List AxisDirection)) :
    TM2EndDelimitedBlockMap.blocks DelimitedReversal.isRouteEnd
        (blocks.flatMap DelimitedReversal.routeBlock) =
      blocks.map DelimitedReversal.routeBlock := by
  induction blocks with
  | nil => rfl
  | cons directions blocks induction =>
      rw [List.flatMap_cons,
        DelimitedReversal.blocks_routeBlock_append, induction,
        List.map_cons]

/-- Mapping the reversal compiler over a canonical delimited stream reverses
each route independently and preserves every route boundary. -/
@[simp] theorem DelimitedReversal.output_routeBlocks
    (blocks : List (List AxisDirection)) :
    DelimitedReversal.output
        (blocks.flatMap DelimitedReversal.routeBlock) =
      blocks.flatMap fun directions =>
        DelimitedReversal.routeBlock
          (Gadget.reverseDirections directions) := by
  unfold DelimitedReversal.output TM2EndDelimitedBlockMap.mappedOutput
  rw [DelimitedReversal.blocks_routeBlocks, List.flatMap_map]
  apply List.flatMap_congr
  intro directions _
  exact DelimitedReversal.blockOutput_routeBlock directions

end Batch
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
