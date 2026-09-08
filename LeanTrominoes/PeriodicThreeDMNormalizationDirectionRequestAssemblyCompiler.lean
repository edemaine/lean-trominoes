/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestDelimitedReversalCompiler

/-! # Joining independently compiled route headers and direction words -/

noncomputable section

namespace LeanTrominoes.PeriodicThreeDM.NormalizationDirectionRequest.Batch.RequestAssembly

open Computability Turing

abbrev PackedToken := FiniteAlphabetDelimitedBlockJoin.Token NormalizationDirectionRequest.Token

def headerBlock (header : Header) : List PackedToken :=
  FiniteAlphabetDelimitedBlockJoin.block (header.tokens ++ [.separator])

def headerTokens (headers : List Header) : List PackedToken := headers.flatMap headerBlock

def directionBlock : NormalizedToken → List PackedToken
  | .direction direction => [.value (.direction direction)]
  | .routeEnd => [.blockEnd]

def directionTokens (tokens : List NormalizedToken) : List PackedToken := tokens.flatMap directionBlock

def batchBlock : PackedToken → List Batch.Token
  | .value token => [.request token]
  | .blockEnd => [.requestEnd]

def batchTokens (tokens : List PackedToken) : List Batch.Token := tokens.flatMap batchBlock

def output (headers : List Header) (directions : List NormalizedToken) : List Batch.Token :=
  batchTokens (FiniteAlphabetDelimitedBlockJoin.joined (headerTokens headers) (directionTokens directions))

private theorem headerTokens_requests (requests : List Request) :
    headerTokens (requests.map Request.header) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (requests.map (fun request => request.header.tokens ++ [.separator])) := by
  simp only [headerTokens, FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map]
  rfl

private theorem directionTokens_routeBlock (directions : List AxisDirection) :
    directionTokens (DelimitedReversal.routeBlock directions) =
      FiniteAlphabetDelimitedBlockJoin.block (directions.map NormalizationDirectionRequest.Token.direction) := by
  simp only [directionTokens, DelimitedReversal.routeBlock, List.flatMap_append,
    List.flatMap_map, directionBlock, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, FiniteAlphabetDelimitedBlockJoin.block, List.map_map, Function.comp_def]
  rw [← List.map_eq_flatMap]

private theorem directionTokens_requests (requests : List Request) :
    directionTokens (requests.flatMap (fun request => DelimitedReversal.routeBlock request.directions)) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (requests.map (fun request => request.directions.map NormalizationDirectionRequest.Token.direction)) := by
  unfold directionTokens
  rw [List.flatMap_assoc]
  change requests.flatMap (fun request => directionTokens (DelimitedReversal.routeBlock request.directions)) = _
  simp only [directionTokens_routeBlock, FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map]

private theorem batchTokens_block (body : List NormalizationDirectionRequest.Token) :
    batchTokens (FiniteAlphabetDelimitedBlockJoin.block body) =
      body.map Batch.Token.request ++ [.requestEnd] := by
  simp only [batchTokens, FiniteAlphabetDelimitedBlockJoin.block, List.flatMap_append,
    List.flatMap_map, batchBlock, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← List.map_eq_flatMap]

/-- Header and direction compilers for the same request list assemble exactly
its canonical end-delimited batch encoding. -/
theorem output_requests (requests : List Request) :
    output (requests.map Request.header)
      (requests.flatMap (fun request => DelimitedReversal.routeBlock request.directions)) =
      Batch.tokens requests := by
  unfold output
  rw [headerTokens_requests, directionTokens_requests]
  have joined := FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
    (requests.map (fun request =>
      (request.header.tokens ++ [.separator],
        request.directions.map NormalizationDirectionRequest.Token.direction)))
  simp only [List.map_map, Function.comp_def] at joined
  rw [joined]
  unfold FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_map]
  unfold batchTokens
  rw [List.flatMap_assoc]
  change requests.flatMap (fun request => batchTokens
    (FiniteAlphabetDelimitedBlockJoin.block
      ((request.header.tokens ++ [.separator]) ++ request.directions.map .direction))) = _
  unfold Batch.tokens Batch.requestBlock Request.tokens
  simp only [batchTokens_block, List.append_assoc, List.singleton_append]

/-- Pointwise finite-alphabet block joining compiles a complete request batch
from independently compiled headers and delimited direction words. -/
noncomputable def computableInPolyTimeOf
    {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (headers : Source → List Header) (directions : Source → List NormalizedToken)
    (headerCompiler : TM2ComputableInPolyTime encodeSource id headers)
    (directionCompiler : TM2ComputableInPolyTime encodeSource id directions) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => output (headers source) (directions source)) := by
  let first := TM2CompositionMachine.computableInPolyTime headerCompiler
    (FiniteBlockTransducer.computableInPolyTime headerBlock)
  let second := TM2CompositionMachine.computableInPolyTime directionCompiler
    (FiniteBlockTransducer.computableInPolyTime directionBlock)
  let joined := FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf encodeSource
    (fun source => headerTokens (headers source))
    (fun source => directionTokens (directions source)) first second
  unfold output
  exact TM2CompositionMachine.computableInPolyTime joined
    (FiniteBlockTransducer.computableInPolyTime batchBlock)

end LeanTrominoes.PeriodicThreeDM.NormalizationDirectionRequest.Batch.RequestAssembly

end
