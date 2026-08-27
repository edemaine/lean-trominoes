/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestTokenData
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerBatchCompiler
import LeanTrominoes.SeparatedProductEncoding

/-! # Framed source words for contracted raster requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedRouteRasterSource

open NormalizationDirectionRequest.Batch

abbrev RasterToken := GadgetSparseRouteRasterRequestTokens.Token
abbrev IncidenceToken := ContractedDirectionAssembler.Token

/-- A request payload either passes through one already compiled prefix token
or contributes one role-tagged incidence token. -/
inductive Payload
  | prefix (token : RasterToken)
  | incidence (token : IncidenceToken)
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- A distinct outer delimiter lets the generic block-map machine process one
contracted edge at a time. -/
inductive Token
  | payload (value : Payload)
  | sourceEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

def isEnd : Token → Bool
  | .sourceEnd => true
  | _ => false

def prefixBlock : Token → List RasterToken
  | .payload (.prefix token) => [token]
  | _ => []

def incidenceBlock : Token → List IncidenceToken
  | .payload (.incidence token) => [token]
  | _ => []

def prefixTokens (tokens : List Token) : List RasterToken :=
  tokens.flatMap prefixBlock

def incidenceTokens (tokens : List Token) : List IncidenceToken :=
  tokens.flatMap incidenceBlock

/-- Interpret the separated output of prefix extraction and contracted-word
assembly as one physical raster-request block. -/
def separatedBlock :
    SeparatedProductEncoding.Token RasterToken NormalizedToken →
      List RasterToken
  | .left token => [token]
  | .separator => []
  | .right (.direction direction) =>
      [.normalization (.direction direction)]
  | .right .routeEnd => [.requestEnd]

def separatedFlatten
    (tokens : List
      (SeparatedProductEncoding.Token RasterToken NormalizedToken)) :
    List RasterToken :=
  tokens.flatMap separatedBlock

def rasterizeDirections (tokens : List NormalizedToken) :
    List RasterToken :=
  tokens.flatMap fun token => separatedBlock (.right token)

@[simp] theorem rasterizeDirections_routeBlock
    (directions : List AxisDirection) :
    rasterizeDirections
        (NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
          directions) =
      directions.map (fun direction =>
        GadgetSparseRouteRasterRequestTokens.Token.normalization
          (.direction direction)) ++ [.requestEnd] := by
  simp [rasterizeDirections, separatedBlock,
    NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock,
    List.flatMap_map]
  induction directions <;> simp_all

@[simp] theorem separatedFlatten_encode
    (leading : List RasterToken) (directions : List NormalizedToken) :
    separatedFlatten
        (SeparatedProductEncoding.encode id id (leading, directions)) =
      leading ++ rasterizeDirections directions := by
  simp [separatedFlatten, separatedBlock, rasterizeDirections,
    SeparatedProductEncoding.encode, List.flatMap_map]

/-- Mathematical result of the fixed one-request pipeline. -/
def requestOutput (tokens : List Token) : List RasterToken :=
  prefixTokens tokens ++
    rasterizeDirections
      (ContractedDirectionAssembler.output (incidenceTokens tokens))

/-- Source-facing decomposition of one contracted edge request. -/
structure Entry where
  leading : List RasterToken
  edge : ContractedDirectionAssembler.EdgeBlock
  deriving DecidableEq

def Entry.payloads (entry : Entry) : List Payload :=
  entry.leading.map .prefix ++
    entry.edge.inputTokens.map .incidence

def Entry.tokens (entry : Entry) : List Token :=
  entry.payloads.map .payload ++ [.sourceEnd]

def tokens (entries : List Entry) : List Token :=
  entries.flatMap Entry.tokens

def Entry.output (entry : Entry) : List RasterToken :=
  entry.leading ++ rasterizeDirections
    (ContractedDirectionAssembler.outputTokens [entry.edge])

def outputTokens (entries : List Entry) : List RasterToken :=
  entries.flatMap Entry.output

@[simp] theorem prefixTokens_entry_tokens (entry : Entry) :
    prefixTokens entry.tokens = entry.leading := by
  simp [prefixTokens, Entry.tokens, Entry.payloads, prefixBlock,
    List.flatMap_map]

@[simp] theorem incidenceTokens_entry_tokens (entry : Entry) :
    incidenceTokens entry.tokens = entry.edge.inputTokens := by
  simp [incidenceTokens, Entry.tokens, Entry.payloads, incidenceBlock,
    List.flatMap_map]

@[simp] theorem requestOutput_entry_tokens (entry : Entry) :
    requestOutput entry.tokens = entry.output := by
  rw [requestOutput, prefixTokens_entry_tokens,
    incidenceTokens_entry_tokens]
  unfold Entry.output
  have inputEq : ContractedDirectionAssembler.inputTokens [entry.edge] =
      entry.edge.inputTokens := by
    simp [ContractedDirectionAssembler.inputTokens]
  rw [← inputEq]
  rw [ContractedDirectionAssembler.output_inputTokens]

private theorem blocksAux_payloads
    (reversePrefix : List Token) (payloads : List Payload)
    (input : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reversePrefix
        (payloads.map Token.payload ++ .sourceEnd :: input) =
      (reversePrefix.reverse ++
          payloads.map Token.payload ++ [.sourceEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] input := by
  induction payloads generalizing reversePrefix with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux, isEnd]
  | cons payload payloads induction =>
      simp only [List.map_cons, List.cons_append]
      rw [TM2EndDelimitedBlockMap.blocksAux]
      simp only [isEnd, Bool.false_eq_true, ↓reduceIte]
      have rest := induction (.payload payload :: reversePrefix)
      rw [rest]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem blocks_entry_append (entry : Entry)
    (input : List Token) :
    TM2EndDelimitedBlockMap.blocks isEnd
        (entry.tokens ++ input) =
      entry.tokens :: TM2EndDelimitedBlockMap.blocks isEnd input := by
  unfold TM2EndDelimitedBlockMap.blocks Entry.tokens
  simp only [List.append_assoc, List.singleton_append]
  simpa using blocksAux_payloads [] entry.payloads input

@[simp] theorem blocks_tokens (entries : List Entry) :
    TM2EndDelimitedBlockMap.blocks isEnd (tokens entries) =
      entries.map Entry.tokens := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      rw [show tokens (entry :: entries) =
        entry.tokens ++ tokens entries by rfl]
      rw [blocks_entry_append, induction, List.map_cons]

/-- The outer block map preserves request order and returns each canonical
entry's prefix followed by its assembled contracted direction block. -/
@[simp] theorem mappedOutput_tokens (entries : List Entry) :
    TM2EndDelimitedBlockMap.mappedOutput isEnd requestOutput
        (tokens entries) =
      outputTokens entries := by
  unfold TM2EndDelimitedBlockMap.mappedOutput outputTokens
  rw [blocks_tokens, List.flatMap_map]
  apply List.flatMap_congr
  intro entry _
  exact requestOutput_entry_tokens entry

end ContractedRouteRasterSource
end PeriodicThreeDM
end LeanTrominoes
