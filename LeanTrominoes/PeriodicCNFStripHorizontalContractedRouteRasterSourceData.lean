/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalContractedRoutedRequestCompiler
import LeanTrominoes.PeriodicThreeDMContractedRouteRasterSourceData

/-! # Framed compact horizontal contracted raster sources -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalContractedRouteRasterSource

open PeriodicThreeDM

abbrev RasterToken := ContractedRouteRasterSource.RasterToken
abbrev RequestToken := HorizontalContractedRoutedRequest.Token

/-- A framed payload contributes either one already compiled raster-prefix
token or one compact role-request token. -/
inductive Payload
  | prefix (token : RasterToken)
  | request (token : RequestToken)
  deriving DecidableEq, Fintype, Inhabited

/-- A distinct outer boundary resets the complete compact contracted request
pipeline between raster requests. -/
inductive Token
  | payload (value : Payload)
  | sourceEnd
  deriving DecidableEq, Fintype, Inhabited

def isEnd : Token → Bool
  | .sourceEnd => true
  | _ => false

def prefixBlock : Token → List RasterToken
  | .payload (.prefix token) => [token]
  | _ => []

def requestBlock : Token → List RequestToken
  | .payload (.request token) => [token]
  | _ => []

def prefixTokens (tokens : List Token) : List RasterToken :=
  tokens.flatMap prefixBlock

def requestTokens (tokens : List Token) : List RequestToken :=
  tokens.flatMap requestBlock

/-- Mathematical output of the fixed compact one-request pipeline. -/
def requestOutput (tokens : List Token) : List RasterToken :=
  prefixTokens tokens ++
    ContractedRouteRasterSource.rasterizeDirections
      (HorizontalContractedRoutedRequest.contractedOutput
        (requestTokens tokens))

/-- One framed source entry stores an already-materialized finite raster
prefix and compact role-request stream. -/
structure Entry where
  leading : List RasterToken
  requests : List RequestToken

def Entry.payloads (entry : Entry) : List Payload :=
  entry.leading.map .prefix ++
    entry.requests.map .request

def Entry.tokens (entry : Entry) : List Token :=
  entry.payloads.map .payload ++ [.sourceEnd]

def Entry.output (entry : Entry) : List RasterToken :=
  entry.leading ++
    ContractedRouteRasterSource.rasterizeDirections
      (HorizontalContractedRoutedRequest.contractedOutput entry.requests)

def tokens (entries : List Entry) : List Token :=
  entries.flatMap Entry.tokens

def outputTokens (entries : List Entry) : List RasterToken :=
  entries.flatMap Entry.output

@[simp] theorem prefixTokens_entry_tokens (entry : Entry) :
    prefixTokens entry.tokens = entry.leading := by
  simp [prefixTokens, Entry.tokens, Entry.payloads, prefixBlock,
    List.flatMap_map]

@[simp] theorem requestTokens_entry_tokens (entry : Entry) :
    requestTokens entry.tokens = entry.requests := by
  simp [requestTokens, Entry.tokens, Entry.payloads, requestBlock,
    List.flatMap_map]

@[simp] theorem requestOutput_entry_tokens (entry : Entry) :
    requestOutput entry.tokens = entry.output := by
  unfold requestOutput Entry.output
  rw [prefixTokens_entry_tokens, requestTokens_entry_tokens]

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

/-- The outer block map preserves entry order and emits each retained prefix
followed by the exact assembled contracted direction word. -/
@[simp] theorem mappedOutput_tokens (entries : List Entry) :
    TM2EndDelimitedBlockMap.mappedOutput isEnd requestOutput
        (tokens entries) =
      outputTokens entries := by
  unfold TM2EndDelimitedBlockMap.mappedOutput outputTokens
  rw [blocks_tokens, List.flatMap_map]
  apply List.flatMap_congr
  intro entry _
  exact requestOutput_entry_tokens entry

end HorizontalContractedRouteRasterSource
end PeriodicCNFStripReduction
end LeanTrominoes
