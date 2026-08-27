/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenInnerCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Batched compiler for expanded raster route requests -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseRouteRasterNormalizedTokens
namespace Batch

open Computability Turing
open GadgetSparseRouteRasterRequestTokens
open PeriodicCNFStripReduction.RouteRasterRequest

def isEnd : ExpandedToken → Bool
  | .requestEnd => true
  | _ => false

def requestBody (request : Request) : List ExpandedToken :=
  expandedMetadataTokens request.metadata ++
    request.normalization.tokens.map .normalization

@[simp] theorem expandedRequestBlock_eq_body (request : Request) :
    expandedRequestBlock request = requestBody request ++ [.requestEnd] := by
  rfl

theorem requestBody_continues (request : Request) :
    ∀ token ∈ requestBody request, isEnd token = false := by
  intro token member
  unfold requestBody at member
  simp only [List.mem_append] at member
  rcases member with metadataMember | normalizationMember
  · unfold expandedMetadataTokens at metadataMember
    simp only [List.mem_append, List.mem_replicate,
      List.mem_singleton] at metadataMember
    rcases metadataMember with
      ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [isEnd]
  · obtain ⟨normalizationToken, _, rfl⟩ :=
      List.mem_map.mp normalizationMember
    rfl

theorem blocksAux_append_requestEnd
    (reverseBlock body rest : List ExpandedToken)
    (continues : ∀ token ∈ body, isEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (body ++ .requestEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.requestEnd]) ::
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

theorem blocksAux_requestBlock_append
    (reverseBlock : List ExpandedToken)
    (request : Request) (rest : List ExpandedToken) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (expandedRequestBlock request ++ rest) =
      (reverseBlock.reverse ++ expandedRequestBlock request) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  rw [expandedRequestBlock_eq_body, List.append_assoc]
  simpa [expandedRequestBlock_eq_body, List.append_assoc] using
    blocksAux_append_requestEnd reverseBlock
      (requestBody request) rest (requestBody_continues request)

@[simp] theorem blocks_expandedTokens (requests : List Request) :
    TM2EndDelimitedBlockMap.blocks isEnd (expandedTokens requests) =
      requests.map expandedRequestBlock := by
  unfold TM2EndDelimitedBlockMap.blocks expandedTokens
  induction requests with
  | nil => rfl
  | cons request requests induction =>
      rw [List.flatMap_cons, blocksAux_requestBlock_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]

def normalizedOutput (input : List ExpandedToken) : List Token :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput input

/-- The batch machine is a polynomial-time map of the certified one-request
inner compiler. -/
noncomputable def normalizedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedOutput :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime isEnd

@[simp] theorem normalizedOutput_expandedTokens (requests : List Request) :
    normalizedOutput (expandedTokens requests) =
      normalizedTokens requests := by
  unfold normalizedOutput TM2EndDelimitedBlockMap.mappedOutput
    normalizedTokens
  rw [blocks_expandedTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro request _
  exact innerOutput_expandedRequestBlock request

end Batch
end GadgetSparseRouteRasterNormalizedTokens
end LeanTrominoes

end
