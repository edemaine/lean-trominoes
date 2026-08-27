/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionRequestCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Batches of compact horizontal typed incidence requests -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceDirectionRequest
namespace Batch

abbrev InnerToken := HorizontalOccurrenceDirectionRequest.Token

inductive Token
  | request (token : InnerToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited

def isEnd : Token → Bool
  | .requestEnd => true
  | _ => false

def requestBlock (request : List InnerToken) : List Token :=
  request.map .request ++ [.requestEnd]

def tokens (requests : List (List InnerToken)) : List Token :=
  requests.flatMap requestBlock

theorem requestBlock_continues (request : List InnerToken) :
    ∀ token ∈ request.map Token.request, isEnd token = false := by
  intro token member
  obtain ⟨inner, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem blocksAux_append_requestEnd
    (reverseBlock body rest : List Token)
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
    (reverseBlock : List Token) (request : List InnerToken)
    (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (requestBlock request ++ rest) =
      (reverseBlock.reverse ++ requestBlock request) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  unfold requestBlock
  rw [List.append_assoc]
  simpa [List.append_assoc] using
    blocksAux_append_requestEnd reverseBlock
      (request.map Token.request) rest
      (requestBlock_continues request)

@[simp] theorem blocks_tokens (requests : List (List InnerToken)) :
    TM2EndDelimitedBlockMap.blocks isEnd (tokens requests) =
      requests.map requestBlock := by
  unfold TM2EndDelimitedBlockMap.blocks tokens
  induction requests with
  | nil => rfl
  | cons request requests induction =>
      rw [List.flatMap_cons, blocksAux_requestBlock_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]

theorem mappedOutput_tokens {Target : Type}
    (function : List Token → List Target)
    (requests : List (List InnerToken)) :
    TM2EndDelimitedBlockMap.mappedOutput isEnd function
        (tokens requests) =
      requests.flatMap fun request => function (requestBlock request) := by
  unfold TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_tokens, List.flatMap_map]

def untagBlock : Token → List InnerToken
  | .request token => [token]
  | .requestEnd => []

def innerOutput (block : List Token) : List NormalizedToken :=
  HorizontalTypedIncidenceDirectionRequest.output
    (block.flatMap untagBlock)

@[simp] theorem innerOutput_requestBlock (request : List InnerToken) :
    innerOutput (requestBlock request) =
      HorizontalTypedIncidenceDirectionRequest.output request := by
  unfold innerOutput requestBlock
  simp [untagBlock, List.flatMap_map]

def output (input : List Token) : List NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput input

@[simp] theorem output_tokens (requests : List (List InnerToken)) :
    output (tokens requests) =
      requests.flatMap HorizontalTypedIncidenceDirectionRequest.output := by
  unfold output
  rw [mappedOutput_tokens]
  apply List.flatMap_congr
  intro request _
  exact innerOutput_requestBlock request

/-- Canonical batch input of a classified typed-incidence block list. -/
noncomputable def blockRequests
    (blocks : List HorizontalTypedIncidenceDirectionBlock) :
    List (List InnerToken) :=
  blocks.map HorizontalTypedIncidenceDirectionBlock.requestTokens

noncomputable def blockTokens
    (blocks : List HorizontalTypedIncidenceDirectionBlock) :
    List Token :=
  tokens (blockRequests blocks)

@[simp] theorem output_blockTokens
    (blocks : List HorizontalTypedIncidenceDirectionBlock) :
    output (blockTokens blocks) =
      blocks.flatMap fun block =>
        block.directions.map .direction ++ [.routeEnd] := by
  unfold blockTokens blockRequests
  rw [output_tokens, List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  exact HorizontalTypedIncidenceDirectionRequest.output_requestTokens block

end Batch
end HorizontalTypedIncidenceDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes
