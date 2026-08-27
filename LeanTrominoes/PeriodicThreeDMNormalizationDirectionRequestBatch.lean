/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # End-delimited batches of route-normalization requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Batch

/-- Outer alphabet separating independently normalized edge requests. -/
inductive Token
  | request (token : NormalizationDirectionRequest.Token)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

def isEnd : Token → Bool
  | .requestEnd => true
  | _ => false

def requestBlock (request : Request) : List Token :=
  request.tokens.map .request ++ [.requestEnd]

def tokens (requests : List Request) : List Token :=
  requests.flatMap requestBlock

theorem requestBlock_continues (request : Request) :
    ∀ token ∈ request.tokens.map Token.request, isEnd token = false := by
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
    (reverseBlock : List Token) (request : Request) (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (requestBlock request ++ rest) =
      (reverseBlock.reverse ++ requestBlock request) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  unfold requestBlock
  rw [List.append_assoc]
  simpa [List.append_assoc] using
    blocksAux_append_requestEnd reverseBlock
      (request.tokens.map Token.request) rest
      (requestBlock_continues request)

@[simp]
theorem blocks_tokens (requests : List Request) :
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
    (function : List Token → List Target) (requests : List Request) :
    TM2EndDelimitedBlockMap.mappedOutput isEnd function
        (tokens requests) =
      requests.flatMap fun request => function (requestBlock request) := by
  unfold TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_tokens, List.flatMap_map]

end Batch
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
