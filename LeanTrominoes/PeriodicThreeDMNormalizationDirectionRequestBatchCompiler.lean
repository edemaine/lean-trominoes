/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Polynomial-time batches of independently normalized routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Batch

open Computability Turing

/-- Physical block-map output on an arbitrary outer token stream. -/
def normalizedOutput (input : List Batch.Token) :
    List NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput input

noncomputable def normalizedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedOutput :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime isEnd

/-- Canonical concatenation of normalized direction words, retaining one
route boundary after every request. -/
def normalizedTokens (requests : List Request) : List NormalizedToken :=
  requests.flatMap normalizedBlock

@[simp]
theorem normalizedOutput_tokens (requests : List Request) :
    normalizedOutput (tokens requests) = normalizedTokens requests := by
  unfold normalizedOutput normalizedTokens
  rw [mappedOutput_tokens]
  apply List.flatMap_congr
  intro request _
  exact innerOutput_requestBlock request

end Batch
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

end
