/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests

/-! # Factor-twelve expansion inside normalization requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Gadget

def expansionBlock : Token → List Token
  | .direction direction =>
      List.replicate 12 (.direction direction)
  | token => [token]

def expandDirectionTokens (tokens : List Token) : List Token :=
  tokens.flatMap expansionBlock

def expandRequest (request : Request) : Request :=
  { header := request.header
    directions := repeatTwelveDirections request.directions }

theorem expandDirectionTokens_request (request : Request) :
    expandDirectionTokens request.tokens = (expandRequest request).tokens := by
  unfold expandDirectionTokens Request.tokens Header.tokens expandRequest
    repeatTwelveDirections
  simp [expansionBlock, List.flatMap_map, List.map_flatMap]

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
