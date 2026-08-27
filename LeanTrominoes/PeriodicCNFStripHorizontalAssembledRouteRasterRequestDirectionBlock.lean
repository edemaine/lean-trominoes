/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestTokenData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteAssembledRasterRequestData
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledContractedDirectionBlock

/-! # Compact token blocks for assembled route-raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Token-level interpretation of one assembled raster request after replacing
its contracted direction list by a compact retained/through block. -/
def horizontalAssembledRouteRasterRequestDirectionBlockTokens
    (metadata : RouteRasterRequest.Metadata)
    (header : Header)
    (block : HorizontalAssembledContractedDirectionBlock) :
    List GadgetSparseRouteRasterRequestTokens.Token :=
  GadgetSparseRouteRasterRequestTokens.metadataTokens metadata ++
    (header.tokens ++
      (PeriodicThreeDM.NormalizationDirectionRequest.Token.separator ::
        block.directions.map
          PeriodicThreeDM.NormalizationDirectionRequest.Token.direction)).map
        GadgetSparseRouteRasterRequestTokens.Token.normalization ++
    [.requestEnd]

/-- Every genuine assembled normalization request has exactly the compact
token form selected by its contracted direction block. -/
theorem horizontalAssembledNormalizationRequest_directionBlock_tokens
    (source : PeriodicCNF Nat)
    (edge : ContractedEdge)
    (edgeMember : edge ∈
      (horizontalThreeDMProblemComputed source).contractedEdges)
    (metadata : RouteRasterRequest.Metadata) :
    ∃ block : HorizontalAssembledContractedDirectionBlock,
      GadgetSparseRouteRasterRequestTokens.requestBlock
          ({ metadata := metadata
             normalization :=
               horizontalAssembledNormalizationRequest source edge } :
            RouteRasterRequest.Request) =
        horizontalAssembledRouteRasterRequestDirectionBlockTokens
          metadata (horizontalAssembledRouteRequestHeader source edge)
          block := by
  rcases horizontalAssembledContractedDirections_directionBlock_of_mem
      source edge edgeMember with
    ⟨block, directions⟩
  refine ⟨block, ?_⟩
  unfold GadgetSparseRouteRasterRequestTokens.requestBlock
    GadgetSparseRouteRasterRequestTokens.requestTokens
    horizontalAssembledRouteRasterRequestDirectionBlockTokens
    horizontalAssembledNormalizationRequest
    NormalizationDirectionRequest.Request.tokens
  rw [directions]

end PeriodicCNFStripReduction
end LeanTrominoes

end
