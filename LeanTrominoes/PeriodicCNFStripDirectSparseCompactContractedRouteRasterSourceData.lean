/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseContractedRouteRasterSourceData
import LeanTrominoes.PeriodicCNFStripHorizontalContractedRouteRasterSourceData

/-! # Direct compact routed source entries for raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest

/-- One complete direct edge entry with its finite raster prefix retained and
its incidence geometry represented by the compact routed request language. -/
def directSparseCompactContractedRouteEntry
    (source : PeriodicCNF Nat)
    (metadata : RouteRasterRequest.Metadata)
    (edge : ContractedEdge)
    (block : HorizontalAssembledContractedDirectionBlock) :
    HorizontalContractedRouteRasterSource.Entry where
  leading := directSparseContractedRouteLeadingTokens source metadata edge
  requests := HorizontalContractedRoutedRequest.contractedInputTokens [block]

/-- If the compact block denotes the assembled direction word of an edge,
the fixed framed pipeline emits that edge's exact canonical raster request.
This packages metadata, all six header fields, contracted-role assembly, and
the outer request delimiter into one source-emitter correctness lemma. -/
theorem directSparseCompactContractedRouteEntry_output
    (source : PeriodicCNF Nat)
    (metadata : RouteRasterRequest.Metadata)
    (edge : ContractedEdge)
    (block : HorizontalAssembledContractedDirectionBlock)
    (directions : block.directions =
      horizontalAssembledContractedDirections source edge) :
    (directSparseCompactContractedRouteEntry
        source metadata edge block).output =
      GadgetSparseRouteRasterRequestTokens.requestBlock
        ({ metadata := metadata
           normalization := horizontalAssembledNormalizationRequest
             source edge } : RouteRasterRequest.Request) := by
  unfold HorizontalContractedRouteRasterSource.Entry.output
    directSparseCompactContractedRouteEntry
    directSparseContractedRouteLeadingTokens
  rw [HorizontalContractedRoutedRequest.contractedOutput_inputTokens]
  unfold HorizontalContractedRoutedRequest.contractedOutputTokens
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [PeriodicThreeDM.ContractedRouteRasterSource.rasterizeDirections_routeBlock,
    directions]
  unfold GadgetSparseRouteRasterRequestTokens.requestBlock
    GadgetSparseRouteRasterRequestTokens.requestTokens
    horizontalAssembledNormalizationRequest
    NormalizationDirectionRequest.Request.tokens
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, List.cons_append, List.nil_append, List.append_assoc]

end PeriodicCNFStripReduction
end LeanTrominoes

end
