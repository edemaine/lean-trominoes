/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenData

/-! # Canonical semantics of normalized raster route tokens -/

namespace LeanTrominoes
namespace GadgetSparseRouteRasterNormalizedTokens

open PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRasterRequestTokens

@[simp] theorem metadataOutput_append
    (first second : List ExpandedToken) :
    metadataOutput (first ++ second) =
      metadataOutput first ++ metadataOutput second := by
  simp [metadataOutput]

@[simp] theorem normalizationInput_append
    (first second : List ExpandedToken) :
    normalizationInput (first ++ second) =
      normalizationInput first ++ normalizationInput second := by
  simp [normalizationInput]

@[simp] theorem metadataOutput_map_normalization
    (tokens : List NormalizationToken) :
    metadataOutput (tokens.map ExpandedToken.normalization) = [] := by
  simp [metadataOutput, metadataBlock, List.flatMap_map]

@[simp] theorem normalizationInput_map_normalization
    (tokens : List NormalizationToken) :
    normalizationInput (tokens.map ExpandedToken.normalization) = tokens := by
  simp [normalizationInput, normalizationBlock, List.flatMap_map]

@[simp] theorem metadataOutput_requestEnd :
    metadataOutput [.requestEnd] = [] := rfl

@[simp] theorem normalizationInput_requestEnd :
    normalizationInput [.requestEnd] = [] := rfl

@[simp] theorem normalizationInput_expandedMetadataTokens
    (metadata : Metadata) :
    normalizationInput (expandedMetadataTokens metadata) = [] := by
  unfold expandedMetadataTokens normalizationInput
  simp [normalizationBlock]

/-- Metadata projection of a canonical expanded request drops exactly its
normalizer suffix and request delimiter. -/
@[simp] theorem metadataOutput_expandedRequestBlock (request : Request) :
    metadataOutput (expandedRequestBlock request) =
      metadataOutput (expandedMetadataTokens request.metadata) := by
  simp [expandedRequestBlock]

/-- Normalizer projection of a canonical expanded request recovers exactly
the original finite request word. -/
@[simp] theorem normalizationInput_expandedRequestBlock (request : Request) :
    normalizationInput (expandedRequestBlock request) =
      request.normalization.tokens := by
  simp [expandedRequestBlock]

end GadgetSparseRouteRasterNormalizedTokens
end LeanTrominoes
