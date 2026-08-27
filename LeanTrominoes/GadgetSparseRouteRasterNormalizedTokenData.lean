/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestTokenData

/-! # Normalized unary raster route tokens -/

namespace LeanTrominoes
namespace GadgetSparseRouteRasterNormalizedTokens

open PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRasterRequestTokens

/-- Unary raster metadata followed by normalized finite directions. -/
inductive Token
  | unit
  | periodEnd
  | horizontalEnd
  | verticalEnd
  | color (value : Gadget.WireColor)
  | direction (value : AxisDirection)
  | routeEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- Project expanded unary metadata into the normalized alphabet. -/
def metadataBlock : ExpandedToken → List Token
  | .unit => [.unit]
  | .periodEnd => [.periodEnd]
  | .horizontalEnd => [.horizontalEnd]
  | .verticalEnd => [.verticalEnd]
  | .color value => [.color value]
  | .normalization _ => []
  | .requestEnd => []

def metadataOutput (tokens : List ExpandedToken) : List Token :=
  tokens.flatMap metadataBlock

/-- Extract the direction-normalizer request suffix. -/
def normalizationBlock : ExpandedToken → List NormalizationToken
  | .normalization value => [value]
  | _ => []

def normalizationInput (tokens : List ExpandedToken) :
    List NormalizationToken :=
  tokens.flatMap normalizationBlock

/-- Tag one normalized direction word and append its route boundary. -/
def directionOutput (directions : List AxisDirection) : List Token :=
  directions.map .direction ++ [.routeEnd]

/-- Canonical normalized token block represented by one compact request. -/
def normalizedRequestBlock (request : Request) : List Token :=
  metadataOutput (expandedMetadataTokens request.metadata) ++
    directionOutput
      (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
        request.normalization).directions

def normalizedTokens (requests : List Request) : List Token :=
  requests.flatMap normalizedRequestBlock

end GadgetSparseRouteRasterNormalizedTokens
end LeanTrominoes
