/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestData

/-! # Data for finite compact raster route request tokens -/

namespace LeanTrominoes
namespace GadgetSparseRouteRasterRequestTokens

open PeriodicCNFStripReduction.RouteRasterRequest

abbrev NormalizationToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Token

inductive Token
  | scaledUnit
  | horizontalOffset
  | verticalOffset
  | periodEnd
  | horizontalEnd
  | verticalEnd
  | color (value : Gadget.WireColor)
  | normalization (value : NormalizationToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

inductive IntermediateToken
  | scale144Unit
  | scale12Unit
  | unit
  | periodEnd
  | horizontalEnd
  | verticalEnd
  | color (value : Gadget.WireColor)
  | normalization (value : NormalizationToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

inductive PreparedToken
  | scale12Unit
  | unit
  | periodEnd
  | horizontalEnd
  | verticalEnd
  | color (value : Gadget.WireColor)
  | normalization (value : NormalizationToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

inductive ExpandedToken
  | unit
  | periodEnd
  | horizontalEnd
  | verticalEnd
  | color (value : Gadget.WireColor)
  | normalization (value : NormalizationToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

def firstBlock : Token → List IntermediateToken
  | .scaledUnit => List.replicate 12 .scale144Unit
  | .horizontalOffset =>
      List.replicate 3 .scale144Unit ++
        List.replicate 3 .scale12Unit ++ List.replicate 3 .unit
  | .verticalOffset =>
      List.replicate 8 .scale144Unit ++
        List.replicate 8 .scale12Unit ++ List.replicate 9 .unit
  | .periodEnd => [.periodEnd]
  | .horizontalEnd => [.horizontalEnd]
  | .verticalEnd => [.verticalEnd]
  | .color value => [.color value]
  | .normalization value => [.normalization value]
  | .requestEnd => [.requestEnd]

def secondBlock : IntermediateToken → List PreparedToken
  | .scale144Unit => List.replicate 12 .scale12Unit
  | .scale12Unit => [.scale12Unit]
  | .unit => [.unit]
  | .periodEnd => [.periodEnd]
  | .horizontalEnd => [.horizontalEnd]
  | .verticalEnd => [.verticalEnd]
  | .color value => [.color value]
  | .normalization value => [.normalization value]
  | .requestEnd => [.requestEnd]

def thirdBlock : PreparedToken → List ExpandedToken
  | .scale12Unit => List.replicate 12 .unit
  | .unit => [.unit]
  | .periodEnd => [.periodEnd]
  | .horizontalEnd => [.horizontalEnd]
  | .verticalEnd => [.verticalEnd]
  | .color value => [.color value]
  | .normalization value => [.normalization value]
  | .requestEnd => [.requestEnd]

def firstExpand (tokens : List Token) : List IntermediateToken :=
  tokens.flatMap firstBlock

def secondExpand (tokens : List IntermediateToken) : List PreparedToken :=
  tokens.flatMap secondBlock

def thirdExpand (tokens : List PreparedToken) : List ExpandedToken :=
  tokens.flatMap thirdBlock

def expand (tokens : List Token) : List ExpandedToken :=
  thirdExpand (secondExpand (firstExpand tokens))

def metadataTokens (metadata : Metadata) : List Token :=
  List.replicate metadata.gridSize .scaledUnit ++ [.periodEnd] ++
    List.replicate metadata.horizontal .scaledUnit ++
      [.horizontalOffset] ++ [.horizontalEnd] ++
    List.replicate metadata.verticalComplement .scaledUnit ++
      [.verticalOffset] ++ [.verticalEnd] ++ [.color metadata.color]

def expandedMetadataTokens (metadata : Metadata) : List ExpandedToken :=
  List.replicate metadata.period .unit ++ [.periodEnd] ++
    List.replicate (1728 * metadata.horizontal + 471) .unit ++
      [.horizontalEnd] ++
    List.replicate (1728 * metadata.verticalComplement + 1257) .unit ++
      [.verticalEnd] ++ [.color metadata.color]

def requestTokens (request : Request) : List Token :=
  metadataTokens request.metadata ++
    request.normalization.tokens.map .normalization

def requestBlock (request : Request) : List Token :=
  requestTokens request ++ [.requestEnd]

def tokens (requests : List Request) : List Token :=
  requests.flatMap requestBlock

def expandedRequestBlock (request : Request) : List ExpandedToken :=
  expandedMetadataTokens request.metadata ++
    request.normalization.tokens.map .normalization ++ [.requestEnd]

def expandedTokens (requests : List Request) : List ExpandedToken :=
  requests.flatMap expandedRequestBlock

end GadgetSparseRouteRasterRequestTokens
end LeanTrominoes
