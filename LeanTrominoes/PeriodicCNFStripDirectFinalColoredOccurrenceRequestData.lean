/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinData
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceEndpointFrameData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRoutedRequestBlockCompiler

/-! # Aligned colored occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalColoredOccurrenceRequest

abbrev RequestToken := HorizontalOccurrenceRoutedRequest.Token
abbrev Token := FiniteAlphabetDelimitedBlockJoin.Token RequestToken
abbrev Frame := DirectFinalOccurrenceEndpointFrame.Data
abbrev RouteToken := HorizontalRoutedRouteDirectionRequest.Token
abbrev RoutedBlockToken := HorizontalRoutedRouteHeaderTailBlock.Token

/-- The fixed prefix surrounding the left endpoint of one routed occurrence. -/
def openingBody (frame : Frame) : List RequestToken :=
  [.leading frame.leading, .lane frame.lane]

/-- The fixed suffix surrounding the right endpoint of one routed occurrence. -/
def trailingBody (frame : Frame) : List RequestToken :=
  [.trailing frame.trailing]

def openingBlock (frame : Frame) : List Token :=
  FiniteAlphabetDelimitedBlockJoin.block (openingBody frame)

def trailingBlock (frame : Frame) : List Token :=
  FiniteAlphabetDelimitedBlockJoin.block (trailingBody frame)

def openingBlocks (frames : List Frame) : List Token :=
  frames.flatMap openingBlock

def trailingBlocks (frames : List Frame) : List Token :=
  frames.flatMap trailingBlock

/-- Retag routed-request payloads for the occurrence compiler while retaining
each route boundary. -/
def routedBlockToken : RoutedBlockToken → List Token
  | .request token => [.value (.routed token)]
  | .requestEnd => [.blockEnd]

def routedBlocks (tokens : List RoutedBlockToken) : List Token :=
  tokens.flatMap routedBlockToken

/-- First align every endpoint opening with its variable-length route body. -/
def opened (frames : List Frame) (routes : List RoutedBlockToken) :
    List Token :=
  FiniteAlphabetDelimitedBlockJoin.joined
    (openingBlocks frames) (routedBlocks routes)

/-- Then append the matching endpoint trailing query, yielding one complete
input block for `HorizontalOccurrenceRoutedRequest.output`. -/
def output (frames : List Frame) (routes : List RoutedBlockToken) :
    List Token :=
  FiniteAlphabetDelimitedBlockJoin.joined
    (opened frames routes) (trailingBlocks frames)

/-- Canonical boundary-preserving serialization of raw route-token bodies. -/
def routedSourceBlock (route : List RouteToken) : List RoutedBlockToken :=
  route.map .request ++ [.requestEnd]

def routedSourceBlocks (routes : List (List RouteToken)) :
    List RoutedBlockToken :=
  routes.flatMap routedSourceBlock

def routedBody (route : List RouteToken) : List RequestToken :=
  route.map .routed

end DirectFinalColoredOccurrenceRequest
end LeanTrominoes.PeriodicCNFStripReduction

end
