/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionRasterCursor
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests

/-! # Compact raster route requests -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace RouteRasterRequest

open Gadget
open PeriodicThreeDM.NormalizationDirectionRequest

structure Metadata where
  gridSize : Nat
  horizontal : Nat
  verticalComplement : Nat
  color : WireColor
  deriving DecidableEq, Repr

def Metadata.period (metadata : Metadata) : Nat :=
  1728 * metadata.gridSize

def Metadata.location (metadata : Metadata) : Cell :=
  ((1728 * metadata.horizontal + 471 : Nat),
    (1728 * metadata.verticalComplement + 1257 : Nat))

structure Request where
  metadata : Metadata
  normalization : PeriodicThreeDM.NormalizationDirectionRequest.Request
  deriving DecidableEq, Repr

def normalizedRecordBlock (request : Request) :
    List GadgetSparseAssignmentTokens.Token :=
  sparseRouteRecordBlocksFromRasterDirections
    request.metadata.period request.metadata.color
    request.metadata.location
    (normalizeThreeRounds request.normalization).directions

end RouteRasterRequest
end PeriodicCNFStripReduction
end LeanTrominoes
