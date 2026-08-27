/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteComplementCursor
import LeanTrominoes.GadgetSparseRouteRasterRequestData

/-! # Compact requests interpreted by complement counters -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace RouteRasterRequest

open Gadget

def Metadata.cursorHorizontal (metadata : Metadata) : Nat :=
  1728 * metadata.horizontal + 471

def Metadata.cursorVertical (metadata : Metadata) : Nat :=
  1728 * metadata.verticalComplement + 1257

/-- The machine-ready state after consuming period, horizontal, and vertical
unary fields. -/
def Metadata.complementLocation (metadata : Metadata) :
    ComplementLocation :=
  ⟨metadata.cursorHorizontal,
    metadata.period - metadata.cursorHorizontal - 1,
    metadata.cursorVertical⟩

/-- The only arithmetic precondition required by the complement parser. -/
def Metadata.CursorValid (metadata : Metadata) : Prop :=
  metadata.cursorHorizontal < metadata.period

theorem Metadata.complementLocation_period
    {metadata : Metadata} (valid : metadata.CursorValid) :
    metadata.complementLocation.period = metadata.period := by
  unfold CursorValid at valid
  unfold complementLocation ComplementLocation.period
  change metadata.cursorHorizontal +
      (metadata.period - metadata.cursorHorizontal - 1) + 1 =
    metadata.period
  omega

@[simp] theorem Metadata.complementLocation_toCell
    (metadata : Metadata) :
    metadata.complementLocation.toNatHorizontal.toCell =
      metadata.location := by
  rfl

/-- Sparse record block computed by the two complementary horizontal unary
counters and signed vertical counter. -/
def complementRecordBlock (request : Request) :
    List GadgetSparseAssignmentTokens.Token :=
  sparseRouteRecordBlocksFromComplementDirections request.metadata.color
    request.metadata.complementLocation
    (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
      request.normalization).directions

/-- Every valid compact request's complement interpretation is exactly its
previously certified raster-cursor interpretation. -/
theorem complementRecordBlock_eq_normalizedRecordBlock
    (request : Request) (valid : request.metadata.CursorValid) :
    complementRecordBlock request = normalizedRecordBlock request := by
  unfold complementRecordBlock normalizedRecordBlock
  rw [sparseRouteRecordBlocksFromComplementDirections_eq]
  rw [request.metadata.complementLocation_period valid]
  rw [sparseRouteRecordBlocksFromNatHorizontalDirections_eq
    request.metadata.period (by
      unfold Metadata.CursorValid at valid
      omega)]
  rw [Metadata.complementLocation_toCell]

end RouteRasterRequest
end PeriodicCNFStripReduction
end LeanTrominoes
