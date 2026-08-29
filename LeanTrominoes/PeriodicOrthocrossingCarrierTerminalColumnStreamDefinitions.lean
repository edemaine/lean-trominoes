/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalColumnSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairSpanGeometry

/-! # Global retained-carrier terminal columns -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanTerminalColumns

/-- The terminal-data block determined by two retained carrier rank data. -/
def retainedPairTerminalDataBlock
    (first second : CarrierNodeRankDatum) :
    List PeriodicEightOccurrenceSplit.RetainedTerminalData :=
  carrierLensRouteTerminalDataBlock first.horizontal
    (second.orderCoordinate - first.orderCoordinate).toNat

@[simp] theorem retainedPairTerminalDataBlock_eq_signedSpan
    (first second : CarrierNodeRankDatum) :
    retainedPairTerminalDataBlock first second =
      carrierLensRouteTerminalDataBlock first.horizontal
        (second.orderCoordinate - first.orderCoordinate) := by
  unfold retainedPairTerminalDataBlock
  exact carrierLensRouteTerminalDataBlock_toNat _ _

/-- Selected row-major carrier terminal blocks from a deduplicated rank-data
stream. -/
def retainedTerminalDataBlocksFromDatums
    (datums : List CarrierNodeRankDatum) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  let entries := CarrierRankGlobal.enumeration datums
  entries.zipIdx.flatMap fun first =>
    entries.zipIdx.filterMap fun second =>
      if retainedPredicate first second then
        some (retainedPairTerminalDataBlock first.1.1 second.1.1)
      else none

/-- One four-incidence terminal block per selected row-major carrier pair. -/
def retainedTerminalDataBlocks (descriptors : List RouteDescriptor) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  retainedTerminalDataBlocksFromDatums datums

/-- Selected carrier direction ranks in exact global clause presentation. -/
def retainedTerminalDirectionRanks
    (descriptors : List RouteDescriptor) : List Nat :=
  ((retainedTerminalDataBlocks descriptors).map
    terminalDataDirectionRanks).flatten

/-- Selected carrier radial lengths in the same presentation. -/
def retainedTerminalRadialLengths
    (descriptors : List RouteDescriptor) : List Nat :=
  ((retainedTerminalDataBlocks descriptors).map
    terminalDataRadialLengths).flatten

theorem directionRankStream_unaryFields (values : List Nat) :
    directionRankStream
        (UnaryFieldEncoderMachine.unaryFields values) =
      values.flatMap fun value =>
        directionRankBlockOutput
          (UnaryFieldEncoderMachine.unaryField value) := by
  unfold directionRankStream TM2EndDelimitedBlockMap.mappedOutput
  rw [CarrierTaggedSpanRouteDirections.blocks_unaryFields,
    List.flatMap_map]

theorem radialLengthStream_unaryFields (values : List Nat) :
    radialLengthStream
        (UnaryFieldEncoderMachine.unaryFields values) =
      values.flatMap fun value =>
        radialLengthBlockOutput
          (UnaryFieldEncoderMachine.unaryField value) := by
  unfold radialLengthStream TM2EndDelimitedBlockMap.mappedOutput
  rw [CarrierTaggedSpanRouteDirections.blocks_unaryFields,
    List.flatMap_map]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
