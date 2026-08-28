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

/-- One optional four-incidence terminal block per row-major carrier pair. -/
def retainedTerminalDataBlocks (descriptors : List RouteDescriptor) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  entries.zipIdx.flatMap fun first =>
    entries.zipIdx.map fun second =>
      if retainedPredicate first second then
        carrierLensRouteTerminalDataBlock first.1.1.horizontal
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
      else []

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
