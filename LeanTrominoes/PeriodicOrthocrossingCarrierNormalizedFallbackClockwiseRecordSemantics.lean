/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelBatchSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData

/-! # Clockwise decoded semantics of normalized carrier record blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierNormalizedFallbackRouteTailRecords

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction
open BinaryRouteTailRecordClockwiseRelabel
open CarrierFallbackRouteTailRecords
open PeriodicEightOccurrenceSplit

/-- One normalized carrier formatter block decodes with its forward tails
reversed and its backward tails reversed exactly in the horizontal case. -/
theorem decodedBlockRecords_block
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    decodedBlockRecords (block geometry first second third fourth) =
      sourceClauseRecords
          (BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor geometry.horizontal
              geometry.nextSlice true))
          [(routeDirections geometry 0 1 second).tail,
            (routeDirections geometry 0 0 first).tail] ++
        sourceClauseRecords
          (BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor geometry.horizontal
              geometry.nextSlice false))
          (if geometry.horizontal then
            [(routeDirections geometry 1 1 fourth).tail,
              (routeDirections geometry 1 0 third).tail]
          else
            [(routeDirections geometry 1 0 third).tail,
              (routeDirections geometry 1 1 fourth).tail]) := by
  unfold decodedBlockRecords block
  rw [BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap_carrier_forward,
    BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap_carrier_backward]
  simp

end CarrierNormalizedFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
