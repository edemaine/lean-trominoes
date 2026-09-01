/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelBatchSemantics
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData

/-! # Clockwise decoded semantics of normalized bend record blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace BendNormalizedFallbackRouteTailRecords

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction
open BinaryRouteTailRecordClockwiseRelabel
open BendFallbackRouteTailRecords
open PeriodicEightOccurrenceSplit

/-- One normalized bend formatter block decodes to its two implication
records, with each pair of presentation tails exchanged exactly when the
clockwise relabeler says that its descriptor requires it. -/
theorem decodedBlockRecords_block
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    decodedBlockRecords (block geometry first second third fourth) =
      sourceClauseRecords
          (BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false true))
          (if profileNeedsSwap
              (BinaryRouteTailRecordFormatter.descriptorProfile
                (bendClauseDescriptor
                  geometry.firstPort geometry.secondPort false true)) then
            [(routeDirections geometry 0 1 second).tail,
              (routeDirections geometry 0 0 first).tail]
          else
            [(routeDirections geometry 0 0 first).tail,
              (routeDirections geometry 0 1 second).tail]) ++
        sourceClauseRecords
          (BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false false))
          (if profileNeedsSwap
              (BinaryRouteTailRecordFormatter.descriptorProfile
                (bendClauseDescriptor
                  geometry.firstPort geometry.secondPort false false)) then
            [(routeDirections geometry 1 1 fourth).tail,
              (routeDirections geometry 1 0 third).tail]
          else
            [(routeDirections geometry 1 0 third).tail,
              (routeDirections geometry 1 1 fourth).tail]) := by
  rfl

end BendNormalizedFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
