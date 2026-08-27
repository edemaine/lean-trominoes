/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionWords

/-! # Flat Figure 9 tail records for retained carriers and bends -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open FormulaShapeFigureNinePolarityRouteTailRecord
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

/-- Serialize one binary direction-aware clause after deleting the
clause-side direction from each of its two complete route words. -/
def binaryRouteTailRecord
    (descriptor : FormulaShapeDirectionOrdering.Token)
    (first second : List AxisDirection) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  match descriptor with
  | .variable => []
  | .clause profile => clauseRecord profile [first.tail, second.tail]

/-- The two implication clauses of one retained carrier lens, in the same
clause-major incidence order as its canonical direction block. -/
def carrierLensRouteTailRecordBlock
    (horizontal nextSlice : Bool) (span : Nat) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  binaryRouteTailRecord
      (carrierClauseDescriptor horizontal nextSlice true)
      (carrierLensRouteDirections horizontal span 0 0)
      (carrierLensRouteDirections horizontal span 0 1) ++
    binaryRouteTailRecord
      (carrierClauseDescriptor horizontal nextSlice false)
      (carrierLensRouteDirections horizontal span 1 0)
      (carrierLensRouteDirections horizontal span 1 1)

/-- The carrier record block is exactly the generic descriptor/tail-table
serialization consumed by the bounded Figure 9 header expander. -/
theorem carrierLensRouteTailRecordBlock_eq_sourceRecordTokens
    (horizontal nextSlice : Bool) (span : Nat) :
    carrierLensRouteTailRecordBlock horizontal nextSlice span =
      sourceRecordTokens
        (canonicalCarrierLinkDescriptorBlock horizontal nextSlice)
        [[(carrierLensRouteDirections horizontal span 0 0).tail,
          (carrierLensRouteDirections horizontal span 0 1).tail],
         [(carrierLensRouteDirections horizontal span 1 0).tail,
          (carrierLensRouteDirections horizontal span 1 1).tail]] := by
  simp [carrierLensRouteTailRecordBlock, binaryRouteTailRecord,
    sourceRecordTokens, sourceClauses, clauseRecords,
    canonicalCarrierLinkDescriptorBlock, carrierClauseDescriptor]

/-- The two implication clauses of one retained bend, again in canonical
clause-major incidence order. -/
def bendRouteTailRecordBlock
    (firstPort secondPort : CornerPort) (nextSlice : Bool) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  binaryRouteTailRecord
      (bendClauseDescriptor firstPort secondPort nextSlice true)
      (bendRouteDirections firstPort secondPort 0 0)
      (bendRouteDirections firstPort secondPort 0 1) ++
    binaryRouteTailRecord
      (bendClauseDescriptor firstPort secondPort nextSlice false)
      (bendRouteDirections firstPort secondPort 1 0)
      (bendRouteDirections firstPort secondPort 1 1)

/-- The bend record block is the same generic descriptor/tail-table
serialization. -/
theorem bendRouteTailRecordBlock_eq_sourceRecordTokens
    (firstPort secondPort : CornerPort) (nextSlice : Bool) :
    bendRouteTailRecordBlock firstPort secondPort nextSlice =
      sourceRecordTokens
        (canonicalBendDescriptorBlock firstPort secondPort nextSlice)
        [[(bendRouteDirections firstPort secondPort 0 0).tail,
          (bendRouteDirections firstPort secondPort 0 1).tail],
         [(bendRouteDirections firstPort secondPort 1 0).tail,
          (bendRouteDirections firstPort secondPort 1 1).tail]] := by
  simp [bendRouteTailRecordBlock, binaryRouteTailRecord,
    sourceRecordTokens, sourceClauses, clauseRecords,
    canonicalBendDescriptorBlock, bendClauseDescriptor]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
