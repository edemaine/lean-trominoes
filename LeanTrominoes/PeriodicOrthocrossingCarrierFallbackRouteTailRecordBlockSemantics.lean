/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryData

/-! # Semantics of retained-carrier fallback record blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierFallbackRouteTailRecords

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- Forgetting the next-slice profile bit recovers the established selected
axis/span stream exactly. -/
@[simp] theorem map_prefixBlock_selectedGeometries
    (entries : List CarrierFallbackTerminalData.IndexedCarrierEntry) :
    (selectedGeometries entries).map Geometry.prefixBlock =
      CarrierFallbackTerminalData.selectedBlocks entries := by
  unfold selectedGeometries CarrierFallbackTerminalData.selectedBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro second _secondMember
  by_cases retained :
      CarrierRankOrderedPairs.retainedPredicate first second
  · simp [retained, Geometry.prefixBlock]
  · simp [retained]

/-- Four available slots per geometry make the block zipper total. -/
theorem blocks_length
    (geometries : List Geometry)
    (slots : List PeriodicEightOccurrenceSplit.RetainedTerminalSlot)
    (lengthEq : slots.length = 4 * geometries.length) :
    (blocks geometries slots).length = geometries.length := by
  induction geometries generalizing slots with
  | nil =>
      have slotsNil : slots = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst slots
      rfl
  | cons geometry geometries induction =>
      rcases slots with _ | ⟨first, slots⟩
      · simp at lengthEq
      rcases slots with _ | ⟨second, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨third, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨fourth, slots⟩
      · simp at lengthEq
        omega
      have tailLength : slots.length = 4 * geometries.length := by
        simp only [List.length_cons] at lengthEq
        omega
      simp [blocks, induction slots tailLength]

/-- The explicit query quartet is the established carrier policy/terminal
query block at the same four selected occurrence slots. -/
@[simp] theorem queryBlock_eq_carrierQueries
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    queryBlock geometry first second third fourth =
      FallbackSuffixQueries.carrierQueries
        geometry.horizontal geometry.span
        [first, second, third, fourth] := by
  rfl

/-- Delimiting the four complete semantic words gives exactly the retained
join of the canonical scaled carrier prefixes and their aligned suffix
queries. -/
theorem routeDirectionBlock_flatMap_delimited
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    (routeDirectionBlock geometry first second third fourth).flatMap
        DelimitedRouteJoin.delimited =
      FallbackSuffixDirectionCompiler.retainedJoinedDirections
        ((CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
            geometry.horizontal geometry.span).zip
          (queryBlock geometry first second third fourth)) := by
  rfl

/-- The semantic block record is exactly the established pair of binary
Figure 9 clause records using the four complete joined carrier routes. -/
theorem block_records
    (geometry : Geometry)
    (first second third fourth :
      PeriodicEightOccurrenceSplit.RetainedTerminalSlot) :
    (block geometry first second third fourth).records =
      binaryRouteTailRecord
          (carrierClauseDescriptor
            geometry.horizontal geometry.nextSlice true)
          (routeDirections geometry 0 0 first)
          (routeDirections geometry 0 1 second) ++
        binaryRouteTailRecord
          (carrierClauseDescriptor
            geometry.horizontal geometry.nextSlice false)
          (routeDirections geometry 1 0 third)
          (routeDirections geometry 1 1 fourth) := by
  simp [block, BinaryRouteTailRecordBatchFormatter.Block.records,
    binaryRouteTailRecord, BinaryRouteTailRecordFormatter.descriptorProfile,
    carrierClauseDescriptor]

/-- The reusable finite-state batch formatter emits every carrier block's
exact flat record stream. -/
@[simp] theorem formatter_output_blocks
    (geometries : List Geometry)
    (slots : List PeriodicEightOccurrenceSplit.RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.output
        (BinaryRouteTailRecordBatchFormatter.tokens
          (blocks geometries slots)) =
      BinaryRouteTailRecordBatchFormatter.records
        (blocks geometries slots) :=
  BinaryRouteTailRecordBatchFormatter.output_tokens _

end CarrierFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
