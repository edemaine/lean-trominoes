/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingBendFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryData

/-! # Semantics of retained-bend fallback record blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace BendFallbackRouteTailRecords

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

theorem blocks_length
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot)
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

@[simp] theorem queryBlock_eq_bendQueries
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    queryBlock geometry first second third fourth =
      FallbackSuffixQueries.bendQueries
        geometry.firstPort geometry.secondPort
        [first, second, third, fourth] := by
  rfl

/-- Delimiting the four complete semantic words gives exactly the retained
join of the canonical scaled bend prefixes and their aligned suffix queries. -/
theorem routeDirectionBlock_flatMap_delimited
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    (routeDirectionBlock geometry first second third fourth).flatMap
        DelimitedRouteJoin.delimited =
      FallbackSuffixDirectionCompiler.retainedJoinedDirections
        ((geometry.prefixWords).zip
          (queryBlock geometry first second third fourth)) := by
  rfl

theorem block_records
    (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    (block geometry first second third fourth).records =
      binaryRouteTailRecord
          (bendClauseDescriptor
            geometry.firstPort geometry.secondPort false true)
          (routeDirections geometry 0 0 first)
          (routeDirections geometry 0 1 second) ++
        binaryRouteTailRecord
          (bendClauseDescriptor
            geometry.firstPort geometry.secondPort false false)
          (routeDirections geometry 1 0 third)
          (routeDirections geometry 1 1 fourth) := by
  simp [block, BinaryRouteTailRecordBatchFormatter.Block.records,
    binaryRouteTailRecord, BinaryRouteTailRecordFormatter.descriptorProfile,
    bendClauseDescriptor]

@[simp] theorem formatter_output_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.output
        (BinaryRouteTailRecordBatchFormatter.tokens
          (blocks geometries slots)) =
      BinaryRouteTailRecordBatchFormatter.records
        (blocks geometries slots) :=
  BinaryRouteTailRecordBatchFormatter.output_tokens _

end BendFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
