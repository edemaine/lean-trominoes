/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingData
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData

/-! # Flattened normalized bend fallback record-block routes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendNormalizedFallbackRouteTailRecords

open PeriodicEightOccurrenceSplit
open BendFallbackRouteTailRecords

/-- Normalizing route fields does not change the bend profile stream. -/
theorem blockProfiles_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (blocks geometries slots) =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (BendFallbackRouteTailRecords.blocks geometries slots) := by
  induction geometries generalizing slots with
  | nil => rfl
  | cons geometry geometries induction =>
      rcases slots with _ | ⟨first, slots⟩
      · rfl
      rcases slots with _ | ⟨second, slots⟩
      · rfl
      rcases slots with _ | ⟨third, slots⟩
      · rfl
      rcases slots with _ | ⟨fourth, slots⟩
      · rfl
      simp only [blocks, BendFallbackRouteTailRecords.blocks,
        BinaryRouteTailRecordProfileFraming.blockProfiles,
        List.flatMap_cons]
      dsimp only [block, BendFallbackRouteTailRecords.block]
      apply congrArg (fun tail =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.bendClauseDescriptor
              geometry.firstPort geometry.secondPort false true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.bendClauseDescriptor
              geometry.firstPort geometry.secondPort false false)] ++ tail)
      exact induction slots

/-- Flattening normalized bend blocks gives the exact normalized ordinary
joined stream represented by the aligned prefix/query pairs. -/
theorem blockRoutes_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordProfileFraming.blockRoutes
        (blocks geometries slots) =
      NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
        (BendFallbackRouteTailRecords.routePairs geometries slots) := by
  induction geometries generalizing slots with
  | nil => rfl
  | cons geometry geometries induction =>
      rcases slots with _ | ⟨first, slots⟩
      · rfl
      rcases slots with _ | ⟨second, slots⟩
      · rfl
      rcases slots with _ | ⟨third, slots⟩
      · rfl
      rcases slots with _ | ⟨fourth, slots⟩
      · rfl
      simp only [blocks, BendFallbackRouteTailRecords.routePairs,
        BendFallbackRouteTailRecords.queryBlocks,
        BinaryRouteTailRecordProfileFraming.blockRoutes,
        List.flatMap_cons]
      rw [List.zip_append
        (by simp [BendFallbackRouteTailRecords.Geometry.prefixWords,
          BendFallbackRouteTailRecords.queryBlock])]
      dsimp only [block]
      rw [show
        NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
            ((geometry.prefixWords.zip
                (BendFallbackRouteTailRecords.queryBlock geometry
                  first second third fourth)) ++
              (geometries.flatMap
                BendFallbackRouteTailRecords.Geometry.prefixWords).zip
                (BendFallbackRouteTailRecords.queryBlocks
                  geometries slots)) =
          NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
              (geometry.prefixWords.zip
                (BendFallbackRouteTailRecords.queryBlock geometry
                  first second third fourth)) ++
            NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
              ((geometries.flatMap
                BendFallbackRouteTailRecords.Geometry.prefixWords).zip
                (BendFallbackRouteTailRecords.queryBlocks
                  geometries slots)) by
        simp [NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections]]
      have tailEq := induction slots
      unfold BinaryRouteTailRecordProfileFraming.blockRoutes
        BendFallbackRouteTailRecords.routePairs at tailEq
      rw [tailEq]
      rw [show
        NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
            (geometry.prefixWords.zip
              (BendFallbackRouteTailRecords.queryBlock geometry
                first second third fourth)) =
          (routeDirectionBlock geometry first second third fourth).flatMap
            DelimitedRouteJoin.delimited by
        rfl]
      simp only [routeDirectionBlock, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]

end BendNormalizedFallbackRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
