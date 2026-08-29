/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData

/-! # Flattened normalized carrier fallback record-block routes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedFallbackRouteTailRecords

open PeriodicEightOccurrenceSplit
open CarrierFallbackRouteTailRecords

/-- Normalizing route fields does not change the carrier profile stream. -/
theorem blockProfiles_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (blocks geometries slots) =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (CarrierFallbackRouteTailRecords.blocks geometries slots) := by
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
      simp only [blocks, CarrierFallbackRouteTailRecords.blocks,
        BinaryRouteTailRecordProfileFraming.blockProfiles,
        List.flatMap_cons]
      dsimp only [block, CarrierFallbackRouteTailRecords.block]
      apply congrArg (fun tail =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice false)] ++ tail)
      exact induction slots

/-- Flattening normalized carrier blocks gives the exact normalized joined
direction stream represented by the aligned prefix/query pairs. -/
theorem blockRoutes_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordProfileFraming.blockRoutes
        (blocks geometries slots) =
      NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
        (CarrierFallbackRouteTailRecords.routePairs geometries slots) := by
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
      simp only [blocks, CarrierFallbackRouteTailRecords.routePairs,
        CarrierFallbackRouteTailRecords.queryBlocks,
        BinaryRouteTailRecordProfileFraming.blockRoutes,
        List.flatMap_cons]
      rw [List.zip_append
        (by simp [CarrierFallbackRouteTailRecords.queryBlock])]
      dsimp only [block]
      rw [show
        NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
            (((CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
                geometry.horizontal geometry.span).zip
                  (CarrierFallbackRouteTailRecords.queryBlock geometry
                    first second third fourth)) ++
              (geometries.flatMap fun geometry =>
                CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
                  geometry.horizontal geometry.span).zip
                (CarrierFallbackRouteTailRecords.queryBlocks
                  geometries slots)) =
          NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
              ((CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
                geometry.horizontal geometry.span).zip
                  (CarrierFallbackRouteTailRecords.queryBlock geometry
                    first second third fourth)) ++
            NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
              ((geometries.flatMap fun geometry =>
                CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
                  geometry.horizontal geometry.span).zip
                (CarrierFallbackRouteTailRecords.queryBlocks
                  geometries slots)) by
        simp [NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections]]
      have tailEq := induction slots
      unfold BinaryRouteTailRecordProfileFraming.blockRoutes
        CarrierFallbackRouteTailRecords.routePairs at tailEq
      rw [tailEq]
      rw [show
        NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
            ((CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
                geometry.horizontal geometry.span).zip
              (CarrierFallbackRouteTailRecords.queryBlock geometry
                first second third fourth)) =
          (routeDirectionBlock geometry first second third fourth).flatMap
            DelimitedRouteJoin.delimited by
        rfl]
      simp only [routeDirectionBlock, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]

end CarrierNormalizedFallbackRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
