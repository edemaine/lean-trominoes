/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingData
import LeanTrominoes.BoundedDelimitedDirectionCancellationDelimited
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanBendRouteCancellation
import LeanTrominoes.RetainedAngularFanNormalizedFallbackJoinedDirectionSemantics

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

/-- Cancellation acts pointwise on the four pre-cancellation words of one
genuine bend block. -/
theorem routeDirectionBlock_flatMap_delimited_eq_cancelled
    (geometry : Geometry)
    (different : geometry.firstPort ≠ geometry.secondPort)
    (first second third fourth : RetainedTerminalSlot) :
    (routeDirectionBlock geometry first second third fourth).flatMap
        DelimitedRouteJoin.delimited =
      (geometry.prefixWords.zip
          (BendFallbackRouteTailRecords.queryBlock geometry
            first second third fourth)).flatMap fun value =>
        BoundedDelimitedDirectionCancellation.output
          (DelimitedRouteJoin.delimited
            (value.1 ++
              NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedOrdinarySuffixDirections
                value.2)) := by
  simp only [routeDirectionBlock, routeDirections,
    BendFallbackRouteTailRecords.Geometry.prefixWords,
    BendFallbackRouteTailRecords.queryBlock,
    BendFallbackRouteTailRecords.routeQuery,
    NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedOrdinarySuffixDirections,
    retainedAngularFanSourceClearanceFactor_eq, Prod.eta,
    List.zip_cons_cons, List.zip_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  have cancel00 :=
    boundedCancellation_bendRoutePreCancellationDirections
      geometry.firstPort geometry.secondPort different
      0 0 (by omega) (by omega) first
  have cancel01 :=
    boundedCancellation_bendRoutePreCancellationDirections
      geometry.firstPort geometry.secondPort different
      0 1 (by omega) (by omega) second
  have cancel10 :=
    boundedCancellation_bendRoutePreCancellationDirections
      geometry.firstPort geometry.secondPort different
      1 0 (by omega) (by omega) third
  have cancel11 :=
    boundedCancellation_bendRoutePreCancellationDirections
      geometry.firstPort geometry.secondPort different
      1 1 (by omega) (by omega) fourth
  simp [bendRoutePreCancellationDirections] at cancel00
  simp [bendRoutePreCancellationDirections] at cancel01
  simp [bendRoutePreCancellationDirections] at cancel10
  simp [bendRoutePreCancellationDirections] at cancel11
  rw [cancel00, cancel01, cancel10, cancel11]

/-- Flattening normalized bend blocks gives bounded junction cancellation
of the normalized-suffix joined stream represented by the aligned pairs. -/
theorem blockRoutes_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot)
    (different : ∀ geometry ∈ geometries,
      geometry.firstPort ≠ geometry.secondPort) :
    BinaryRouteTailRecordProfileFraming.blockRoutes
        (blocks geometries slots) =
      BoundedDelimitedDirectionCancellation.output
        (NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
          (BendFallbackRouteTailRecords.routePairs geometries slots)) := by
  unfold NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
  rw [BoundedDelimitedDirectionCancellation.output_flatMap_delimited]
  induction geometries generalizing slots with
  | nil => rfl
  | cons geometry geometries induction =>
      have geometryDifferent :
          geometry.firstPort ≠ geometry.secondPort :=
        different geometry (by simp)
      have geometriesDifferent : ∀ member ∈ geometries,
          member.firstPort ≠ member.secondPort := by
        intro member memberIn
        exact different member (by simp [memberIn])
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
      rw [List.flatMap_append,
        ← routeDirectionBlock_flatMap_delimited_eq_cancelled
          geometry geometryDifferent first second third fourth]
      have tailEq := induction slots geometriesDifferent
      unfold BinaryRouteTailRecordProfileFraming.blockRoutes
        BendFallbackRouteTailRecords.routePairs at tailEq
      rw [tailEq]
      simp [routeDirectionBlock, List.append_assoc]

end BendNormalizedFallbackRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
