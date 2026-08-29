/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingData
import LeanTrominoes.PeriodicOrthocrossingBendFallbackRouteTailRecordBlockData

/-! # Flattened bend fallback record-block routes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendFallbackRouteTailRecords

open PeriodicEightOccurrenceSplit

theorem blockRoutes_blocks
    (geometries : List Geometry)
    (slots : List RetainedTerminalSlot) :
    BinaryRouteTailRecordProfileFraming.blockRoutes
        (blocks geometries slots) =
      FallbackSuffixDirectionCompiler.retainedJoinedDirections
        (routePairs geometries slots) := by
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
      simp only [blocks, routePairs, queryBlocks,
        BinaryRouteTailRecordProfileFraming.blockRoutes,
        List.flatMap_cons]
      rw [List.zip_append
        (by simp [Geometry.prefixWords, queryBlock])]
      dsimp only [block]
      rw [show
        FallbackSuffixDirectionCompiler.retainedJoinedDirections
            ((geometry.prefixWords.zip
                (queryBlock geometry first second third fourth)) ++
              (geometries.flatMap Geometry.prefixWords).zip
                (queryBlocks geometries slots)) =
          FallbackSuffixDirectionCompiler.retainedJoinedDirections
              (geometry.prefixWords.zip
                (queryBlock geometry first second third fourth)) ++
            FallbackSuffixDirectionCompiler.retainedJoinedDirections
              ((geometries.flatMap Geometry.prefixWords).zip
                (queryBlocks geometries slots)) by
        simp [FallbackSuffixDirectionCompiler.retainedJoinedDirections]]
      have tailEq := induction slots
      unfold BinaryRouteTailRecordProfileFraming.blockRoutes routePairs at tailEq
      rw [tailEq]
      rw [show
        FallbackSuffixDirectionCompiler.retainedJoinedDirections
            (geometry.prefixWords.zip
              (queryBlock geometry first second third fourth)) =
          (routeDirectionBlock geometry first second third fourth).flatMap
            DelimitedRouteJoin.delimited by
        rfl]
      simp only [routeDirectionBlock, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]

end BendFallbackRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
