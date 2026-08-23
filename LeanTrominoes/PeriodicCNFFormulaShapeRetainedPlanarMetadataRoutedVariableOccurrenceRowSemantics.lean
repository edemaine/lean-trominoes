/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData
import Mathlib.Data.List.Nodup

/-! # Occurrence rows of the routed-variable pair scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A rank-zero descriptor row contributes only its diagonal next-boundary
block, selected precisely by positive horizontal offset. -/
theorem routedVariablePairDescriptorRow_rankZero
    (descriptors : List RouteDescriptor)
    (edgeIndicesNodup :
      (descriptors.map RouteDescriptor.edgeIndex).Nodup)
    (first : RouteDescriptor) (firstMember : first ∈ descriptors)
    (rankZero : first.targetPortRank = 0) :
    descriptors.flatMap (fun second =>
        routedVariablePairDescriptorBlock (first, second)) =
      if first.offset = ((1, 0) : Cell) then
        routedVariableNextBoundaryBlock else [] := by
  rw [List.flatMap_eq_selected_of_unique descriptors
    (fun second => routedVariablePairDescriptorBlock (first, second))
    first (edgeIndicesNodup.of_map RouteDescriptor.edgeIndex)
    firstMember]
  · simp [routedVariablePairDescriptorBlock,
      routedVariableNextBoundaryPair,
      routedVariableCurrentCyclePair,
      routedVariableNextCyclePair, rankZero]
  · intro second secondMember secondNe
    have edgeIndexNe : first.edgeIndex ≠ second.edgeIndex := by
      intro edgeIndexEq
      exact secondNe
        (List.inj_on_of_nodup_map edgeIndicesNodup
          firstMember secondMember edgeIndexEq).symm
    simp [routedVariablePairDescriptorBlock,
      routedVariableNextBoundaryPair,
      routedVariableCurrentCyclePair,
      routedVariableNextCyclePair, rankZero, edgeIndexNe]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
