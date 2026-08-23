/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListKeyedDiagonalFlatMap
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData

/-! # Diagonal semantics of the routed-variable boundary scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- On a descriptor list with distinct stored edge indices, the next-boundary
predicate selects exactly the diagonal rank-zero descriptors with positive
horizontal offset. -/
theorem routedVariableNextBoundaryScan_eq_diagonal
    (descriptors : List RouteDescriptor)
    (edgeIndicesNodup :
      (descriptors.map RouteDescriptor.edgeIndex).Nodup) :
    ((descriptors ×ˢ descriptors).flatMap fun pair =>
        if routedVariableNextBoundaryPair pair then
          routedVariableNextBoundaryBlock else []) =
      descriptors.flatMap fun descriptor =>
        if descriptor.targetPortRank = 0 ∧
            descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else [] := by
  rw [List.keyedProduct_flatMap_eq_diagonal descriptors
    RouteDescriptor.edgeIndex
    (fun pair =>
      if routedVariableNextBoundaryPair pair then
        routedVariableNextBoundaryBlock else [])
    edgeIndicesNodup]
  · apply List.flatMap_congr
    intro descriptor _descriptorMember
    simp [routedVariableNextBoundaryPair]
  · intro first _firstMember second _secondMember edgeIndexNe
    simp [routedVariableNextBoundaryPair, edgeIndexNe]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
