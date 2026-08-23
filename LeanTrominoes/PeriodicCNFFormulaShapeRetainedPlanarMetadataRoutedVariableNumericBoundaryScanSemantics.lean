/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableBoundaryScanSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEdgeIndexNodup

/-! # Boundary scans of numeric CNF route descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The next-boundary portion of a numeric descriptor square is exactly one
block per rank-zero positive-horizontal descriptor. -/
theorem routedVariableNextBoundaryScan_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((numericRouteDescriptors formula ×ˢ numericRouteDescriptors formula).flatMap
        fun pair =>
          if routedVariableNextBoundaryPair pair then
            routedVariableNextBoundaryBlock else []) =
      (numericRouteDescriptors formula).flatMap fun descriptor =>
        if descriptor.targetPortRank = 0 ∧
            descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else [] :=
  routedVariableNextBoundaryScan_eq_diagonal
    (numericRouteDescriptors formula)
    (numericRouteDescriptor_edgeIndices_nodup formula)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
