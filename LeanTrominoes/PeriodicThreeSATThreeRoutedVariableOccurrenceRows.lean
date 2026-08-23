/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableOccurrenceRowSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorNodup

/-! # Occurrence-prefix rows of the split routed-variable scan -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Scanning the full split descriptor stream against every occurrence-prefix
row emits exactly the optional next-boundary blocks in occurrence order. -/
theorem splitRouteDescriptor_occurrenceRows
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceRouteDescriptors source).flatMap fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          routedVariablePairDescriptorBlock (first, second)) =
      (occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundaryBlock else [] := by
  apply List.flatMap_congr
  intro first firstMember
  exact routedVariablePairDescriptorRow_rankZero
    (splitRouteDescriptors source)
    (splitRouteDescriptors_edgeIndices_nodup source)
    first
    (List.mem_append_left _ firstMember)
    (occurrenceRouteDescriptor_targetPortRank_eq_zero
      source firstMember)

end PeriodicThreeSATThree
end LeanTrominoes
