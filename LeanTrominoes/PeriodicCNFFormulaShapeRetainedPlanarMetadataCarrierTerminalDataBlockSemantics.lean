/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierTerminalDataBlockNumericPhysicalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierTerminalDataBlockPhysicalSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDataBlockKeyDescriptorSemantics

/-! # Semantic retained-link meaning of compiled carrier terminal blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The descriptor-compiled carrier terminal blocks are exactly the semantic
retained carrier-link blocks in global presentation order. -/
theorem retainedTerminalDataBlocks_numeric_eq_links
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (nonempty : incidencesWithMetadata source ≠ []) :
    CarrierRankOrderedPairs.retainedTerminalDataBlocks
        (numericRouteDescriptors source) =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        fun link =>
          carrierLensRouteTerminalDataBlock link.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position source.incidenceGraph link.first)
              (CarrierNode.position source.incidenceGraph link.second)) := by
  rw [CarrierRankOrderedPairs.retainedTerminalDataBlocks_eq_keyBlocks]
  unfold CarrierRankOrderedPairs.retainedKeyTerminalDataBlocks
  refine (numericCarrierTerminalDataKeyBlocks_eq_physicalPairs
    source nonempty).trans ?_
  exact physicalCarrierTerminalDataBlocks_eq_links
    source wellFormed degree isLocal

/-- Flattening the compiled blocks gives the exact global carrier terminal
datum column, one four-incidence block per retained carrier link. -/
theorem retainedTerminalData_numeric_eq_links
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (nonempty : incidencesWithMetadata source ≠ []) :
    (CarrierRankOrderedPairs.retainedTerminalDataBlocks
      (numericRouteDescriptors source)).flatten =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).flatMap
        fun link =>
          carrierLensRouteTerminalDataBlock link.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position source.incidenceGraph link.first)
              (CarrierNode.position source.incidenceGraph link.second)) := by
  rw [retainedTerminalDataBlocks_numeric_eq_links
    source wellFormed degree isLocal nonempty]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
