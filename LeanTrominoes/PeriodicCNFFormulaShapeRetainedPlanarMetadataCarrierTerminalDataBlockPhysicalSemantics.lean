/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalRetainedTerminalDataBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyBlockSemantics

/-! # Physical carrier terminal blocks as semantic retained links -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Concatenating the physical representative-pair blocks over the stable
carrier keys gives exactly one terminal-data block per semantic retained
carrier link, in presentation order. -/
theorem physicalCarrierTerminalDataBlocks_eq_links
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        (fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              fun pair =>
                carrierLensRouteTerminalDataBlock pair.1.isHorizontal
                  (carrierNodeOrderCoordinateAtPeriod
                      (drawingGridSize source.incidenceGraph) pair.2 -
                    carrierNodeOrderCoordinateAtPeriod
                      (drawingGridSize source.incidenceGraph) pair.1)) =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        fun link =>
          carrierLensRouteTerminalDataBlock link.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position source.incidenceGraph link.first)
              (CarrierNode.position source.incidenceGraph link.second)) := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  rw [retainedDrawingCompleteCarrierLinks_eq_keyBlocks, List.map_flatMap]
  apply List.flatMap_congr
  intro key _keyMember
  exact retainedRepresentativeCarrierNodeTerminalDataBlocks_eq_links
    source.incidenceGraph wellFormed degree isLocal key

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
