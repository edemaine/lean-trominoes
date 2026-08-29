/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierTerminalDataBlockSemantics
import LeanTrominoes.RetainedAngularCarrierTaggedTerminalCoordinateFamily

/-! # Coordinate semantics of compiled carrier terminal blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing PlanarThreeSAT

/-- Mapping terminal data to numeric coordinates identifies the compiled
carrier stream with the canonical retained-link coordinate blocks. -/
theorem retainedCarrierLinkTerminalCoordinates_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (nonempty : incidencesWithMetadata source ≠ []) :
    retainedCarrierLinkTerminalCoordinates source
        (retainedDrawingCompleteCarrierLinks source.incidenceGraph) =
      List.map retainedTerminalDataCoordinate
        (CarrierRankOrderedPairs.retainedTerminalDataBlocks
          (numericRouteDescriptors source)).flatten := by
  have dataEq := retainedTerminalData_numeric_eq_links
    source wellFormed degree isLocal nonempty
  have coordinateEq :=
    congrArg (List.map retainedTerminalDataCoordinate) dataEq
  unfold retainedCarrierLinkTerminalCoordinates
  rw [List.map_flatMap] at coordinateEq
  exact coordinateEq.symm

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
