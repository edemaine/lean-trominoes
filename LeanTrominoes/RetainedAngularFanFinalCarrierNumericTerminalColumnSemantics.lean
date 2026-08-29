/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierTerminalCoordinateSemantics

/-! # Compiled numeric semantics of the final carrier terminal column -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalCarrierNumericColumnThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The descriptor-compiled carrier terminal data maps to exactly the
actual terminal-coordinate column of the final carrier clause family. -/
theorem finalCarrierTerminalCoordinates_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (retainedNonempty : incidencesWithMetadata
      (PeriodicThreeSATThree.formula source) ≠ []) :
    let retained := PeriodicThreeSATThree.formula source
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaCarrierMetadataNormalizedClauses source) =
      List.map retainedTerminalDataCoordinate
        (CarrierRankOrderedPairs.retainedTerminalDataBlocks
          (numericRouteDescriptors retained)).flatten := by
  exact (finalCarrierTerminalCoordinates_eq_linkBlocks
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets).trans
      (retainedCarrierLinkTerminalCoordinates_eq_numeric
        (PeriodicThreeSATThree.formula source)
        (formula_incidenceGraph_isWellFormed source)
        (formula_incidenceGraph_degreeAtMostThree sourceWidth)
        (formula_incidenceGraph_isLocal sourceLocal)
        retainedNonempty)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
