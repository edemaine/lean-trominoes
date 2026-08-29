/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierFamilyTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalCoordinateBlockPresentation

/-! # Actual terminal-coordinate column of final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierColumnThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The actual carrier-family coordinate column is the canonical four-entry
terminal block of every retained link in presentation order. -/
theorem finalCarrierTerminalCoordinates_eq_linkBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := PeriodicThreeSATThree.formula source
    let links :=
      retainedDrawingCompleteCarrierLinks retained.incidenceGraph
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaCarrierMetadataNormalizedClauses source) =
      retainedCarrierLinkTerminalCoordinates retained links := by
  exact (finalCarrierTerminalCoordinates_eq_taggedLinks
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets).trans
      (taggedCarrierTerminalCoordinates_eq_linkBlocks
        (PeriodicThreeSATThree.formula source)
        (retainedDrawingCompleteCarrierLinks
          (PeriodicThreeSATThree.formula source).incidenceGraph)
        (crossoverMetadataNormalizedClausesDedup
          (PeriodicThreeSATThree.formula source)).length)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
