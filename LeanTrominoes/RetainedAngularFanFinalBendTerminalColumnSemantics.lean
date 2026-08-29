/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendFamilyTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularFanFinalBendTerminalCoordinateBlockPresentation

/-! # Actual terminal-coordinate column of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendColumnThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The actual bend-family coordinate column is the canonical four-entry
terminal block of every untranslated routed bend in presentation order. -/
theorem finalBendTerminalCoordinates_eq_bendBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := PeriodicThreeSATThree.formula source
    let bends := baseRouteBends retained
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length +
        (formulaCarrierMetadataNormalizedClauses source).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaBaseBendNormalizedClauses source) =
      retainedBendTerminalCoordinates bends := by
  exact (finalBendTerminalCoordinates_eq_taggedBends
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets).trans
      (taggedBendTerminalCoordinates_eq_bendBlocks
        (baseRouteBends (PeriodicThreeSATThree.formula source))
        ((crossoverMetadataNormalizedClausesDedup
            (PeriodicThreeSATThree.formula source)).length +
          (formulaCarrierMetadataNormalizedClauses source).length))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
