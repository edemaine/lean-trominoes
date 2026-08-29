/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendTerminalColumnSemantics
import LeanTrominoes.RetainedAngularBendTerminalCoordinateData

/-! # Compiled numeric semantics of the final bend terminal column -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendNumericColumnThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The compiler-ordered base-bend terminal data maps to exactly the actual
terminal-coordinate column of the final bend clause family. -/
theorem finalBendTerminalCoordinates_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let retained := PeriodicThreeSATThree.formula source
    let start :=
      (crossoverMetadataNormalizedClausesDedup retained).length +
        (formulaCarrierMetadataNormalizedClauses source).length
    retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes retained) start
        (formulaBaseBendNormalizedClauses source) =
      baseBendTerminalCoordinates retained := by
  exact (finalBendTerminalCoordinates_eq_bendBlocks
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets).trans
      (retainedBendTerminalCoordinates_baseRouteBends_eq
        (PeriodicThreeSATThree.formula source))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
