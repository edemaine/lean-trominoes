/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-!
# Ordered retained Figure 9 3DM endpoint

This module applies the normalized periodic 3DM encoding to the completed
clockwise-ordered Figure 9 endpoint.  It records the target's nongeometric
promises and transfers perfect matching and incidence-orientation existence
back to satisfiability of the original local periodic CNF.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1000000

/-- Normalized periodic 3DM target of the ordered retained Figure 9
pipeline. -/
def retainedOrderedFixedEightPeriodicThreeDMProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source)

/-- Every triple reference in the ordered normalized target names a declared
colored element. -/
theorem retainedOrderedFixedEightPeriodicThreeDMProblem_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedOrderedFixedEightPeriodicThreeDMProblem source).IsWellFormed := by
  unfold retainedOrderedFixedEightPeriodicThreeDMProblem
  exact
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isWellFormed
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)

/-- Every colored element of the ordered normalized target has degree two
or three. -/
theorem retainedOrderedFixedEightPeriodicThreeDMProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicThreeDMProblem
      source).DegreeTwoOrThree := by
  have finalOccurrences :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_occurrencesAtMostThreeFor
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold RetainedOrderedFixedEightOccurrencesAtMostThree at finalOccurrences
  unfold retainedOrderedFixedEightPeriodicThreeDMProblem
  exact
    @PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_degreeTwoOrThree
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      retainedOrderedFixedEightOneInThreeVariableDecidableEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      finalOccurrences
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
        source)

/-- The ordered normalized 3DM target has a perfect matching exactly when
the original periodic CNF is satisfiable. -/
theorem retainedOrderedFixedEightPeriodicThreeDMProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicThreeDMProblem source).Satisfiable ↔
      source.Satisfiable := by
  have finalOccurrences :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_occurrencesAtMostThreeFor
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold RetainedOrderedFixedEightOccurrencesAtMostThree at finalOccurrences
  unfold retainedOrderedFixedEightPeriodicThreeDMProblem
  exact
    (@PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_satisfiable_iff_source
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      retainedOrderedFixedEightOneInThreeVariableDecidableEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      finalOccurrences
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
        source)).trans
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences)

/-- The abstract incidence graph of the ordered normalized 3DM target admits
the required orientation exactly when the original periodic CNF is
satisfiable. -/
theorem
    retainedOrderedFixedEightPeriodicThreeDMProblem_graphHasOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicThreeDMProblem
        source).GraphHasOrientation ↔
      source.Satisfiable := by
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation
      (retainedOrderedFixedEightPeriodicThreeDMProblem source)).symm.trans
      (retainedOrderedFixedEightPeriodicThreeDMProblem_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
