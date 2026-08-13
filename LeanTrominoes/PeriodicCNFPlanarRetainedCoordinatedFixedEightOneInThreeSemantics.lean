/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes

/-!
# Semantics of the coordinated retained exact-one pipeline

The coordinated fixed-eight construction changes the positioned geometry
and incidence routes, but erasing positions recovers the same semantic
formula as the established retained fixed-eight pipeline.  This module
transfers its width, occurrence, and end-to-end satisfiability certificates
to the coordinated endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Binary-or-ternary arity gives the final coordinated exact-one formula
the width-three promise expected by the planar 3DM reduction. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase.WidthAtMost 3 := by
  intro clause clauseMember
  rcases
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source clause clauseMember with arity | arity
  · exact arity.le.trans (by decide)
  · exact arity.le

/-- The coordinated geometric realization preserves the final semantic
occurrence-three promise. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase.OccurrencesAtMost 3 := by
  simpa only [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
    retainedDrawingEightOccurrenceSplitPositionedFormula_erase] using
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

/-- The final coordinated unit-free exact-one instance is satisfiable
exactly when the original local periodic CNF is satisfiable. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase ↔
      source.Satisfiable := by
  simpa only [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
    retainedDrawingEightOccurrenceSplitPositionedFormula_erase] using
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
      source sourceLocal sourceWidth sourceOccurrences

end PeriodicOrthocrossing
end LeanTrominoes
