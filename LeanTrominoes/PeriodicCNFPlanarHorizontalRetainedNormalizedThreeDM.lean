/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGauge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalizedOneDimensional

/-!
# One-dimensional normalized 3DM image of the retained source
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The normalized planar Figure 10 problem over the twice-scaled final
gauged retained source remains one-dimensional. -/
theorem
    retainedOrderedFixedEightFinalGaugedPaddedNormalizedProblem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).scale 2)
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source).scale 2)).IsOneDimensional := by
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isOneDimensional
  simpa only [PositionedPeriodicCNF.erase_scale] using
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_isOneDimensional
      wellFormed degree graphLocal sourceLocal sourceWidth
      sourceOccurrences sourceClausesNonempty horizontal)

end PeriodicOrthocrossing
end LeanTrominoes
