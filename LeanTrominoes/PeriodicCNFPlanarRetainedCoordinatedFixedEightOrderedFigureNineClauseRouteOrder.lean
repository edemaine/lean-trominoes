import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClauseRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes

/-!
# Clause route order for the retained ordered Figure 9 source

This file specializes the finite composed-template route-order theorem to
the retained fixed-eight source used by the hardness pipeline.  Before final
loop erasure, every ternary output route leaves its clause in the canonical
south-west-east literal order required by the 3DM ribbon construction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The complete raw ordered Figure 9 route family has the canonical
ternary-clause exit order. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_ternaryClauseRoutesInUnitEliminationOrder
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          (retainedFigureNineClearancePositionedFormula_widthAtMostThree
            source sourceWidth)
          (retainedFigureNineClearancePositionedFormula_allAtomsNodup
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
