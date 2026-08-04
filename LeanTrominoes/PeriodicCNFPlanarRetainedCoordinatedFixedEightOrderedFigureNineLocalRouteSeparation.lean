import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds
import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Local-route separation for the ordered retained Figure 9 construction

The extra whole-source factor two turns the tight radius-36 local Figure 9
neighborhoods into neighborhoods of a factor-144 lattice.  Consequently two
local routes are contact-free whenever their unscaled source-gauge centers
are distinct.  This module exposes the remaining equal-center case together
with all source-clause provenance needed to solve it inside one finite
Figure 9 template.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance orderedLocalRouteVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- For two genuine final incidences, recover their unscaled clockwise
source clauses.  Either the corresponding source-gauge centers coincide, or
the two relatively positioned normalized local routes are contact-free. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_sameSourceGaugeCenter_or_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    ∃ firstMetadata secondMetadata
        firstSourceClause secondSourceClause,
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          firstClauseIndex]? = some firstMetadata ∧
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          secondClauseIndex]? = some secondMetadata ∧
      firstMetadata.clause = firstClause ∧
      secondMetadata.clause = secondClause ∧
      (firstSourceClause, firstMetadata.sourceClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      (secondSourceClause, secondMetadata.sourceClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      firstMetadata.sourceClause =
        firstSourceClause.scale retainedFigureNineSourceClearanceFactor ∧
      secondMetadata.sourceClause =
        secondSourceClause.scale retainedFigureNineSourceClearanceFactor ∧
      (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source)
          firstSourceClause firstClause =
        Cell.add
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source).translation relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source)
            secondSourceClause secondClause) ∨
        RoutesStrictlyAvoidEachOther
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)
            firstClauseIndex firstLiteralIndex)
          ((PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source)
              secondClauseIndex secondLiteralIndex).map
            (Cell.add
              ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)).translation
                  relativeTranslate)))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
        clearanceSource clearancePlacement
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        firstClauseMember firstLiteralMember with
    ⟨firstMetadata, firstLookup, firstClauseEq,
      firstClearanceSourceMember, firstBounded⟩
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
        clearanceSource clearancePlacement
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        secondClauseMember secondLiteralMember with
    ⟨secondMetadata, secondLookup, secondClauseEq,
      secondClearanceSourceMember, secondBounded⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      firstClearanceSourceMember with
    ⟨firstSourceClause, firstSourceMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      secondClearanceSourceMember with
    ⟨secondSourceClause, secondSourceMember, secondSourceEq⟩
  refine
    ⟨firstMetadata, secondMetadata,
      firstSourceClause, secondSourceClause,
      firstLookup, secondLookup, firstClauseEq, secondClauseEq,
      firstSourceMember, secondSourceMember,
      firstSourceEq, secondSourceEq, ?_⟩
  let firstCenter :=
    PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
      clockwisePlacement firstSourceClause firstClause
  let secondCenter :=
    Cell.add (clockwisePlacement.translation relativeTranslate)
      (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
        clockwisePlacement secondSourceClause secondClause)
  by_cases centersEqual : firstCenter = secondCenter
  · exact Or.inl centersEqual
  · apply Or.inr
    apply
      routesStrictlyAvoidEachOther_of_distinct_offsetScaledCoordinateNeighborhoods
        (firstCenter := firstCenter)
        (secondCenter := secondCenter)
        (factor := 144)
        (radius := 36)
        (offset :=
          PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset)
        centersEqual
    · native_decide
    · native_decide
    · intro point pointMember
      have bounded := firstBounded point pointMember
      have centerEq :
          Cell.add
              (Cell.scale
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                  clearancePlacement firstMetadata.sourceClause firstClause))
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset =
            Cell.add
              (Cell.scale
                144
                firstCenter)
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset := by
        rw [firstSourceEq]
        apply Prod.ext <;>
          simp [firstCenter, clockwisePlacement, clearancePlacement,
            retainedFigureNineClearancePlacement,
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
            PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
            PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
            Cell.add, Cell.sub, Cell.scale] <;>
          ring
      rwa [centerEq] at bounded
    · intro point pointMember
      rcases List.mem_map.mp pointMember with
        ⟨sourcePoint, sourcePointMember, rfl⟩
      have bounded :=
        (secondBounded sourcePoint sourcePointMember).translate
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            clearanceSource clearancePlacement).translation
              relativeTranslate)
      have centerEq :
          Cell.add
              ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                clearanceSource clearancePlacement).translation
                  relativeTranslate)
              (Cell.add
                (Cell.scale
                  PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                  (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                    clearancePlacement secondMetadata.sourceClause
                    secondClause))
                PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset) =
            Cell.add
              (Cell.scale
                144
                secondCenter)
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset := by
        rw [secondSourceEq]
        apply Prod.ext <;>
          simp [secondCenter, clockwisePlacement,
            clearanceSource, clearancePlacement,
            retainedFigureNineClearancePlacement,
            PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
            PeriodicOneInThreeNoUnitsPositioned.placement,
            PeriodicOneInThreePositioned.placement,
            PeriodicVariablePlacement.translation,
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
            PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
            PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
            Cell.add, Cell.sub, Cell.scale] <;>
          ring
      rw [centerEq] at bounded
      simpa [clearanceSource, clearancePlacement] using bounded

end PeriodicOrthocrossing
end LeanTrominoes
