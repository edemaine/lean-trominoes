import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineSplicedRouteSeparation

/-!
# Relative separation interface for ordered retained Figure 9 routes

This module specializes the generic relative splice assembly to the retained
clockwise-ordered fixed-eight source.  It identifies the complete global
separation obligation with six explicit component predicates for each pair of
incidences and relative lattice translation, and connects that obligation all
the way to ribbon readiness of the normalized drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance orderedComposedVariableDecidableEqForSeparation
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Four pointwise avoidance conditions—ordinary local/local and
suffix/suffix separation plus strict separation of the two cross pairs—imply
complete raw relative route separation for the retained ordered family. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_avoidances
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (avoidances :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairAvoidances
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
                  source)
                (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                  source)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_relativeIncidenceRoutesAvoidEachOther_of_avoidances
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        avoidances

/-- The six generic component conditions, instantiated at every distinct
relative pair of incidences of the retained ordered composed formula, imply
complete raw relative route separation. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (components :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairComponentsSeparated
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
                  source)
                (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                  source)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_relativeIncidenceRoutesAvoidEachOther_of_components
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        components

/-- The same component family is the final missing geometric input for the
normalized ordered drawing's ribbon-ready certificate. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (components :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairComponentsSeparated
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
                  source)
                (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                  source)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_rawRelativeIncidenceRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_components
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty components

end PeriodicOrthocrossing
end LeanTrominoes
