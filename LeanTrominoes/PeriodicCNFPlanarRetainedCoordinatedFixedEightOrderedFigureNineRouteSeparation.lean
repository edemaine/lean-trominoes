import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineSplicedRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationOrdering
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackCompleteSeparation

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

/-- Reordering the retained fixed-eight clauses by their clockwise exit
directions preserves the complete relative separation certificate already
proved for the normalized source routes.  This is the suffix/suffix source
geometry consumed by the ordered two-stage splice. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) := by
  apply
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther.orderCanonicalRoutesByClauseDirection
  exact
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      (retainedFinalCopiedSourceRoutes_relativeAvoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- A distinct final relative occurrence remains distinct after recovering
its original source coordinates and changing to the inherited source-route
gauges. -/
private theorem inheritedSourceOccurrencesDifferent
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        source sourcePlacement firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        source sourcePlacement secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    ((first.sourceClauseIndex, first.sourceLiteralIndex), (0, 0)) ≠
      ((second.sourceClauseIndex, second.sourceLiteralIndex),
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          first.sourceClause second.sourceClause
          first.generatedClause second.generatedClause
          relativeTranslate) := by
  intro sourceOccurrencesEqual
  have sourceClauseIndexEqual :
      first.sourceClauseIndex = second.sourceClauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      sourceOccurrencesEqual
  have sourceLiteralIndexEqual :
      first.sourceLiteralIndex = second.sourceLiteralIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
      sourceOccurrencesEqual
  have sourceCoordinatesNotDistinct :
      ¬ (first.sourceClauseIndex ≠ second.sourceClauseIndex ∨
        first.sourceLiteralIndex ≠ second.sourceLiteralIndex) := by
    simp [sourceClauseIndexEqual, sourceLiteralIndexEqual]
  have generatedCoordinatesNotDistinct :
      ¬ (firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) := by
    intro generatedCoordinatesDistinct
    exact sourceCoordinatesNotDistinct
      (first.sourceCoordinatesDistinct_of_generatedDistinct
        source sourcePlacement sourceWidth second
        generatedCoordinatesDistinct)
  simp only [not_or, not_ne_iff] at generatedCoordinatesNotDistinct
  have sourceClauseEqual : first.sourceClause = second.sourceClause := by
    have secondMember :
        (second.sourceClause, first.sourceClauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [sourceClauseIndexEqual] using second.sourceClauseMember
    exact
      (List.mem_zipIdx' first.sourceClauseMember).2.trans
        (List.mem_zipIdx' secondMember).2.symm
  have generatedClauseEqual :
      first.generatedClause = second.generatedClause := by
    have secondMember :
        (second.generatedClause, firstClauseIndex) ∈
          (PeriodicOneInThreeNoUnitsPositioned.formula
            (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx := by
      simpa [generatedCoordinatesNotDistinct.1] using
        second.generatedClauseMember
    exact
      (List.mem_zipIdx' first.generatedClauseMember).2.trans
        (List.mem_zipIdx' secondMember).2.symm
  have adjustedTranslateZero :
      (0, 0) =
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          first.sourceClause second.sourceClause
          first.generatedClause second.generatedClause
          relativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      sourceOccurrencesEqual
  have relativeTranslateZero : relativeTranslate = (0, 0) := by
    simpa [
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
      sourceClauseEqual, generatedClauseEqual,
      Cell.add, Cell.sub] using adjustedTranslateZero.symm
  apply generatedOccurrencesDifferent
  apply Prod.ext
  · exact Prod.ext generatedCoordinatesNotDistinct.1
      generatedCoordinatesNotDistinct.2
  · exact relativeTranslateZero.symm

/-- Two inherited source-route cores of the retained ordered construction
remain relatively separated after factor-`72` refinement.  Removing their
obsolete clause-side heads leaves routes whose only possible listed contact
is at their variable-side tails. -/
theorem
    retainedOrderedFixedEightInheritedSourceRouteTails_relativeSeparated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    let sourceFormula :=
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source
    let sourcePlacement :=
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
    let sourceRoutes :=
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        sourceFormula sourcePlacement
    let firstTransformed :=
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement sourcePlacement first.sourceClause
        first.generatedClause
        (sourceRoutes first.sourceClauseIndex first.sourceLiteralIndex)
    let secondTransformed :=
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement sourcePlacement second.sourceClause
        second.generatedClause
        (sourceRoutes second.sourceClauseIndex second.sourceLiteralIndex)).map
          (Cell.add (outputPlacement.translation relativeTranslate))
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstTransformed.tail secondTransformed.tail ∧
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtTails
        firstTransformed.tail secondTransformed.tail := by
  let sourceFormula :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source
  let sourcePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let sourceRoutes :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source
  have sourceOccurrencesDifferent :=
    inheritedSourceOccurrencesDifferent
      sourceFormula sourcePlacement
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      first second relativeTranslate generatedOccurrencesDifferent
  have sourceAvoids :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).coordinate
      first.sourceClause first.sourceClauseIndex first.sourceClauseMember
      first.sourceLiteral first.sourceLiteralIndex first.sourceLiteralMember
      second.sourceClause second.sourceClauseIndex second.sourceClauseMember
      second.sourceLiteral second.sourceLiteralIndex second.sourceLiteralMember
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
        first.sourceClause second.sourceClause
        first.generatedClause second.generatedClause relativeTranslate)
      sourceOccurrencesDifferent
  exact
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute_tails_relative_separated
      sourceFormula sourcePlacement
      first.sourceClause second.sourceClause
      first.generatedClause second.generatedClause
      (sourceRoutes first.sourceClauseIndex first.sourceLiteralIndex)
      (sourceRoutes second.sourceClauseIndex second.sourceLiteralIndex)
      relativeTranslate sourceAvoids
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_nodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first.sourceClauseMember
        first.sourceLiteralMember)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_nodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty second.sourceClauseMember
        second.sourceLiteralMember)

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
