import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily

/-!
# Same-gauge inherited Figure 9 connector separation

Equal normalized source gauges identify one retained source-clause block.
For a distinct relative pair of final incidences, positivity of the composed
period then forces the recovered occurrences in that block to use different
source slots.  The finite extended-exit-fan certificate can consequently be
transported into their common normalized gauge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance orderedInheritedConnectorVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem value_eq_of_mem_zipIdx_same_index
    {Value : Type*} {values : List Value}
    {first second : Value} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second :=
  (List.mem_zipIdx' firstMember).2.trans
    (List.mem_zipIdx' secondMember).2.symm

/-- Under an equal normalized source gauge, a distinct relative pair of
twice-inherited incidences must already have distinct final coordinates. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedGeneratedCoordinatesDistinct_of_sourceGaugesEqual
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
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    firstClauseIndex ≠ secondClauseIndex ∨
      firstLiteralIndex ≠ secondLiteralIndex := by
  have metadataSourceClauseIndicesEqual :=
    retainedOrderedFixedEightFigureNine_sourceClauseIndex_eq_of_normalizedSourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      first.metadata first.metadataLookup first.metadataClause
      second relativeTranslate (by
        simpa [first.metadataSourceClause] using sourceGaugesEqual)
  have sourceClauseIndicesEqual :
      first.sourceClauseIndex = second.sourceClauseIndex :=
    first.metadataSourceClauseIndex.symm.trans
      metadataSourceClauseIndicesEqual
  by_contra generatedCoordinatesNotDistinct
  simp only [not_or, not_ne_iff] at generatedCoordinatesNotDistinct
  have generatedClausesEqual :
      first.generatedClause = second.generatedClause := by
    apply value_eq_of_mem_zipIdx_same_index first.generatedClauseMember
    simpa [generatedCoordinatesNotDistinct.1] using
      second.generatedClauseMember
  have sourceClausesEqual : first.sourceClause = second.sourceClause := by
    apply value_eq_of_mem_zipIdx_same_index first.sourceClauseMember
    simpa [sourceClauseIndicesEqual] using second.sourceClauseMember
  have outputPeriodPositive :
      0 <
        (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)).period := by
    apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
    apply PeriodicOneInThreePositioned.placement_period_pos
    exact retainedFigureNineClearancePlacement_period_pos source
  have relativeTranslateZero : relativeTranslate = (0, 0) := by
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst sourceGaugesEqual
      simp [sourceClausesEqual, generatedClausesEqual,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale] at coordinateEqual
      simpa using coordinateEqual.resolve_left outputPeriodPositive.ne'
    · have coordinateEqual := congrArg Prod.snd sourceGaugesEqual
      simp [sourceClausesEqual, generatedClausesEqual,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale] at coordinateEqual
      simpa using coordinateEqual.resolve_left outputPeriodPositive.ne'
  apply generatedOccurrencesDifferent
  simp [generatedCoordinatesNotDistinct.1,
    generatedCoordinatesNotDistinct.2, relativeTranslateZero]

/-- The radially extended exit connectors of a distinct inherited pair are
strictly separated when their normalized source gauges agree. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedExtendedConnectors_strictlyAvoidEachOther_of_sourceGaugesEqual
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
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      ((PositionedPeriodicCNF.clauseExitFanData
          first.sourceClause first.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source)
        ).translatedExtendedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause)
          (first.sourceSlot clearanceWidth))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            (second.sourceSlot clearanceWidth))) := by
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
  have metadataSourceClauseIndicesEqual :=
    retainedOrderedFixedEightFigureNine_sourceClauseIndex_eq_of_normalizedSourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      first.metadata first.metadataLookup first.metadataClause
      second relativeTranslate (by
        simpa [first.metadataSourceClause] using sourceGaugesEqual)
  have sourceClauseIndicesEqual :
      first.sourceClauseIndex = second.sourceClauseIndex :=
    first.metadataSourceClauseIndex.symm.trans
      metadataSourceClauseIndicesEqual
  have sourceClausesEqual : first.sourceClause = second.sourceClause := by
    apply value_eq_of_mem_zipIdx_same_index first.sourceClauseMember
    simpa [sourceClauseIndicesEqual] using second.sourceClauseMember
  have generatedCoordinatesDistinct :=
    retainedOrderedFixedEightFigureNine_inheritedGeneratedCoordinatesDistinct_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  have sourceCoordinatesDistinct :=
    first.sourceCoordinatesDistinct_of_generatedDistinct
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      clearanceWidth second generatedCoordinatesDistinct
  have sourceLiteralIndicesDifferent :
      first.sourceLiteralIndex ≠ second.sourceLiteralIndex :=
    sourceCoordinatesDistinct.resolve_left
      (fun different => different sourceClauseIndicesEqual)
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let firstSlot := first.sourceSlot clearanceWidth
  let secondSlot := second.sourceSlot clearanceWidth
  have sourceClauseNonempty : first.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx first.sourceLiteralMember)
  have fanValid : fanData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.sourceClauseMember sourceClauseNonempty
  have fanCount : fanData.count = first.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr sourceClauseNonempty)
      (first.sourceClause_width clearanceWidth)
  have firstSlotActive : fanData.SlotActive firstSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact first.sourceLiteralIndex_lt
  have secondSlotActive : fanData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    change second.sourceLiteralIndex < first.sourceClause.literals.length
    simpa [sourceClausesEqual] using second.sourceLiteralIndex_lt
  have slotsDifferent : firstSlot ≠ secondSlot := by
    intro slotsEqual
    apply sourceLiteralIndicesDifferent
    exact congrArg Fin.val slotsEqual
  have finiteStrict :=
    PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.extendedRoutes_strictlyAvoidEachOther
      fanData fanValid firstSlot secondSlot
      firstSlotActive secondSlotActive slotsDifferent
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement first.sourceClause first.generatedClause
  let secondOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement second.sourceClause second.generatedClause
  let offset := outputPlacement.translation relativeTranslate
  have translatedSecondConnector :
      translatePolyline offset
          (translatePolyline secondOrigin
            (fanData.extendedRoute secondSlot)) =
        translatePolyline firstOrigin
          (fanData.extendedRoute secondSlot) := by
    unfold translatePolyline
    rw [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    apply Prod.ext <;>
      simp [firstOrigin, secondOrigin, offset, outputPlacement,
        sourceGaugesEqual, Cell.add] <;>
      ring
  have translatedStrict := finiteStrict.translatePolyline firstOrigin
  dsimp only
  rw [show
    PositionedPeriodicCNF.clauseExitFanData
        second.sourceClause second.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source) = fanData by
      simp [fanData, sourceClausesEqual, sourceClauseIndicesEqual]]
  simp only [
    PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedExtendedRoute]
  change
    RoutesStrictlyAvoidEachOther
      (translatePolyline firstOrigin (fanData.extendedRoute firstSlot))
      (translatePolyline offset
        (translatePolyline secondOrigin
          (fanData.extendedRoute secondSlot)))
  rw [translatedSecondConnector]
  exact translatedStrict

end PeriodicOrthocrossing
end LeanTrominoes
