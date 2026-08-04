import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalInheritedSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineTranslatedOrderedInheritedRouteSplicing

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

private theorem composedSourceLocalPosition_injective_below_three
    {firstIndex secondIndex : Nat}
    (firstLt : firstIndex < 3)
    (secondLt : secondIndex < 3)
    (positionsEqual :
      PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition firstIndex =
        PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition secondIndex) :
    firstIndex = secondIndex := by
  have firstCases :
      firstIndex = 0 ∨ firstIndex = 1 ∨ firstIndex = 2 := by
    omega
  have secondCases :
      secondIndex = 0 ∨ secondIndex = 1 ∨ secondIndex = 2 := by
    omega
  rcases firstCases with rfl | rfl | rfl <;>
    rcases secondCases with rfl | rfl | rfl <;>
    simp [PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition]
      at positionsEqual ⊢

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

/-- Distinct inherited final incidences in one normalized source gauge
recover different source-literal slots. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSourceLiteralIndicesDifferent_of_sourceGaugesEqual
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
    first.sourceLiteralIndex ≠ second.sourceLiteralIndex := by
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
  have generatedCoordinatesDistinct :=
    retainedOrderedFixedEightFigureNine_inheritedGeneratedCoordinatesDistinct_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  have sourceCoordinatesDistinct :=
    first.sourceCoordinatesDistinct_of_generatedDistinct
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      second generatedCoordinatesDistinct
  exact sourceCoordinatesDistinct.resolve_left
    (fun different => different sourceClauseIndicesEqual)

/-- A retained inherited extended connector begins at the recovered composed
source port in its final clause gauge. -/
theorem retainedOrderedFixedEightFigureNine_inheritedExtendedConnector_head?
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clauseIndex literalIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    ((PositionedPeriodicCNF.clauseExitFanData
        data.sourceClause data.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source)
      ).translatedExtendedRoute
        (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement data.sourceClause data.generatedClause)
        (data.sourceSlot clearanceWidth)).head? =
      some
        (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
          outputPlacement data.sourceClause data.generatedClause
          data.sourceLiteralIndex) := by
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx data.sourceLiteralMember)
  have fanValid : fanData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember sourceClauseNonempty
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr sourceClauseNonempty)
      (data.sourceClause_width clearanceWidth)
  have slotActive : fanData.SlotActive slot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact data.sourceLiteralIndex_lt
  dsimp only
  change
    (fanData.translatedExtendedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement data.sourceClause data.generatedClause)
      slot).head? = _
  rw [PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedExtendedRoute_head?
    _ fanData fanValid slot slotActive]
  simp [PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
    slot,
    PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  rfl

/-- For a distinct inherited pair in one normalized source gauge, the first
local route strictly avoids the translated second inherited suffix. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesEqual
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
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let firstLocalRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      firstClauseIndex firstLiteralIndex
  let secondConnector :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedExtendedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  let offset := outputPlacement.translation relativeTranslate
  have sourceLiteralIndicesDifferent :=
    retainedOrderedFixedEightFigureNine_inheritedSourceLiteralIndicesDifferent_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  have firstIndexLtThree : first.sourceLiteralIndex < 3 := by
    have sourceIndexLt := first.sourceLiteralIndex_lt
    have sourceWidthAtMost := first.sourceClause_width clearanceWidth
    omega
  have secondIndexLtThree : second.sourceLiteralIndex < 3 := by
    have sourceIndexLt := second.sourceLiteralIndex_lt
    have sourceWidthAtMost := second.sourceClause_width clearanceWidth
    omega
  have sourceGaugesEqual' :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement first.sourceClause first.generatedClause =
        Cell.add offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement second.sourceClause second.generatedClause) := by
    simpa [outputPlacement, offset, clearanceSource,
      clearancePlacement] using sourceGaugesEqual
  have sourcePortsDifferent :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
          outputPlacement first.sourceClause first.generatedClause
          first.sourceLiteralIndex ≠
        Cell.add offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement second.sourceClause second.generatedClause
            second.sourceLiteralIndex) := by
    intro portsEqual
    apply sourceLiteralIndicesDifferent
    apply composedSourceLocalPosition_injective_below_three
      firstIndexLtThree secondIndexLtThree
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst portsEqual
      have gaugeCoordinateEqual := congrArg Prod.fst sourceGaugesEqual'
      simp [PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
        Cell.add] at coordinateEqual gaugeCoordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd portsEqual
      have gaugeCoordinateEqual := congrArg Prod.snd sourceGaugesEqual'
      simp [PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
        Cell.add] at coordinateEqual gaugeCoordinateEqual ⊢
      nlinarith
  have firstLocalEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      first.generatedClauseMember first.generatedLiteralMember
  have firstLocalLast :
      firstLocalRoute.getLast? =
        some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement first.sourceClause first.generatedClause
            first.sourceLiteralIndex) := by
    rw [firstLocalEndpoints.2]
    exact congrArg some first.localEndpoint
  have secondConnectorHead :=
    retainedOrderedFixedEightFigureNine_inheritedExtendedConnector_head?
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second
  have translatedSecondConnectorHead :
      (translatePolyline offset secondConnector).head? =
        some
          (Cell.add offset
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
              outputPlacement second.sourceClause second.generatedClause
              second.sourceLiteralIndex)) := by
    simpa [secondConnector, translatePolyline] using
      congrArg (Option.map (Cell.add offset)) secondConnectorHead
  have endpointsDifferent :
      firstLocalRoute.getLast? ≠
        (translatePolyline offset secondConnector).head? := by
    rw [firstLocalLast, translatedSecondConnectorHead]
    exact fun equal => sourcePortsDifferent (Option.some.inj equal)
  dsimp only
  exact
    retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_translatedInheritedSuffix_of_sourceGauge
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      first.generatedLiteralMember first.metadata first.metadataLookup
      first.metadataClause second relativeTranslate
      (by simpa [first.metadataSourceClause] using sourceGaugesEqual)
      (by simpa [firstLocalRoute, secondConnector, offset,
        clearanceSource, clearancePlacement, outputPlacement,
        clearanceWidth] using endpointsDifferent)

/-- The reverse cross pair follows from the preceding theorem at the negated
relative translation. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSuffix_strictlyAvoids_translatedInheritedLocal_of_sourceGaugesEqual
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
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          first.sourceClause first.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source))
        (first.sourceSlot clearanceWidth)
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex first.sourceLiteralIndex))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex)) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let reverseTranslate := Cell.neg relativeTranslate
  let offset := outputPlacement.translation relativeTranslate
  let reverseOffset := outputPlacement.translation reverseTranslate
  let firstSuffix :=
    PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (PositionedPeriodicCNF.clauseExitFanData
        first.sourceClause first.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source))
      (first.sourceSlot clearanceWidth)
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)
  let secondLocal :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      secondClauseIndex secondLiteralIndex
  have reverseSourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement second.sourceClause second.generatedClause =
        Cell.add reverseOffset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause) := by
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst sourceGaugesEqual
      simp [outputPlacement, clearanceSource, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd sourceGaugesEqual
      simp [outputPlacement, clearanceSource, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
  have reverseOccurrencesDifferent :
      ((secondClauseIndex, secondLiteralIndex), (0, 0)) ≠
        ((firstClauseIndex, firstLiteralIndex), reverseTranslate) := by
    intro reverseEqual
    have clauseEqual : secondClauseIndex = firstClauseIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
        reverseEqual
    have literalEqual : secondLiteralIndex = firstLiteralIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
        reverseEqual
    have reverseTranslateZero : (0, 0) = reverseTranslate :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
        reverseEqual
    have relativeTranslateZero : relativeTranslate = (0, 0) := by
      rcases relativeTranslate with ⟨translateX, translateY⟩
      simp [reverseTranslate, Cell.neg, Cell.sub]
        at reverseTranslateZero ⊢
      exact ⟨reverseTranslateZero.1,
        reverseTranslateZero.2⟩
    apply generatedOccurrencesDifferent
    simp [clauseEqual, literalEqual, relativeTranslateZero]
  have backwards :=
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second first reverseTranslate
      (by simpa [outputPlacement, reverseOffset,
        clearanceSource, clearancePlacement] using
        reverseSourceGaugesEqual)
      reverseOccurrencesDifferent
  have shifted := backwards.symm.translatePolyline offset
  have shiftCancel : Cell.add reverseOffset offset = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseOffset, offset, reverseTranslate,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  simpa [firstSuffix, secondLocal, outputPlacement,
    clearanceSource, clearancePlacement, clearanceWidth,
    offset, reverseOffset, reverseTranslate] using shifted

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

/-- The finite exit connectors of a distinct inherited pair are strictly
separated when their normalized source gauges agree. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedConnectors_strictlyAvoidEachOther_of_sourceGaugesEqual
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
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause)
          (first.sourceSlot clearanceWidth))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedRoute
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
  have sourceLiteralIndicesDifferent :=
    retainedOrderedFixedEightFigureNine_inheritedSourceLiteralIndicesDifferent_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
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
            (fanData.route secondSlot)) =
        translatePolyline firstOrigin
          (fanData.route secondSlot) := by
    unfold translatePolyline
    rw [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    apply Prod.ext <;>
      simp [firstOrigin, secondOrigin, offset, outputPlacement,
        sourceGaugesEqual, Cell.add] <;>
      ring
  have translatedStrict :=
    fanData.translatedRoutes_strictlyAvoidEachOther
      firstOrigin fanValid firstSlot secondSlot
      firstSlotActive secondSlotActive slotsDifferent
  dsimp only
  rw [show
    PositionedPeriodicCNF.clauseExitFanData
        second.sourceClause second.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source) = fanData by
      simp [fanData, sourceClausesEqual, sourceClauseIndicesEqual]]
  simp only [
    PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedRoute]
  change
    RoutesStrictlyAvoidEachOther
      (translatePolyline firstOrigin (fanData.route firstSlot))
      (translatePolyline offset
        (translatePolyline secondOrigin (fanData.route secondSlot)))
  rw [translatedSecondConnector]
  exact translatedStrict

/-- Unequal retained source gauges put the two finite inherited connectors
in disjoint radius-`73` neighborhoods.  Although Figure 9 itself only adds
factor `144`, every gauge of the retained fixed-eight source was already
refined by factor eight, so distinct connector origins are separated on a
factor-`1152` lattice. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedConnectors_strictlyAvoidEachOther_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
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
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause)
          (first.sourceSlot clearanceWidth))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            (second.sourceSlot clearanceWidth))) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let firstData :=
    PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let secondData :=
    PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let firstSlot := first.sourceSlot clearanceWidth
  let secondSlot := second.sourceSlot clearanceWidth
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement first.sourceClause first.generatedClause
  let secondBaseOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement second.sourceClause second.generatedClause
  let secondOrigin := Cell.add offset secondBaseOrigin
  have firstClauseNonempty : first.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx first.sourceLiteralMember)
  have secondClauseNonempty : second.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx second.sourceLiteralMember)
  have firstValid : firstData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.sourceClauseMember firstClauseNonempty
  have secondValid : secondData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second.sourceClauseMember secondClauseNonempty
  have firstCount :
      firstData.count = first.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr firstClauseNonempty)
      (first.sourceClause_width clearanceWidth)
  have secondCount :
      secondData.count = second.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr secondClauseNonempty)
      (second.sourceClause_width clearanceWidth)
  have firstActive : firstData.SlotActive firstSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [firstCount]
    exact first.sourceLiteralIndex_lt
  have secondActive : secondData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [secondCount]
    exact second.sourceLiteralIndex_lt
  rcases exists_clockwiseClause_of_clearanceClause_mem
      first.sourceClauseMember with
    ⟨firstClockwiseClause, firstClockwiseMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨secondClockwiseClause, secondClockwiseMember, secondSourceEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source firstClockwiseMember first.generatedClause with
    ⟨firstBaseCenter, firstCenterEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source secondClockwiseMember second.generatedClause with
    ⟨secondBaseCenter, secondCenterEq⟩
  rcases
      retainedOrderedFixedEight_translation_eq_scale_refinement
        source relativeTranslate with
    ⟨baseOffset, offsetCenterEq⟩
  let connectorScale : Nat := 1152
  have firstOriginEq :
      firstOrigin = Cell.scale connectorScale firstBaseCenter := by
    dsimp only [firstOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      firstSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor)
            (firstClockwiseClause.scale
              retainedFigureNineSourceClearanceFactor)
            first.generatedClause) = _
    rw [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      firstCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale,
        Cell.scale] <;>
      ring
  have secondOriginEq :
      secondOrigin =
        Cell.scale connectorScale
          (Cell.add baseOffset secondBaseCenter) := by
    dsimp only [secondOrigin, secondBaseOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      secondSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (Cell.add
            ((clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor).translation
                relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (clockwisePlacement.scale
                retainedFigureNineSourceClearanceFactor)
              (secondClockwiseClause.scale
                retainedFigureNineSourceClearanceFactor)
              second.generatedClause)) = _
    rw [PeriodicVariablePlacement.translation_scale,
      PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      offsetCenterEq, secondCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale,
        Cell.add, Cell.scale] <;>
      ring
  have baseCentersDifferent :
      firstBaseCenter ≠ Cell.add baseOffset secondBaseCenter := by
    intro baseCentersEqual
    apply sourceGaugesNe
    change firstOrigin = secondOrigin
    rw [firstOriginEq, secondOriginEq, baseCentersEqual]
  have connectorsStrict :=
    routesStrictlyAvoidEachOther_of_distinct_scaledCoordinateNeighborhoods
      (firstCenter := firstBaseCenter)
      (secondCenter := Cell.add baseOffset secondBaseCenter)
      (factor := connectorScale) (radius := 73)
      baseCentersDifferent (by norm_num [connectorScale])
      (by norm_num [connectorScale])
      (fun point pointMember => by
        simpa only [firstOriginEq] using
          firstData.translatedRoute_points_within_sourceNeighborhood
            firstOrigin firstValid firstSlot firstActive pointMember)
      (fun point pointMember => by
        simpa only [secondOriginEq] using
          secondData.translatedRoute_points_within_sourceNeighborhood
            secondOrigin secondValid secondSlot secondActive pointMember)
  have translatedSecondConnector :
      translatePolyline offset
          (secondData.translatedRoute secondBaseOrigin secondSlot) =
        secondData.translatedRoute secondOrigin secondSlot := by
    simp [PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedRoute,
      translatePolyline_add, secondOrigin, Cell.add, add_comm]
  dsimp only [clearanceWidth, outputPlacement, clearancePlacement]
  change
    RoutesStrictlyAvoidEachOther
      (firstData.translatedRoute firstOrigin firstSlot)
      (translatePolyline offset
        (secondData.translatedRoute secondBaseOrigin secondSlot))
  simpa only [translatedSecondConnector] using connectorsStrict

/-- At unequal retained source gauges, the first finite connector strictly
avoids the translated radially extended second connector.  Both lie in
radius-`144` neighborhoods of distinct points of the factor-`1152` source
lattice. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
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
        ).translatedRoute
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
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let firstData :=
    PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let secondData :=
    PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let firstSlot := first.sourceSlot clearanceWidth
  let secondSlot := second.sourceSlot clearanceWidth
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement first.sourceClause first.generatedClause
  let secondBaseOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement second.sourceClause second.generatedClause
  let secondOrigin := Cell.add offset secondBaseOrigin
  have firstClauseNonempty : first.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx first.sourceLiteralMember)
  have secondClauseNonempty : second.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx second.sourceLiteralMember)
  have firstValid : firstData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.sourceClauseMember firstClauseNonempty
  have secondValid : secondData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second.sourceClauseMember secondClauseNonempty
  have firstCount :
      firstData.count = first.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr firstClauseNonempty)
      (first.sourceClause_width clearanceWidth)
  have secondCount :
      secondData.count = second.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr secondClauseNonempty)
      (second.sourceClause_width clearanceWidth)
  have firstActive : firstData.SlotActive firstSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [firstCount]
    exact first.sourceLiteralIndex_lt
  have secondActive : secondData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [secondCount]
    exact second.sourceLiteralIndex_lt
  rcases exists_clockwiseClause_of_clearanceClause_mem
      first.sourceClauseMember with
    ⟨firstClockwiseClause, firstClockwiseMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨secondClockwiseClause, secondClockwiseMember, secondSourceEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source firstClockwiseMember first.generatedClause with
    ⟨firstBaseCenter, firstCenterEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source secondClockwiseMember second.generatedClause with
    ⟨secondBaseCenter, secondCenterEq⟩
  rcases
      retainedOrderedFixedEight_translation_eq_scale_refinement
        source relativeTranslate with
    ⟨baseOffset, offsetCenterEq⟩
  let connectorScale : Nat := 1152
  have firstOriginEq :
      firstOrigin = Cell.scale connectorScale firstBaseCenter := by
    dsimp only [firstOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      firstSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor)
            (firstClockwiseClause.scale
              retainedFigureNineSourceClearanceFactor)
            first.generatedClause) = _
    rw [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      firstCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale,
        Cell.scale] <;>
      ring
  have secondOriginEq :
      secondOrigin =
        Cell.scale connectorScale
          (Cell.add baseOffset secondBaseCenter) := by
    dsimp only [secondOrigin, secondBaseOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      secondSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (Cell.add
            ((clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor).translation
                relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (clockwisePlacement.scale
                retainedFigureNineSourceClearanceFactor)
              (secondClockwiseClause.scale
                retainedFigureNineSourceClearanceFactor)
              second.generatedClause)) = _
    rw [PeriodicVariablePlacement.translation_scale,
      PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      offsetCenterEq, secondCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale,
        Cell.add, Cell.scale] <;>
      ring
  have baseCentersDifferent :
      firstBaseCenter ≠ Cell.add baseOffset secondBaseCenter := by
    intro baseCentersEqual
    apply sourceGaugesNe
    change firstOrigin = secondOrigin
    rw [firstOriginEq, secondOriginEq, baseCentersEqual]
  have connectorExtendedStrict :=
    routesStrictlyAvoidEachOther_of_distinct_scaledCoordinateNeighborhoods
      (firstCenter := firstBaseCenter)
      (secondCenter := Cell.add baseOffset secondBaseCenter)
      (factor := connectorScale) (radius := 144)
      baseCentersDifferent (by norm_num [connectorScale])
      (by norm_num [connectorScale])
      (fun point pointMember => by
        have bounded :=
          firstData.translatedRoute_points_within_sourceNeighborhood
            firstOrigin firstValid firstSlot firstActive pointMember
        exact (firstOriginEq ▸ bounded).mono (by norm_num))
      (fun point pointMember => by
        simpa only [secondOriginEq] using
          secondData.translatedExtendedRoute_points_within_sourceNeighborhood
            secondOrigin secondValid secondSlot secondActive pointMember)
  have translatedSecondExtendedConnector :
      translatePolyline offset
          (secondData.translatedExtendedRoute secondBaseOrigin secondSlot) =
        secondData.translatedExtendedRoute secondOrigin secondSlot := by
    simp [PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedExtendedRoute,
      translatePolyline_add, secondOrigin, Cell.add, add_comm]
  dsimp only [clearanceWidth, outputPlacement, clearancePlacement]
  change
    RoutesStrictlyAvoidEachOther
      (firstData.translatedRoute firstOrigin firstSlot)
      (translatePolyline offset
        (secondData.translatedExtendedRoute secondBaseOrigin secondSlot))
  simpa only [translatedSecondExtendedConnector] using
    connectorExtendedStrict

/-- At unequal retained source gauges, an arbitrary normalized local route
strictly avoids the translated extended connector of an inherited incidence.
The radius-`72` local route and radius-`144` connector both lie around
distinct points of the factor-`1152` retained source lattice. -/
theorem
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ localClause.literals.zipIdx)
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            (second.sourceSlot clearanceWidth))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      localClauseIndex localLiteralIndex
  let secondData :=
    PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let secondSlot := second.sourceSlot clearanceWidth
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement localMetadata.sourceClause localClause
  let secondBaseOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement second.sourceClause second.generatedClause
  let secondOrigin := Cell.add offset secondBaseOrigin
  have secondClauseNonempty : second.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx second.sourceLiteralMember)
  have secondValid : secondData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second.sourceClauseMember secondClauseNonempty
  have secondCount :
      secondData.count = second.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr secondClauseNonempty)
      (second.sourceClause_width clearanceWidth)
  have secondActive : secondData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [secondCount]
    exact second.sourceLiteralIndex_lt
  have localBounded :
      ∀ point ∈ localRoute,
        PeriodicEightOccurrenceSplit.WithinCoordinateRadius 72
          firstOrigin point := by
    intro point pointMember
    have bounded :=
      normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
        clearanceSource clearancePlacement clearanceWidth
        localClauseMember localLiteralMember
        localMetadata localMetadataLookup point pointMember
    have firstOriginEqGauge :
        firstOrigin =
          Cell.scale
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              clearancePlacement localMetadata.sourceClause
              localClause) := by
      simpa [firstOrigin, outputPlacement, clearanceSource] using
        PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
          clearanceSource clearancePlacement localMetadata.sourceClause
          localClause
    rw [firstOriginEqGauge]
    exact bounded
  have localMetadataSourceClauseMember :
      (localMetadata.sourceClause, localMetadata.sourceClauseIndex) ∈
        clearanceSource.clauses.zipIdx := by
    rcases
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
          clearanceSource localClauseMember with
      ⟨actualMetadata, actualLookup, _actualClause,
        actualSourceMember, _actualEmbedded⟩
    have actualMetadataEq : actualMetadata = localMetadata := by
      apply Option.some.inj
      exact actualLookup.symm.trans localMetadataLookup
    simpa [actualMetadataEq] using actualSourceMember
  rcases exists_clockwiseClause_of_clearanceClause_mem
      localMetadataSourceClauseMember with
    ⟨firstClockwiseClause, firstClockwiseMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨secondClockwiseClause, secondClockwiseMember, secondSourceEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source firstClockwiseMember localClause with
    ⟨firstBaseCenter, firstCenterEq⟩
  rcases
      retainedOrderedFixedEight_localRouteSourceGaugeCenter_eq_scale_refinement
        source secondClockwiseMember second.generatedClause with
    ⟨secondBaseCenter, secondCenterEq⟩
  rcases
      retainedOrderedFixedEight_translation_eq_scale_refinement
        source relativeTranslate with
    ⟨baseOffset, offsetCenterEq⟩
  let connectorScale : Nat := 1152
  have firstOriginEq :
      firstOrigin = Cell.scale connectorScale firstBaseCenter := by
    dsimp only [firstOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      firstSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor)
            (firstClockwiseClause.scale
              retainedFigureNineSourceClearanceFactor)
            localClause) = _
    rw [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      firstCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale, Cell.scale] <;>
      ring
  have secondOriginEq :
      secondOrigin =
        Cell.scale connectorScale
          (Cell.add baseOffset secondBaseCenter) := by
    dsimp only [secondOrigin, secondBaseOrigin]
    rw [PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      secondSourceEq]
    change
      Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (Cell.add
            ((clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor).translation
                relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (clockwisePlacement.scale
                retainedFigureNineSourceClearanceFactor)
              (secondClockwiseClause.scale
                retainedFigureNineSourceClearanceFactor)
              second.generatedClause)) = _
    rw [PeriodicVariablePlacement.translation_scale,
      PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
      offsetCenterEq, secondCenterEq]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        retainedFigureNineSourceClearanceFactor,
        PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
        connectorScale, Cell.add, Cell.scale] <;>
      ring
  have baseCentersDifferent :
      firstBaseCenter ≠ Cell.add baseOffset secondBaseCenter := by
    intro baseCentersEqual
    apply sourceGaugesNe
    change firstOrigin = secondOrigin
    rw [firstOriginEq, secondOriginEq, baseCentersEqual]
  have localExtendedStrict :=
    routesStrictlyAvoidEachOther_of_distinct_scaledCoordinateNeighborhoods
      (firstCenter := firstBaseCenter)
      (secondCenter := Cell.add baseOffset secondBaseCenter)
      (factor := connectorScale) (radius := 144)
      baseCentersDifferent (by norm_num [connectorScale])
      (by norm_num [connectorScale])
      (fun point pointMember => by
        have bounded := localBounded point pointMember
        exact (firstOriginEq ▸ bounded).mono (by norm_num))
      (fun point pointMember => by
        simpa only [secondOriginEq] using
          secondData.translatedExtendedRoute_points_within_sourceNeighborhood
            secondOrigin secondValid secondSlot secondActive pointMember)
  have translatedSecondExtendedConnector :
      translatePolyline offset
          (secondData.translatedExtendedRoute secondBaseOrigin secondSlot) =
        secondData.translatedExtendedRoute secondOrigin secondSlot := by
    simp [PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedExtendedRoute,
      translatePolyline_add, secondOrigin, Cell.add, add_comm]
  dsimp only [clearanceWidth, outputPlacement, clearancePlacement]
  change
    RoutesStrictlyAvoidEachOther localRoute
      (translatePolyline offset
        (secondData.translatedExtendedRoute secondBaseOrigin secondSlot))
  simpa only [translatedSecondExtendedConnector] using localExtendedStrict

/-- The arbitrary-local unequal-gauge connector separation specialized to
the local route carried by a first inherited incidence. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            (second.sourceSlot clearanceWidth))) := by
  simpa only [first.metadataSourceClause] using
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      first.generatedLiteralMember first.metadata first.metadataLookup
      second relativeTranslate (by
        simpa only [first.metadataSourceClause] using sourceGaugesNe)

/-- Unequal normalized source gauges force any recovered incidence of the
local metadata source clause to differ from the translated inherited source
incidence. -/
private theorem
    localSourceOccurrenceDifferent_of_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localSourceClauseMember :
      (localMetadata.sourceClause, localMetadata.sourceClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (localSourceLiteralIndex : Nat)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    ((localMetadata.sourceClauseIndex, localSourceLiteralIndex), (0, 0)) ≠
      ((second.sourceClauseIndex, second.sourceLiteralIndex),
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          localMetadata.sourceClause second.sourceClause
          localClause second.generatedClause relativeTranslate) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let sourceRelativeTranslate :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
      localMetadata.sourceClause second.sourceClause
      localClause second.generatedClause relativeTranslate
  intro sourceOccurrencesEqual
  have sourceClauseIndexEqual :
      localMetadata.sourceClauseIndex = second.sourceClauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      sourceOccurrencesEqual
  have sourceRelativeTranslateZero :
      (0, 0) = sourceRelativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      sourceOccurrencesEqual
  have sourceClausesEqual :
      localMetadata.sourceClause = second.sourceClause := by
    apply value_eq_of_mem_zipIdx_same_index localSourceClauseMember
    simpa [sourceClauseIndexEqual] using second.sourceClauseMember
  have canonicalPositionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          clearancePlacement localMetadata.sourceClause =
        Cell.add
          (clearancePlacement.translation sourceRelativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            clearancePlacement second.sourceClause) := by
    rw [← sourceRelativeTranslateZero]
    simp [sourceClausesEqual,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale]
  have sourceCentersEqual :=
    (localRouteSourceGaugeCenter_eq_translated_iff
      clearancePlacement localMetadata.sourceClause second.sourceClause
      localClause second.generatedClause relativeTranslate).mpr
        (by simpa [sourceRelativeTranslate] using canonicalPositionsEqual)
  apply sourceGaugesNe
  rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
    PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
  exact congrArg
    (Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale)
    sourceCentersEqual

/-- Unequal normalized source gauges force distinct recovered source-route
occurrences after the inherited anchor change. -/
private theorem
    inheritedSourceOccurrencesDifferent_of_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    ((first.sourceClauseIndex, first.sourceLiteralIndex), (0, 0)) ≠
      ((second.sourceClauseIndex, second.sourceLiteralIndex),
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          first.sourceClause second.sourceClause
          first.generatedClause second.generatedClause
          relativeTranslate) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let sourceRelativeTranslate :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
      first.sourceClause second.sourceClause
      first.generatedClause second.generatedClause
      relativeTranslate
  intro sourceOccurrencesEqual
  have sourceClauseIndexEqual :
      first.sourceClauseIndex = second.sourceClauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      sourceOccurrencesEqual
  have sourceRelativeTranslateZero :
      (0, 0) = sourceRelativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      sourceOccurrencesEqual
  have sourceClausesEqual : first.sourceClause = second.sourceClause := by
    apply value_eq_of_mem_zipIdx_same_index first.sourceClauseMember
    simpa [sourceClauseIndexEqual] using second.sourceClauseMember
  have canonicalPositionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          clearancePlacement first.sourceClause =
        Cell.add
          (clearancePlacement.translation sourceRelativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            clearancePlacement second.sourceClause) := by
    rw [← sourceRelativeTranslateZero]
    simp [sourceClausesEqual,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale]
  have sourceCentersEqual :=
    (localRouteSourceGaugeCenter_eq_translated_iff
      clearancePlacement first.sourceClause second.sourceClause
      first.generatedClause second.generatedClause relativeTranslate).mpr
        (by simpa [sourceRelativeTranslate] using canonicalPositionsEqual)
  apply sourceGaugesNe
  rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
    PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
  exact congrArg
    (Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale)
    sourceCentersEqual

/-- At unequal retained source gauges, the first inherited connector
strictly avoids the translated transformed source tail of the second
incidence.  The finite radial part uses factor-`1152` neighborhood
separation; the far part descends to endpoint-aware separation of the
clockwise source routes and is then transported through the Figure 9
refinement. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
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
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause)
          (first.sourceSlot clearanceWidth))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex)).tail)) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let sourceRelativeTranslate :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
      first.sourceClause second.sourceClause
      first.generatedClause second.generatedClause
      relativeTranslate
  let sourceOffset :=
    clockwisePlacement.translation sourceRelativeTranslate
  let reverseSourceOffset := Cell.neg sourceOffset
  let firstData :=
    PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let secondData :=
    PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let firstSlot := first.sourceSlot clearanceWidth
  let secondSlot := second.sourceSlot clearanceWidth
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement first.sourceClause first.generatedClause
  let firstConnector :=
    firstData.translatedRoute firstOrigin firstSlot
  let secondClearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  rcases exists_clockwiseClause_of_clearanceClause_mem
      first.sourceClauseMember with
    ⟨firstClockwiseClause, firstClockwiseMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨secondClockwiseClause, secondClockwiseMember, secondSourceEq⟩
  have sourceRelativeTranslateEq :
      sourceRelativeTranslate =
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          firstClockwiseClause secondClockwiseClause
          first.generatedClause second.generatedClause
          relativeTranslate := by
    apply Prod.ext <;>
      simp [sourceRelativeTranslate, firstSourceEq, secondSourceEq,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        Cell.add, Cell.sub]
  have firstClockwiseLiteralMember :
      (first.sourceLiteral, first.sourceLiteralIndex) ∈
        firstClockwiseClause.literals.zipIdx := by
    simpa [firstSourceEq] using first.sourceLiteralMember
  have secondClockwiseLiteralMember :
      (second.sourceLiteral, second.sourceLiteralIndex) ∈
        secondClockwiseClause.literals.zipIdx := by
    simpa [secondSourceEq] using second.sourceLiteralMember
  let firstOriginalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source first.sourceClauseIndex first.sourceLiteralIndex
  let secondOriginalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  have firstOriginalValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClockwiseMember
      firstClockwiseLiteralMember
  have secondOriginalValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have secondOriginalLength : 2 ≤ secondOriginalRoute.length :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have secondOriginalUnitSteps :
      secondOriginalRoute.IsChain AxisDirection.IsUnitAxisStep :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have sourceOccurrenceDifferent :=
    inheritedSourceOccurrencesDifferent_of_sourceGaugesNe
      source first second relativeTranslate sourceGaugesNe
  have sourceAvoid :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).coordinate
      firstClockwiseClause first.sourceClauseIndex firstClockwiseMember
      first.sourceLiteral first.sourceLiteralIndex
      firstClockwiseLiteralMember
      secondClockwiseClause second.sourceClauseIndex secondClockwiseMember
      second.sourceLiteral second.sourceLiteralIndex
      secondClockwiseLiteralMember
      sourceRelativeTranslate
      (by simpa [sourceRelativeTranslate] using sourceOccurrenceDifferent)
  have sourceHeadsDifferent :
      PositionedPeriodicCNF.canonicalClausePosition
          clockwisePlacement firstClockwiseClause ≠
        Cell.add sourceOffset
          (PositionedPeriodicCNF.canonicalClausePosition
            clockwisePlacement secondClockwiseClause) := by
    intro sourceHeadsEqual
    have clockwiseCentersEqual :=
      (localRouteSourceGaugeCenter_eq_translated_iff
        clockwisePlacement firstClockwiseClause secondClockwiseClause
        first.generatedClause second.generatedClause
        relativeTranslate).mpr
          (by simpa [sourceOffset, sourceRelativeTranslateEq] using
            sourceHeadsEqual)
    have clearanceCentersEqual :
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            clearancePlacement first.sourceClause first.generatedClause =
          Cell.add (clearancePlacement.translation relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              clearancePlacement second.sourceClause
              second.generatedClause) := by
      rw [firstSourceEq, secondSourceEq]
      change
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor)
            (firstClockwiseClause.scale
              retainedFigureNineSourceClearanceFactor)
            first.generatedClause =
          Cell.add
            ((clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor).translation
                relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (clockwisePlacement.scale
                retainedFigureNineSourceClearanceFactor)
              (secondClockwiseClause.scale
                retainedFigureNineSourceClearanceFactor)
              second.generatedClause)
      rw [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
        PeriodicVariablePlacement.translation_scale,
        clockwiseCentersEqual]
      apply Prod.ext <;>
        simp [Cell.add, Cell.scale] <;>
        ring
    apply sourceGaugesNe
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
    exact congrArg
      (Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale)
      clearanceCentersEqual
  have sourceHeadDifferentSecondLast :
      PositionedPeriodicCNF.canonicalClausePosition
          clockwisePlacement firstClockwiseClause ≠
        Cell.add sourceOffset
          (PositionedPeriodicCNF.canonicalLiteralPosition
            clockwisePlacement secondClockwiseClause
            second.sourceLiteral) := by
    simpa [sourceOffset, sourceRelativeTranslateEq] using
      retainedOrderedFixedEightCanonicalClausePosition_ne_translatedLiteralPosition
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClockwiseMember secondClockwiseMember
        secondClockwiseLiteralMember sourceRelativeTranslate
  let firstHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      clockwisePlacement firstClockwiseClause
  let secondHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      clockwisePlacement secondClockwiseClause
  let secondLast :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      clockwisePlacement secondClockwiseClause second.sourceLiteral
  let shiftedFirstHead := Cell.add reverseSourceOffset firstHead
  have shiftedSourceAvoid :
      RoutesAvoidEachOther
        (translatePolyline reverseSourceOffset firstOriginalRoute)
        secondOriginalRoute := by
    have shifted := sourceAvoid.translate reverseSourceOffset
    change RoutesAvoidEachOther
      (translatePolyline reverseSourceOffset firstOriginalRoute)
      (translatePolyline reverseSourceOffset
        (translatePolyline sourceOffset secondOriginalRoute)) at shifted
    have offsetsCancel :
        Cell.add sourceOffset reverseSourceOffset = (0, 0) := by
      rcases sourceOffset with ⟨sourceOffsetX, sourceOffsetY⟩
      simp [reverseSourceOffset, Cell.neg, Cell.add, Cell.sub]
    rw [translatePolyline_add, offsetsCancel,
      translatePolyline_zero] at shifted
    simpa [firstOriginalRoute, secondOriginalRoute,
      sourceOffset, reverseSourceOffset] using shifted
  have shiftedFirstHeadLookup :
      (translatePolyline reverseSourceOffset firstOriginalRoute).head? =
        some shiftedFirstHead := by
    simpa [translatePolyline, shiftedFirstHead, firstHead,
      firstOriginalRoute] using
      congrArg (Option.map (Cell.add reverseSourceOffset))
        firstOriginalValid.1
  have secondHeadLookup :
      secondOriginalRoute.head? = some secondHead := by
    simpa [secondOriginalRoute, secondHead] using
      secondOriginalValid.1
  have secondLastLookup :
      secondOriginalRoute.getLast? = some secondLast := by
    simpa [secondOriginalRoute, secondLast] using
      secondOriginalValid.2.1
  have shiftedHeadsDifferent : shiftedFirstHead ≠ secondHead := by
    intro shiftedEqual
    apply sourceHeadsDifferent
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst shiftedEqual
      simp [shiftedFirstHead, firstHead, secondHead, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
    · have coordinateEqual := congrArg Prod.snd shiftedEqual
      simp [shiftedFirstHead, firstHead, secondHead, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
  have shiftedHeadDifferentSecondLast :
      shiftedFirstHead ≠ secondLast := by
    intro shiftedEqual
    apply sourceHeadDifferentSecondLast
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst shiftedEqual
      simp [shiftedFirstHead, firstHead, secondLast, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
    · have coordinateEqual := congrArg Prod.snd shiftedEqual
      simp [shiftedFirstHead, firstHead, secondLast, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
  have secondAvoidsShiftedFirstHead :=
    shiftedSourceAvoid.second_avoids_first_head_of_endpoints_ne
      shiftedFirstHeadLookup secondHeadLookup secondLastLookup
      shiftedHeadsDifferent shiftedHeadDifferentSecondLast
  have firstClauseNonempty : first.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx first.sourceLiteralMember)
  have secondClauseNonempty : second.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx second.sourceLiteralMember)
  have firstFanValid : firstData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.sourceClauseMember firstClauseNonempty
  have secondFanValid : secondData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second.sourceClauseMember secondClauseNonempty
  have firstCount :
      firstData.count = first.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr firstClauseNonempty)
      (first.sourceClause_width clearanceWidth)
  have secondCount :
      secondData.count = second.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr secondClauseNonempty)
      (second.sourceClause_width clearanceWidth)
  have firstSlotActive : firstData.SlotActive firstSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [firstCount]
    exact first.sourceLiteralIndex_lt
  have secondSlotActive : secondData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [secondCount]
    exact second.sourceLiteralIndex_lt
  have firstConnectorOrthogonal : OrthogonalPolyline firstConnector :=
    firstData.translatedRoute_orthogonal
      firstOrigin firstFanValid firstSlot firstSlotActive
  have extendedAvoid :
      RoutesStrictlyAvoidEachOther firstConnector
        (translatePolyline offset
          (secondData.translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            secondSlot)) := by
    simpa [firstConnector, firstData, secondData, firstOrigin,
      firstSlot, secondSlot, outputPlacement, clearancePlacement,
      clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate sourceGaugesNe
  cases secondOriginalRouteEq : secondOriginalRoute with
  | nil => simp [secondOriginalRouteEq] at secondOriginalLength
  | cons firstPoint remaining =>
      cases remaining with
      | nil => simp [secondOriginalRouteEq] at secondOriginalLength
      | cons secondPoint rest =>
          have firstUnit :
              AxisDirection.IsUnitAxisStep firstPoint secondPoint :=
            (List.isChain_cons_cons.mp
              (secondOriginalRouteEq ▸ secondOriginalUnitSteps)).1
          have clearanceRouteEq :
              secondClearanceRoute =
                AxisDirection.unitSubdividePolyline
                  (scalePolyline 2
                    (firstPoint :: secondPoint :: rest)) := by
            simpa [secondClearanceRoute, secondOriginalRoute,
              secondOriginalRouteEq,
              retainedFigureNineSourceClearanceFactor] using
              retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember
          have firstPointEq :
              firstPoint = secondHead := by
            apply Option.some.inj
            exact (by simpa [secondOriginalRoute,
              secondOriginalRouteEq] using secondOriginalValid.1)
          have scaledHead :
              Cell.scale 2 firstPoint =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement second.sourceClause := by
            rw [firstPointEq, secondSourceEq]
            simpa [secondHead, clearancePlacement, clockwisePlacement,
              retainedFigureNineClearancePlacement] using
              PositionedPeriodicCNF.canonicalClausePosition_scale
                retainedFigureNineSourceClearanceFactor
                clockwisePlacement secondClockwiseClause
          have directionBase :
              AxisDirection.polylineFirstDirection
                  secondClearanceRoute =
                AxisDirection.between firstPoint secondPoint := by
            rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty second.sourceClauseMember
              second.sourceLiteralMember]
            simp [secondOriginalRoute, secondOriginalRouteEq]
          have directionEq :
              secondData.direction secondSlot =
                AxisDirection.between firstPoint secondPoint := by
            simpa only [secondData,
              PositionedPeriodicCNF.clauseExitFanData, secondSlot,
              PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
              using directionBase
          let secondShift :=
            PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause
          let farShift := Cell.add offset secondShift
          have connectorCenterEq :
              firstOrigin =
                Cell.add farShift
                  (Cell.scale 144 shiftedFirstHead) := by
            apply Prod.ext <;>
              simp [firstOrigin, farShift, secondShift,
                shiftedFirstHead, firstHead,
                reverseSourceOffset, sourceOffset,
                sourceRelativeTranslate, offset,
                outputPlacement, clearancePlacement,
                clockwisePlacement,
                retainedFigureNineClearancePlacement,
                PeriodicVariablePlacement.scale,
                firstSourceEq, secondSourceEq,
                PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
                PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
                PeriodicOneInThreeNoUnitsPositioned.placement,
                PeriodicOneInThreePositioned.placement,
                PositionedPeriodicCNF.canonicalClausePosition,
                PeriodicVariablePlacement.translation,
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
                PlanarOneInThree.gadgetScale,
                PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
                retainedFigureNineSourceClearanceFactor,
                Cell.neg, Cell.add, Cell.sub, Cell.scale] <;>
              ring
          have connectorBounded :
              ∀ point ∈ firstConnector,
                PeriodicEightOccurrenceSplit.WithinCoordinateRadius 73
                  (Cell.add farShift
                    (Cell.scale 144 shiftedFirstHead)) point := by
            intro point pointMember
            rw [← connectorCenterEq]
            exact
              firstData.translatedRoute_points_within_sourceNeighborhood
                firstOrigin firstFanValid firstSlot firstSlotActive
                pointMember
          have secondTailOrthogonal :
              OrthogonalPolyline (secondPoint :: rest) := by
            have originalOrthogonal :
                OrthogonalPolyline secondOriginalRoute := by
              simpa [secondOriginalRoute] using secondOriginalValid.2.2
            exact (List.isChain_cons_cons.mp
              (secondOriginalRouteEq ▸ originalOrthogonal)).2
          have secondTailPointsAvoid :
              ∀ point ∈ secondPoint :: rest,
                point ≠ shiftedFirstHead := by
            intro point pointMember
            exact secondAvoidsShiftedFirstHead.1 point
              (by
                rw [secondOriginalRouteEq]
                exact List.mem_cons_of_mem firstPoint pointMember)
          have secondTailSegmentsAvoid :
              ∀ segment ∈ gridPolylineSegments (secondPoint :: rest),
                segment.IsAxisAligned →
                  ¬segment.Contains shiftedFirstHead := by
            intro segment segmentMember _aligned
            exact secondAvoidsShiftedFirstHead.2 segment
              (by
                rw [secondOriginalRouteEq]
                apply gridPolylineSegments_tail_subset
                exact segmentMember)
          have farTailAvoidBase :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail_of_avoidedCenter
              farShift 73 (by norm_num) secondTailOrthogonal
              secondTailPointsAvoid secondTailSegmentsAvoid
              firstConnectorOrthogonal connectorBounded
          have farTailAvoid :
              RoutesStrictlyAvoidEachOther firstConnector
                (translatePolyline offset
                  (translatePolyline secondShift
                    (scalePolyline
                      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                      (AxisDirection.unitSubdividePolyline
                        (scalePolyline 2
                          (secondPoint :: rest)))))) := by
            simpa [farShift, translatePolyline_add, Cell.add, add_comm] using
              farTailAvoidBase
          have strictSuffix :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translated_fanInheritedRouteSuffix_of_extended_of_farTail
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause secondData secondSlot
              firstPoint secondPoint rest firstConnector offset
              secondFanValid secondSlotActive firstUnit scaledHead directionEq
              extendedAvoid farTailAvoid
          have secondClearanceHead :
              secondClearanceRoute.head? =
                some
                  (PositionedPeriodicCNF.canonicalClausePosition
                    clearancePlacement second.sourceClause) := by
            simpa [secondClearanceRoute, clearancePlacement] using
              (retainedFigureNineClearanceIncidenceRoutes_valid
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember).1
          have secondClearanceTailNonempty :
              ∃ sourceExit,
                secondClearanceRoute.tail.head? = some sourceExit := by
            simpa [secondClearanceRoute] using
              retainedFigureNineClearanceIncidenceRoutes_exits
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember
          have secondClearanceUnitSteps :
              secondClearanceRoute.IsChain
                AxisDirection.IsUnitAxisStep := by
            simpa [secondClearanceRoute] using
              retainedFigureNineClearanceIncidenceRoutes_unitSteps
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember
          have clearanceDirectionEq :
              secondData.direction secondSlot =
                AxisDirection.polylineFirstDirection
                  secondClearanceRoute := by
            exact directionEq.trans directionBase.symm
          have strictTail :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedInheritedSourceRouteTail_of_fanInheritedRouteSuffix_of_sourceRoute_eq
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause secondData secondSlot
              secondClearanceRoute
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (firstPoint :: secondPoint :: rest)))
              firstConnector offset clearanceRouteEq
              secondFanValid secondSlotActive clearanceDirectionEq
              secondClearanceHead secondClearanceTailNonempty
              secondClearanceUnitSteps strictSuffix
          dsimp only [clearanceWidth, outputPlacement,
            clearancePlacement]
          change RoutesStrictlyAvoidEachOther firstConnector
            (translatePolyline offset
              ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
                outputPlacement clearancePlacement second.sourceClause
                second.generatedClause secondClearanceRoute).tail))
          exact strictTail

/-- At unequal retained source gauges, an arbitrary normalized local route
strictly avoids the translated inherited suffix of the second incidence.
The near field uses factor-`1152` neighborhood separation; the far field
selects any incidence of the nonempty local metadata source clause and
descends to endpoint-aware separation of the clockwise source routes. -/
theorem
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ localClause.literals.zipIdx)
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex))) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let sourceRelativeTranslate :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
      localMetadata.sourceClause second.sourceClause
      localClause second.generatedClause
      relativeTranslate
  let sourceOffset :=
    clockwisePlacement.translation sourceRelativeTranslate
  let reverseSourceOffset := Cell.neg sourceOffset
  let secondData :=
    PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let secondSlot := second.sourceSlot clearanceWidth
  let firstOrigin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement localMetadata.sourceClause localClause
  let firstLocalRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement localClauseIndex localLiteralIndex
  let secondClearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  have localMetadataSourceClauseMember :
      (localMetadata.sourceClause, localMetadata.sourceClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx := by
    rcases
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
          (retainedFigureNineClearancePositionedFormula source)
          localClauseMember with
      ⟨actualMetadata, actualLookup, _actualClause,
        actualSourceMember, _actualEmbedded⟩
    have actualMetadataEq : actualMetadata = localMetadata := by
      apply Option.some.inj
      exact actualLookup.symm.trans localMetadataLookup
    simpa [actualMetadataEq] using actualSourceMember
  have localSourceClauseNonempty :
      localMetadata.sourceClause.literals ≠ [] :=
    retainedFigureNineClearancePositionedFormula_clausesNonempty
      source sourceClausesNonempty localMetadata.sourceClause
      (List.fst_mem_of_mem_zipIdx localMetadataSourceClauseMember)
  rcases List.exists_cons_of_ne_nil localSourceClauseNonempty with
    ⟨firstSourceLiteral, firstSourceRest, localSourceLiteralsEq⟩
  have localSourceLiteralMember :
      (firstSourceLiteral, 0) ∈
        localMetadata.sourceClause.literals.zipIdx := by
    rw [localSourceLiteralsEq]
    simp
  rcases exists_clockwiseClause_of_clearanceClause_mem
      localMetadataSourceClauseMember with
    ⟨firstClockwiseClause, firstClockwiseMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨secondClockwiseClause, secondClockwiseMember, secondSourceEq⟩
  have sourceRelativeTranslateEq :
      sourceRelativeTranslate =
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          firstClockwiseClause secondClockwiseClause
          localClause second.generatedClause
          relativeTranslate := by
    apply Prod.ext <;>
      simp [sourceRelativeTranslate, firstSourceEq, secondSourceEq,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        Cell.add, Cell.sub]
  have firstClockwiseLiteralMember :
      (firstSourceLiteral, 0) ∈
        firstClockwiseClause.literals.zipIdx := by
    simpa [firstSourceEq] using localSourceLiteralMember
  have secondClockwiseLiteralMember :
      (second.sourceLiteral, second.sourceLiteralIndex) ∈
        secondClockwiseClause.literals.zipIdx := by
    simpa [secondSourceEq] using second.sourceLiteralMember
  let firstOriginalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source localMetadata.sourceClauseIndex 0
  let secondOriginalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  have firstOriginalValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClockwiseMember
      firstClockwiseLiteralMember
  have secondOriginalValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have secondOriginalLength : 2 ≤ secondOriginalRoute.length :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have secondOriginalUnitSteps :
      secondOriginalRoute.IsChain AxisDirection.IsUnitAxisStep :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClockwiseMember
      secondClockwiseLiteralMember
  have sourceOccurrenceDifferent :=
    localSourceOccurrenceDifferent_of_sourceGaugesNe
      source localMetadata localMetadataSourceClauseMember 0
      second relativeTranslate sourceGaugesNe
  have sourceAvoid :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).coordinate
      firstClockwiseClause localMetadata.sourceClauseIndex firstClockwiseMember
      firstSourceLiteral 0
      firstClockwiseLiteralMember
      secondClockwiseClause second.sourceClauseIndex secondClockwiseMember
      second.sourceLiteral second.sourceLiteralIndex
      secondClockwiseLiteralMember
      sourceRelativeTranslate
      (by simpa [sourceRelativeTranslate] using sourceOccurrenceDifferent)
  have sourceHeadsDifferent :
      PositionedPeriodicCNF.canonicalClausePosition
          clockwisePlacement firstClockwiseClause ≠
        Cell.add sourceOffset
          (PositionedPeriodicCNF.canonicalClausePosition
            clockwisePlacement secondClockwiseClause) := by
    intro sourceHeadsEqual
    have clockwiseCentersEqual :=
      (localRouteSourceGaugeCenter_eq_translated_iff
        clockwisePlacement firstClockwiseClause secondClockwiseClause
        localClause second.generatedClause
        relativeTranslate).mpr
          (by simpa [sourceOffset, sourceRelativeTranslateEq] using
            sourceHeadsEqual)
    have clearanceCentersEqual :
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            clearancePlacement localMetadata.sourceClause localClause =
          Cell.add (clearancePlacement.translation relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              clearancePlacement second.sourceClause
              second.generatedClause) := by
      rw [firstSourceEq, secondSourceEq]
      change
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor)
            (firstClockwiseClause.scale
              retainedFigureNineSourceClearanceFactor)
            localClause =
          Cell.add
            ((clockwisePlacement.scale
              retainedFigureNineSourceClearanceFactor).translation
                relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (clockwisePlacement.scale
                retainedFigureNineSourceClearanceFactor)
              (secondClockwiseClause.scale
                retainedFigureNineSourceClearanceFactor)
              second.generatedClause)
      rw [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter_scale,
        PeriodicVariablePlacement.translation_scale,
        clockwiseCentersEqual]
      apply Prod.ext <;>
        simp [Cell.add, Cell.scale] <;>
        ring
    apply sourceGaugesNe
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter,
      PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
    exact congrArg
      (Cell.scale PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale)
      clearanceCentersEqual
  have sourceHeadDifferentSecondLast :
      PositionedPeriodicCNF.canonicalClausePosition
          clockwisePlacement firstClockwiseClause ≠
        Cell.add sourceOffset
          (PositionedPeriodicCNF.canonicalLiteralPosition
            clockwisePlacement secondClockwiseClause
            second.sourceLiteral) := by
    simpa [sourceOffset, sourceRelativeTranslateEq] using
      retainedOrderedFixedEightCanonicalClausePosition_ne_translatedLiteralPosition
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClockwiseMember secondClockwiseMember
        secondClockwiseLiteralMember sourceRelativeTranslate
  let firstHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      clockwisePlacement firstClockwiseClause
  let secondHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      clockwisePlacement secondClockwiseClause
  let secondLast :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      clockwisePlacement secondClockwiseClause second.sourceLiteral
  let shiftedFirstHead := Cell.add reverseSourceOffset firstHead
  have shiftedSourceAvoid :
      RoutesAvoidEachOther
        (translatePolyline reverseSourceOffset firstOriginalRoute)
        secondOriginalRoute := by
    have shifted := sourceAvoid.translate reverseSourceOffset
    change RoutesAvoidEachOther
      (translatePolyline reverseSourceOffset firstOriginalRoute)
      (translatePolyline reverseSourceOffset
        (translatePolyline sourceOffset secondOriginalRoute)) at shifted
    have offsetsCancel :
        Cell.add sourceOffset reverseSourceOffset = (0, 0) := by
      rcases sourceOffset with ⟨sourceOffsetX, sourceOffsetY⟩
      simp [reverseSourceOffset, Cell.neg, Cell.add, Cell.sub]
    rw [translatePolyline_add, offsetsCancel,
      translatePolyline_zero] at shifted
    simpa [firstOriginalRoute, secondOriginalRoute,
      sourceOffset, reverseSourceOffset] using shifted
  have shiftedFirstHeadLookup :
      (translatePolyline reverseSourceOffset firstOriginalRoute).head? =
        some shiftedFirstHead := by
    simpa [translatePolyline, shiftedFirstHead, firstHead,
      firstOriginalRoute] using
      congrArg (Option.map (Cell.add reverseSourceOffset))
        firstOriginalValid.1
  have secondHeadLookup :
      secondOriginalRoute.head? = some secondHead := by
    simpa [secondOriginalRoute, secondHead] using
      secondOriginalValid.1
  have secondLastLookup :
      secondOriginalRoute.getLast? = some secondLast := by
    simpa [secondOriginalRoute, secondLast] using
      secondOriginalValid.2.1
  have shiftedHeadsDifferent : shiftedFirstHead ≠ secondHead := by
    intro shiftedEqual
    apply sourceHeadsDifferent
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst shiftedEqual
      simp [shiftedFirstHead, firstHead, secondHead, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
    · have coordinateEqual := congrArg Prod.snd shiftedEqual
      simp [shiftedFirstHead, firstHead, secondHead, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
  have shiftedHeadDifferentSecondLast :
      shiftedFirstHead ≠ secondLast := by
    intro shiftedEqual
    apply sourceHeadDifferentSecondLast
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst shiftedEqual
      simp [shiftedFirstHead, firstHead, secondLast, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
    · have coordinateEqual := congrArg Prod.snd shiftedEqual
      simp [shiftedFirstHead, firstHead, secondLast, reverseSourceOffset,
        Cell.neg, Cell.add, Cell.sub] at coordinateEqual ⊢
      omega
  have secondAvoidsShiftedFirstHead :=
    shiftedSourceAvoid.second_avoids_first_head_of_endpoints_ne
      shiftedFirstHeadLookup secondHeadLookup secondLastLookup
      shiftedHeadsDifferent shiftedHeadDifferentSecondLast
  have secondClauseNonempty : second.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx second.sourceLiteralMember)
  have secondFanValid : secondData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second.sourceClauseMember secondClauseNonempty
  have secondCount :
      secondData.count = second.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr secondClauseNonempty)
      (second.sourceClause_width clearanceWidth)
  have secondSlotActive : secondData.SlotActive secondSlot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [secondCount]
    exact second.sourceLiteralIndex_lt
  have firstLocalRouteOrthogonal : OrthogonalPolyline firstLocalRoute := by
    simpa [firstLocalRoute, clearancePlacement] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
        (retainedFigureNineClearancePositionedFormula source)
        clearancePlacement clearanceWidth
        (retainedFigureNineClearancePositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        localClauseMember localLiteralMember
  have firstLocalRouteBounded :
      ∀ point ∈ firstLocalRoute,
        PeriodicEightOccurrenceSplit.WithinCoordinateRadius 72
          firstOrigin point := by
    intro point pointMember
    have bounded :=
      normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
        (retainedFigureNineClearancePositionedFormula source)
        clearancePlacement clearanceWidth
        localClauseMember localLiteralMember
        localMetadata localMetadataLookup point pointMember
    have firstOriginEqGauge :
        firstOrigin =
          Cell.scale
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              clearancePlacement localMetadata.sourceClause
              localClause) := by
      simpa [firstOrigin, outputPlacement] using
        PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
          (retainedFigureNineClearancePositionedFormula source)
          clearancePlacement localMetadata.sourceClause localClause
    rw [firstOriginEqGauge]
    exact bounded
  have extendedAvoid :
      RoutesStrictlyAvoidEachOther firstLocalRoute
        (translatePolyline offset
          (secondData.translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              outputPlacement second.sourceClause second.generatedClause)
            secondSlot)) := by
    simpa [firstLocalRoute, secondData, secondSlot,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedExtendedConnector_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty localClauseMember localLiteralMember
        localMetadata localMetadataLookup second relativeTranslate sourceGaugesNe
  cases secondOriginalRouteEq : secondOriginalRoute with
  | nil => simp [secondOriginalRouteEq] at secondOriginalLength
  | cons firstPoint remaining =>
      cases remaining with
      | nil => simp [secondOriginalRouteEq] at secondOriginalLength
      | cons secondPoint rest =>
          have firstUnit :
              AxisDirection.IsUnitAxisStep firstPoint secondPoint :=
            (List.isChain_cons_cons.mp
              (secondOriginalRouteEq ▸ secondOriginalUnitSteps)).1
          have clearanceRouteEq :
              secondClearanceRoute =
                AxisDirection.unitSubdividePolyline
                  (scalePolyline 2
                    (firstPoint :: secondPoint :: rest)) := by
            simpa [secondClearanceRoute, secondOriginalRoute,
              secondOriginalRouteEq,
              retainedFigureNineSourceClearanceFactor] using
              retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember
          have firstPointEq :
              firstPoint = secondHead := by
            apply Option.some.inj
            exact (by simpa [secondOriginalRoute,
              secondOriginalRouteEq] using secondOriginalValid.1)
          have scaledHead :
              Cell.scale 2 firstPoint =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement second.sourceClause := by
            rw [firstPointEq, secondSourceEq]
            simpa [secondHead, clearancePlacement, clockwisePlacement,
              retainedFigureNineClearancePlacement] using
              PositionedPeriodicCNF.canonicalClausePosition_scale
                retainedFigureNineSourceClearanceFactor
                clockwisePlacement secondClockwiseClause
          have directionBase :
              AxisDirection.polylineFirstDirection
                  secondClearanceRoute =
                AxisDirection.between firstPoint secondPoint := by
            rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty second.sourceClauseMember
              second.sourceLiteralMember]
            simp [secondOriginalRoute, secondOriginalRouteEq]
          have directionEq :
              secondData.direction secondSlot =
                AxisDirection.between firstPoint secondPoint := by
            simpa only [secondData,
              PositionedPeriodicCNF.clauseExitFanData, secondSlot,
              PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
              using directionBase
          let secondShift :=
            PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause
          let farShift := Cell.add offset secondShift
          have connectorCenterEq :
              firstOrigin =
                Cell.add farShift
                  (Cell.scale 144 shiftedFirstHead) := by
            apply Prod.ext <;>
              simp [firstOrigin, farShift, secondShift,
                shiftedFirstHead, firstHead,
                reverseSourceOffset, sourceOffset,
                sourceRelativeTranslate, offset,
                outputPlacement, clearancePlacement,
                clockwisePlacement,
                retainedFigureNineClearancePlacement,
                PeriodicVariablePlacement.scale,
                firstSourceEq, secondSourceEq,
                PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
                PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
                PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
                PeriodicOneInThreeNoUnitsPositioned.placement,
                PeriodicOneInThreePositioned.placement,
                PositionedPeriodicCNF.canonicalClausePosition,
                PeriodicVariablePlacement.translation,
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
                PlanarOneInThree.gadgetScale,
                PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
                retainedFigureNineSourceClearanceFactor,
                Cell.neg, Cell.add, Cell.sub, Cell.scale] <;>
              ring
          have localRouteBounded :
              ∀ point ∈ firstLocalRoute,
                PeriodicEightOccurrenceSplit.WithinCoordinateRadius 72
                  (Cell.add farShift
                    (Cell.scale 144 shiftedFirstHead)) point := by
            intro point pointMember
            rw [← connectorCenterEq]
            exact firstLocalRouteBounded point pointMember
          have secondTailOrthogonal :
              OrthogonalPolyline (secondPoint :: rest) := by
            have originalOrthogonal :
                OrthogonalPolyline secondOriginalRoute := by
              simpa [secondOriginalRoute] using secondOriginalValid.2.2
            exact (List.isChain_cons_cons.mp
              (secondOriginalRouteEq ▸ originalOrthogonal)).2
          have secondTailPointsAvoid :
              ∀ point ∈ secondPoint :: rest,
                point ≠ shiftedFirstHead := by
            intro point pointMember
            exact secondAvoidsShiftedFirstHead.1 point
              (by
                rw [secondOriginalRouteEq]
                exact List.mem_cons_of_mem firstPoint pointMember)
          have secondTailSegmentsAvoid :
              ∀ segment ∈ gridPolylineSegments (secondPoint :: rest),
                segment.IsAxisAligned →
                  ¬segment.Contains shiftedFirstHead := by
            intro segment segmentMember _aligned
            exact secondAvoidsShiftedFirstHead.2 segment
              (by
                rw [secondOriginalRouteEq]
                apply gridPolylineSegments_tail_subset
                exact segmentMember)
          have farTailAvoidBase :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail_of_avoidedCenter
              farShift 72 (by norm_num) secondTailOrthogonal
              secondTailPointsAvoid secondTailSegmentsAvoid
              firstLocalRouteOrthogonal localRouteBounded
          have farTailAvoid :
              RoutesStrictlyAvoidEachOther firstLocalRoute
                (translatePolyline offset
                  (translatePolyline secondShift
                    (scalePolyline
                      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                      (AxisDirection.unitSubdividePolyline
                        (scalePolyline 2
                          (secondPoint :: rest)))))) := by
            simpa [farShift, translatePolyline_add, Cell.add, add_comm] using
              farTailAvoidBase
          have strictSuffix :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translated_fanInheritedRouteSuffix_of_extended_of_farTail
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause secondData secondSlot
              firstPoint secondPoint rest firstLocalRoute offset
              secondFanValid secondSlotActive firstUnit scaledHead directionEq
              extendedAvoid farTailAvoid
          have translatedStrictSuffix :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedFanInheritedRouteSuffix_of_sourceRoute_eq
              outputPlacement clearancePlacement second.sourceClause
              second.generatedClause secondData secondSlot
              secondClearanceRoute
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (firstPoint :: secondPoint :: rest)))
              firstLocalRoute offset clearanceRouteEq strictSuffix
          dsimp only [clearanceWidth, outputPlacement,
            clearancePlacement]
          change RoutesStrictlyAvoidEachOther firstLocalRoute
            (translatePolyline offset
              (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
                outputPlacement clearancePlacement second.sourceClause
                second.generatedClause secondData secondSlot
                secondClearanceRoute))
          exact translatedStrictSuffix

/-- The arbitrary-local unequal-gauge suffix separation specialized to the
local route carried by a first inherited incidence. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex))) := by
  simpa only [first.metadataSourceClause] using
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      first.generatedLiteralMember first.metadata first.metadataLookup
      second relativeTranslate (by
        simpa only [first.metadataSourceClause] using sourceGaugesNe)



/-- The unequal-gauge reverse connector–source-tail cross pair follows by
changing to the second inherited incidence's gauge and translating back. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSourceTail_strictlyAvoids_translatedInheritedConnector_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex
          first.sourceLiteralIndex)).tail)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
          second.sourceClause second.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source)
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement second.sourceClause second.generatedClause)
          (second.sourceSlot clearanceWidth))) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let reverseTranslate := Cell.neg relativeTranslate
  let offset := outputPlacement.translation relativeTranslate
  let reverseOffset := outputPlacement.translation reverseTranslate
  let firstTail :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)).tail
  let secondConnector :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  have reverseSourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement second.sourceClause second.generatedClause ≠
        Cell.add reverseOffset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause) := by
    intro reverseEqual
    apply sourceGaugesNe
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst reverseEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd reverseEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
  have backwards :=
    retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second first reverseTranslate
      (by simpa [outputPlacement, reverseOffset,
        clearancePlacement] using reverseSourceGaugesNe)
  have shifted := backwards.symm.translatePolyline offset
  have shiftCancel : Cell.add reverseOffset offset = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseOffset, offset, reverseTranslate,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  simpa [firstTail, secondConnector, outputPlacement,
    clearancePlacement, clearanceWidth, offset,
    reverseOffset, reverseTranslate] using shifted

/-- The unequal-gauge reverse local–suffix cross pair follows by
changing to the second inherited incidence's gauge and translating back. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSuffix_strictlyAvoids_translatedInheritedLocal_of_sourceGaugesNe
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
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          first.sourceClause first.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source))
        (first.sourceSlot clearanceWidth)
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex first.sourceLiteralIndex))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex)) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let reverseTranslate := Cell.neg relativeTranslate
  let offset := outputPlacement.translation relativeTranslate
  let reverseOffset := outputPlacement.translation reverseTranslate
  let firstSuffix :=
    PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (PositionedPeriodicCNF.clauseExitFanData
        first.sourceClause first.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source))
      (first.sourceSlot clearanceWidth)
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)
  let secondLocal :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement secondClauseIndex secondLiteralIndex
  have reverseSourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement second.sourceClause second.generatedClause ≠
        Cell.add reverseOffset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause) := by
    intro reverseEqual
    apply sourceGaugesNe
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst reverseEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd reverseEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
  have backwards :=
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second first reverseTranslate
      (by simpa [outputPlacement, reverseOffset,
        clearancePlacement] using reverseSourceGaugesNe)
  have shifted := backwards.symm.translatePolyline offset
  have shiftCancel : Cell.add reverseOffset offset = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseOffset, offset, reverseTranslate,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  simpa [firstSuffix, secondLocal, outputPlacement,
    clearancePlacement, clearanceWidth, offset,
    reverseOffset, reverseTranslate] using shifted



/-- In one retained normalized source gauge, the first inherited connector
strictly avoids the translated transformed source tail selected by a
different inherited slot. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesEqual
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
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause)
          (first.sourceSlot clearanceWidth))
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex)).tail)) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
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
  have sourceLiteralIndicesDifferent :=
    retainedOrderedFixedEightFigureNine_inheritedSourceLiteralIndicesDifferent_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
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
  rcases exists_clockwiseClause_of_clearanceClause_mem
      second.sourceClauseMember with
    ⟨clockwiseClause, clockwiseClauseMember, secondSourceClauseEq⟩
  let originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  let clearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source second.sourceClauseIndex second.sourceLiteralIndex
  have originalLength : 2 ≤ originalRoute.length :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [secondSourceClauseEq] using second.sourceLiteralMember)
  have originalOrthogonal : OrthogonalPolyline originalRoute :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [secondSourceClauseEq] using second.sourceLiteralMember)).2.2
  have originalSimple :
      LocalIncidenceDrawing.RouteIsSimple originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [secondSourceClauseEq] using second.sourceLiteralMember)
  have originalUnitSteps :
      originalRoute.IsChain AxisDirection.IsUnitAxisStep :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [secondSourceClauseEq] using second.sourceLiteralMember)
  cases originalRouteEq : originalRoute with
  | nil => simp [originalRouteEq] at originalLength
  | cons firstPoint remaining =>
      cases remaining with
      | nil => simp [originalRouteEq] at originalLength
      | cons secondPoint rest =>
          have firstUnit :
              AxisDirection.IsUnitAxisStep firstPoint secondPoint :=
            (List.isChain_cons_cons.mp
              (originalRouteEq ▸ originalUnitSteps)).1
          have clearanceRouteEq :
              clearanceRoute =
                AxisDirection.unitSubdividePolyline
                  (scalePolyline 2
                    (firstPoint :: secondPoint :: rest)) := by
            simpa [clearanceRoute, originalRoute, originalRouteEq,
              retainedFigureNineSourceClearanceFactor] using
              retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty second.sourceClauseMember
                second.sourceLiteralMember
          have clearanceHead :=
            (retainedFigureNineClearanceIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty second.sourceClauseMember
              second.sourceLiteralMember).1
          have subdividedHead :
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2
                  (firstPoint :: secondPoint :: rest))).head? =
                some (Cell.scale 2 firstPoint) := by
            simpa [scalePolyline] using
              AxisDirection.unitSubdividePolyline_head?
                (points := scalePolyline 2
                  (firstPoint :: secondPoint :: rest))
                (by simp)
          have scaledHeadSecond :
              Cell.scale 2 firstPoint =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement second.sourceClause := by
            apply Option.some.inj
            exact subdividedHead.symm.trans
              (clearanceRouteEq ▸ clearanceHead)
          have scaledHeadFirst :
              Cell.scale 2 firstPoint =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement first.sourceClause := by
            simpa [sourceClausesEqual] using scaledHeadSecond
          have directionBase :
              AxisDirection.polylineFirstDirection clearanceRoute =
                AxisDirection.between firstPoint secondPoint := by
            rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty second.sourceClauseMember
              second.sourceLiteralMember]
            simp [originalRoute, originalRouteEq]
          have directionEq :
              fanData.direction secondSlot =
                AxisDirection.between firstPoint secondPoint := by
            simpa only [fanData,
              PositionedPeriodicCNF.clauseExitFanData, secondSlot,
              sourceClauseIndicesEqual,
              PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
              using directionBase
          have genericStrict :=
            PlanarOneInThreeNoUnitsFigureNine.translatedConnector_strictlyAvoids_otherInheritedSourceRouteTail
              outputPlacement clearancePlacement first.sourceClause
              first.generatedClause fanData firstSlot secondSlot
              firstPoint secondPoint rest fanValid
              firstSlotActive secondSlotActive slotsDifferent firstUnit
              scaledHeadFirst directionEq
              (by simpa [originalRoute, originalRouteEq] using
                originalOrthogonal)
              (by simpa [originalRoute, originalRouteEq] using
                originalSimple)
          have gaugesEqualCommon :
              PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                  outputPlacement first.sourceClause first.generatedClause =
                Cell.add offset
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                    outputPlacement first.sourceClause
                    second.generatedClause) := by
            simpa [sourceClausesEqual, outputPlacement, offset,
              clearancePlacement] using sourceGaugesEqual
          have transformedRouteEq :=
            PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute_eq_translate_of_normalizedSourceClausePosition_eq
              outputPlacement clearancePlacement first.sourceClause
              first.generatedClause second.generatedClause
              clearanceRoute offset gaugesEqualCommon
          have transformedTailEq :
              (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
                outputPlacement clearancePlacement first.sourceClause
                first.generatedClause
                (AxisDirection.unitSubdividePolyline
                  (scalePolyline 2
                    (firstPoint :: secondPoint :: rest)))).tail =
                translatePolyline offset
                  ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
                    outputPlacement clearancePlacement first.sourceClause
                    second.generatedClause clearanceRoute).tail) := by
            simpa [translatePolyline, clearanceRouteEq] using
              congrArg List.tail transformedRouteEq
          rw [show
            PositionedPeriodicCNF.clauseExitFanData
                first.sourceClause first.sourceClauseIndex
                (retainedFigureNineClearanceIncidenceRoutes source) =
              fanData by rfl]
          change RoutesStrictlyAvoidEachOther
            (fanData.translatedRoute
              (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                outputPlacement first.sourceClause first.generatedClause)
              firstSlot)
            (translatePolyline offset
              ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
                outputPlacement clearancePlacement second.sourceClause
                second.generatedClause clearanceRoute).tail))
          rw [← sourceClausesEqual]
          rw [← transformedTailEq]
          exact genericStrict

/-- The reverse connector–source-tail cross pair follows by changing to the
second inherited incidence's gauge and translating back. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSourceTail_strictlyAvoids_translatedInheritedConnector_of_sourceGaugesEqual
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
      ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex
          first.sourceLiteralIndex)).tail)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        ((PositionedPeriodicCNF.clauseExitFanData
          second.sourceClause second.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source)
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement second.sourceClause second.generatedClause)
          (second.sourceSlot clearanceWidth))) := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let reverseTranslate := Cell.neg relativeTranslate
  let offset := outputPlacement.translation relativeTranslate
  let reverseOffset := outputPlacement.translation reverseTranslate
  let firstTail :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)).tail
  let secondConnector :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  have reverseSourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement second.sourceClause second.generatedClause =
        Cell.add reverseOffset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement first.sourceClause first.generatedClause) := by
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst sourceGaugesEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd sourceGaugesEqual
      simp [outputPlacement, clearancePlacement,
        reverseOffset, reverseTranslate,
        PeriodicVariablePlacement.translation,
        Cell.neg, Cell.add, Cell.sub, Cell.scale]
        at coordinateEqual ⊢
      nlinarith
  have reverseOccurrencesDifferent :
      ((secondClauseIndex, secondLiteralIndex), (0, 0)) ≠
        ((firstClauseIndex, firstLiteralIndex), reverseTranslate) := by
    intro reverseEqual
    have clauseEqual : secondClauseIndex = firstClauseIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
        reverseEqual
    have literalEqual : secondLiteralIndex = firstLiteralIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
        reverseEqual
    have reverseTranslateZero : (0, 0) = reverseTranslate :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
        reverseEqual
    have relativeTranslateZero : relativeTranslate = (0, 0) := by
      rcases relativeTranslate with ⟨translateX, translateY⟩
      simp [reverseTranslate, Cell.neg, Cell.sub]
        at reverseTranslateZero ⊢
      exact ⟨reverseTranslateZero.1,
        reverseTranslateZero.2⟩
    apply generatedOccurrencesDifferent
    simp [clauseEqual, literalEqual, relativeTranslateZero]
  have backwards :=
    retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second first reverseTranslate
      (by simpa [outputPlacement, reverseOffset,
        clearancePlacement] using reverseSourceGaugesEqual)
      reverseOccurrencesDifferent
  have shifted := backwards.symm.translatePolyline offset
  have shiftCancel : Cell.add reverseOffset offset = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseOffset, offset, reverseTranslate,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  simpa [firstTail, secondConnector, outputPlacement,
    clearancePlacement, clearanceWidth, offset,
    reverseOffset, reverseTranslate] using shifted

/-- The finite inherited connector and the unchanged transformed source tail
advertise the same splice endpoint. -/
theorem retainedOrderedFixedEightFigureNine_inheritedConnector_spliceEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clauseIndex literalIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    ∃ splicePoint,
      ((PositionedPeriodicCNF.clauseExitFanData
          data.sourceClause data.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source)
        ).translatedRoute
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement data.sourceClause data.generatedClause)
          (data.sourceSlot clearanceWidth)).getLast? = some splicePoint ∧
        ((PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          data.sourceClause data.generatedClause
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex)).tail).head? =
          some splicePoint := by
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let clearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] :=
    List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx data.sourceLiteralMember)
  have fanValid : fanData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember sourceClauseNonempty
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr sourceClauseNonempty)
      (data.sourceClause_width clearanceWidth)
  have slotActive : fanData.SlotActive slot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact data.sourceLiteralIndex_lt
  have directionEq :
      fanData.direction slot =
        AxisDirection.polylineFirstDirection clearanceRoute := by
    simp [fanData, clearanceRoute,
      PositionedPeriodicCNF.clauseExitFanData, slot,
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  have sourceHead :
      clearanceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            clearancePlacement data.sourceClause) := by
    simpa [clearanceRoute, clearancePlacement] using
      (retainedFigureNineClearanceIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember).1
  have sourceTailNonempty :
      ∃ sourceExit, clearanceRoute.tail.head? = some sourceExit := by
    simpa [clearanceRoute] using
      retainedFigureNineClearanceIncidenceRoutes_exits
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  have sourceUnitSteps :
      clearanceRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa [clearanceRoute] using
      retainedFigureNineClearanceIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  have connectorLast :=
    fanData.translatedRoute_getLast?
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement data.sourceClause data.generatedClause)
      fanValid slot slotActive
  have sourceTailHead :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute_tail_head?_of_unitSteps
      outputPlacement clearancePlacement data.sourceClause
      data.generatedClause clearanceRoute sourceHead
      sourceTailNonempty sourceUnitSteps
  rw [directionEq] at connectorLast
  exact ⟨_, connectorLast, sourceTailHead⟩

end PeriodicOrthocrossing
end LeanTrominoes
