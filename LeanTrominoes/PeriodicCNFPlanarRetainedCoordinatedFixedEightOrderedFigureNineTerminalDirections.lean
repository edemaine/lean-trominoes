import LeanTrominoes.OrthogonalPolylineHeadReplacementEndpointDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSuffixCases

/-!
# Terminal directions of ordered Figure 9 suffixes

The direct twice-inherited suffix replaces only the source end of a refined
source route.  Positive scaling and whole-period translation preserve its
variable-side direction, and a valid ordered fan connector can replace the
head without changing that final direction.  This module specializes those
facts to the retained fixed-eight construction.
-/

namespace LeanTrominoes

set_option maxHeartbeats 2000000

namespace PlanarOneInThreeNoUnitsFigureNine

/-- The combined Figure 9 scale and canonical-gauge translation preserve
the source route's final direction. -/
@[simp]
theorem inheritedSourceRoute_lastDirection
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell) :
    AxisDirection.polylineLastDirection
        (inheritedSourceRoute
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute) =
      AxisDirection.polylineLastDirection sourceRoute := by
  have factorPositive : 0 < composedGadgetScale := by
    simp [composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
  simp [inheritedSourceRoute, factorPositive]

/-- Replacing the transformed source head by a matching ordered fan
connector preserves the source route's final direction. -/
theorem fanInheritedRouteSuffix_lastDirection
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute : List Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (directionEq :
      data.direction slot =
        AxisDirection.polylineFirstDirection sourceRoute)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceTailNonempty :
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep)
    (sourceLength : 3 ≤ sourceRoute.length) :
    AxisDirection.polylineLastDirection
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot sourceRoute) =
      AxisDirection.polylineLastDirection sourceRoute := by
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  have connectorLast :
      (data.translatedRoute origin slot).getLast? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) :=
    data.translatedRoute_getLast? origin fanValid slot slotActive
  have transformedTailHead :
      transformed.tail.head? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) := by
    rw [directionEq]
    exact
      inheritedSourceRoute_tail_head?_of_unitSteps
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute sourceHead sourceTailNonempty sourceUnitSteps
  have transformedLength : 3 ≤ transformed.length := by
    simpa [transformed, inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, scalePolyline] using
      sourceLength
  calc
    AxisDirection.polylineLastDirection
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot sourceRoute) =
      AxisDirection.polylineLastDirection transformed := by
        exact
          AxisDirection.polylineLastDirection_replacePolylineHead
            connectorLast transformedTailHead transformedLength
    _ = AxisDirection.polylineLastDirection sourceRoute := by
      exact inheritedSourceRoute_lastDirection
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute

end PlanarOneInThreeNoUnitsFigureNine

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

private theorem
    unitSubdividePolyline_scale_two_length_ge_three_of_unitSteps
    {route : List Cell}
    (length : 2 ≤ route.length)
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep) :
    3 ≤
      (AxisDirection.unitSubdividePolyline
        (scalePolyline 2 route)).length := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second tail =>
          have firstUnit :
              AxisDirection.IsUnitAxisStep first second :=
            (List.isChain_cons_cons.mp unitSteps).1
          simp only [scalePolyline_cons]
          rw [AxisDirection.unitSubdividePolyline.eq_def]
          simp only
          rw [AxisDirection.unitSegmentPoints_scale_two_of_unitAxisStep
            firstUnit]
          simp [LeanTrominoes.joinAtEndpoint]

/-- The factor-two clearance normalization inserts a midpoint into the
first edge of every genuine clockwise source route. -/
theorem retainedFigureNineClearanceIncidenceRoutes_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    3 ≤
      (retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex).length := by
  rw [retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty clauseMember literalMember]
  rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseEq⟩
  subst clause
  have sourceLiteralMember :
      (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
    simpa using literalMember
  let sourceRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex
  have sourceLength : 2 ≤ sourceRoute.length := by
    simpa only [sourceRoute] using
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember
  have sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa only [sourceRoute] using
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember
  simpa [sourceRoute,
    retainedFigureNineSourceClearanceFactor] using
    unitSubdividePolyline_scale_two_length_ge_three_of_unitSteps
      sourceLength sourceUnitSteps

/-- A genuine total terminal direction can only come from a route containing
an actual final edge. -/
private theorem two_le_length_of_polylineLastDirection_isGenuine
    {route : List Cell}
    (genuine :
      (AxisDirection.polylineLastDirection route).IsGenuine) :
    2 ≤ route.length := by
  cases route with
  | nil =>
      simp [AxisDirection.polylineLastDirection,
        AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine, AxisDirection.opposite] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineLastDirection,
            AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine, AxisDirection.opposite] at genuine
      | cons second tail => simp

/-- Every concrete twice-inherited retained suffix enters its final variable
with the same direction as the recovered clearance-source occurrence. -/
theorem
    retainedOrderedFixedEightCompleteRouteSuffixes_lastDirection_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    ∃ data :
        PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex,
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex = some data ∧
        AxisDirection.polylineLastDirection
            ((PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source)
              (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                source sourceWidth)
              (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty)
              (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty)).routes clauseIndex literalIndex) =
          AxisDirection.polylineLastDirection
            (retainedFigureNineClearanceIncidenceRoutes
              source data.sourceClauseIndex data.sourceLiteralIndex) := by
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, dataLookup, suffixShape⟩
  refine ⟨data, dataLookup, ?_⟩
  rw [suffixShape]
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  have sourceIndexLt := data.sourceLiteralIndex_lt
  have sourceClauseWidth := data.sourceClause_width clearanceWidth
  have sourceClausePositive : 0 < data.sourceClause.literals.length := by
    omega
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      sourceClausePositive sourceClauseWidth
  have slotActive : fanData.SlotActive slot := by
    unfold
      PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact sourceIndexLt
  have directionEq :
      fanData.direction slot =
        AxisDirection.polylineFirstDirection
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) := by
    dsimp only [fanData, slot,
      PositionedPeriodicCNF.clauseExitFanData]
    rw [PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  have sourceValid :=
    retainedFigureNineClearanceIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember
  exact
    PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix_lastDirection
      (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source))
      (retainedFigureNineClearancePlacement source)
      data.sourceClause data.generatedClause fanData slot
      (retainedFigureNineClearanceIncidenceRoutes
        source data.sourceClauseIndex data.sourceLiteralIndex)
      (retainedFigureNineClearance_clauseExitFanData_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        (List.length_pos_iff.mp sourceClausePositive))
      slotActive directionEq sourceValid.1
      (retainedFigureNineClearanceIncidenceRoutes_exits
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember)
      (retainedFigureNineClearanceIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember)
      (retainedFigureNineClearanceIncidenceRoutes_length_ge_three
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember)

/-- The complete composed route of every twice-inherited occurrence keeps
the terminal direction of its recovered clearance-source route. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_lastDirection_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    ∃ data :
        PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex,
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex = some data ∧
        AxisDirection.polylineLastDirection
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty clauseIndex literalIndex) =
          AxisDirection.polylineLastDirection
            (retainedFigureNineClearanceIncidenceRoutes
              source data.sourceClauseIndex data.sourceLiteralIndex) := by
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_lastDirection_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, dataLookup, suffixDirection⟩
  refine ⟨data, dataLookup, ?_⟩
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      clearanceWidth clearanceDistinct
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  have sourceUnitSteps :=
    retainedFigureNineClearanceIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember
  have sourceLength :
      2 ≤
        (retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex).length := by
    have :=
      retainedFigureNineClearanceIncidenceRoutes_length_ge_three
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember data.sourceLiteralMember
    omega
  have sourceDirectionGenuine :
      (AxisDirection.polylineLastDirection
        (retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex)).IsGenuine :=
    AxisDirection.polylineLastDirection_isGenuine
      sourceLength sourceUnitSteps
  have suffixLength :
      2 ≤ (suffixes.routes clauseIndex literalIndex).length := by
    apply two_le_length_of_polylineLastDirection_isGenuine
    rw [suffixDirection]
    exact sourceDirectionGenuine
  have localEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      clearanceWidth clearanceDistinct clauseMember literalMember
  have suffixEndpoints :=
    suffixes.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  calc
    AxisDirection.polylineLastDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (suffixes.routes clauseIndex literalIndex) := by
          change
            AxisDirection.polylineLastDirection
                (PositionedPeriodicCNF.spliceLocalIncidenceRoutes
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
                    (retainedFigureNineClearancePositionedFormula source)
                    (retainedFigureNineClearancePlacement source))
                  suffixes clauseIndex literalIndex) = _
          exact
            PositionedPeriodicCNF.spliceLocalIncidenceRoutes_lastDirection
              (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source))
              suffixes clauseIndex literalIndex
              (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)
                clauseIndex literalIndex)
              localEndpoints.2 suffixEndpoints.1 suffixLength
    _ = AxisDirection.polylineLastDirection
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) :=
      suffixDirection

end PeriodicOrthocrossing
end LeanTrominoes
