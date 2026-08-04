import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalExitConnectorSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineTranslatedOrderedInheritedRouteSplicing

/-!
# Same-clause local/inherited separation for retained Figure 9 routes

The retained factor-two source clearance exposes each inherited route as a
doubled clockwise source route.  For a local route selected from the same
generated clause metadata, the finite extended connector certificate covers
the near part of the suffix and factor-144 point clearance covers its refined
far tail.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

local instance orderedLocalInheritedVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem value_eq_of_mem_zipIdx_same_index
    {α : Type*} {values : List α}
    {first second : α} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second :=
  (List.mem_zipIdx' firstMember).2.trans
    (List.mem_zipIdx' secondMember).2.symm

/-- The radius-72 local-route bound, with the clause metadata fixed by a
supplied successful lookup.  Keeping this uniqueness step in the generic
Figure 9 context avoids making later retained-instance proofs unfold the
entire composed formula merely to compare metadata witnesses. -/
theorem normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (metadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata Variable)
    (metadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
        clauseIndex]? = some metadata) :
    ∀ point ∈
        PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          source sourcePlacement clauseIndex literalIndex,
      WithinCoordinateRadius 72
        (Cell.scale
          PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            sourcePlacement metadata.sourceClause clause)) point := by
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_points_within_sourceGaugeRadius72_of_members
        source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨actualMetadata, actualLookup, _actualClause,
      _actualSourceMember, bounded⟩
  have metadataEqual : actualMetadata = metadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans metadataLookup
  subst actualMetadata
  exact bounded

/-- A normalized local route strictly avoids an inherited ordered suffix
selected from the same generated clause, unless their advertised splice
endpoints coincide. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_sameClauseInheritedSuffix
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
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ clause.literals.zipIdx)
    {inheritedLiteralIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex inheritedLiteralIndex)
    (endpointsDifferent :
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex localLiteralIndex).getLast? ≠
        ((PositionedPeriodicCNF.clauseExitFanData
            data.sourceClause data.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source)
          ).translatedExtendedRoute
            (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
              (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source))
              data.sourceClause data.generatedClause)
            (data.sourceSlot
              (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                source sourceWidth))).head?) :
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex localLiteralIndex)
      (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
        (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source))
        (retainedFigureNineClearancePlacement source)
        data.sourceClause data.generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          data.sourceClause data.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source))
        (data.sourceSlot
          (retainedFigureNineClearancePositionedFormula_widthAtMostThree
            source sourceWidth))
        (retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex)) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex localLiteralIndex
  let clearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  have generatedClauseEqual : data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  subst clause
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] := by
    exact List.ne_nil_of_mem
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
  rcases exists_clockwiseClause_of_clearanceClause_mem
      data.sourceClauseMember with
    ⟨clockwiseClause, clockwiseClauseMember, sourceClauseEq⟩
  let originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  have originalLength : 2 ≤ originalRoute.length :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  have originalOrthogonal : OrthogonalPolyline originalRoute :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)).2.2
  have originalSimple :
      LocalIncidenceDrawing.RouteIsSimple originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  have originalUnitSteps :
      originalRoute.IsChain AxisDirection.IsUnitAxisStep :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  cases originalRouteEq : originalRoute with
  | nil => simp [originalRouteEq] at originalLength
  | cons first remaining =>
      cases remaining with
      | nil => simp [originalRouteEq] at originalLength
      | cons second rest =>
          have firstUnit : AxisDirection.IsUnitAxisStep first second :=
            (List.isChain_cons_cons.mp
              (originalRouteEq ▸ originalUnitSteps)).1
          have clearanceRouteEq :
              clearanceRoute =
                AxisDirection.unitSubdividePolyline
                  (scalePolyline 2 (first :: second :: rest)) := by
            simpa [clearanceRoute, originalRoute, originalRouteEq,
              retainedFigureNineSourceClearanceFactor] using
              retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty data.sourceClauseMember
                data.sourceLiteralMember
          have clearanceHead :=
            (retainedFigureNineClearanceIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty data.sourceClauseMember
              data.sourceLiteralMember).1
          have subdividedHead :
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (first :: second :: rest))).head? =
                  some (Cell.scale 2 first) := by
            simpa [scalePolyline] using
              AxisDirection.unitSubdividePolyline_head?
                (points := scalePolyline 2 (first :: second :: rest))
                (by simp)
          have scaledHead :
              Cell.scale 2 first =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement data.sourceClause := by
            apply Option.some.inj
            exact subdividedHead.symm.trans
              (clearanceRouteEq ▸ clearanceHead)
          have directionBase :
              AxisDirection.polylineFirstDirection
                  (retainedFigureNineClearanceIncidenceRoutes
                    source data.sourceClauseIndex
                    data.sourceLiteralIndex) =
                AxisDirection.between first second := by
            rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty data.sourceClauseMember
              data.sourceLiteralMember]
            simp [originalRoute, originalRouteEq]
          have directionEq :
              fanData.direction slot =
                AxisDirection.between first second := by
            simpa only [fanData,
              PositionedPeriodicCNF.clauseExitFanData, slot,
              PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
              using directionBase
          have localBounded :=
            normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
              clearanceSource clearancePlacement clearanceWidth
              data.generatedClauseMember localLiteralMember
              data.metadata data.metadataLookup
          have centerEq :
              Cell.scale
                  PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                  (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                    clearancePlacement data.metadata.sourceClause
                    data.generatedClause) =
                Cell.add
                  (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                    outputPlacement clearancePlacement data.sourceClause
                    data.generatedClause)
                  (Cell.scale 144 first) := by
            rw [data.metadataSourceClause,
              ← PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
                clearanceSource clearancePlacement data.sourceClause
                data.generatedClause]
            simp only [
              PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift]
            rw [← scaledHead]
            apply Prod.ext <;>
              simp [outputPlacement,
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
                PlanarOneInThree.gadgetScale,
                PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
                Cell.add, Cell.sub, Cell.scale] <;>
              ring
          have localBounded' :
              ∀ point ∈ localRoute,
                WithinCoordinateRadius 72
                  (Cell.add
                    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                      outputPlacement clearancePlacement data.sourceClause
                      data.generatedClause)
                    (Cell.scale 144 first)) point := by
            intro point pointMember
            rw [← centerEq]
            exact localBounded point (by simpa [localRoute] using pointMember)
          have localOrthogonal : OrthogonalPolyline localRoute :=
            PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
              clearanceSource clearancePlacement clearanceWidth
              (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty)
              data.generatedClauseMember localLiteralMember
          have endpointsDifferentMetadata :
              localRoute.getLast? ≠
                (fanData.translatedExtendedRoute
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                    outputPlacement data.metadata.sourceClause
                    data.metadata.clause)
                  slot).head? := by
            rw [data.metadataSourceClause, data.metadataClause]
            simpa only [localRoute, fanData, slot, clearanceSource,
              clearancePlacement, clearanceWidth, outputPlacement]
              using endpointsDifferent
          have extendedAvoidMetadata :=
            PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_strictlyAvoids_translatedExtendedExitConnector_of_members
              clearanceSource clearancePlacement clearanceWidth
              data.generatedClauseMember localLiteralMember
              data.metadata data.metadataLookup fanData slot
              fanValid slotActive endpointsDifferentMetadata
          have extendedAvoid :
              RoutesStrictlyAvoidEachOther localRoute
                (fanData.translatedExtendedRoute
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                    outputPlacement data.sourceClause data.generatedClause)
                  slot) :=
            by
              rw [← data.metadataSourceClause, ← data.metadataClause]
              exact extendedAvoidMetadata
          have farAvoid :
              RoutesStrictlyAvoidEachOther localRoute
                (PeriodicOrthocrossing.translatePolyline
                  (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                    outputPlacement clearancePlacement data.sourceClause
                    data.generatedClause)
                  (scalePolyline
                    PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                    (AxisDirection.unitSubdividePolyline
                      (scalePolyline 2 (second :: rest))))) :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail
              (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                outputPlacement clearancePlacement data.sourceClause
                data.generatedClause)
              (by simpa [originalRoute, originalRouteEq] using originalOrthogonal)
              (by simpa [originalRoute, originalRouteEq] using originalSimple)
              localOrthogonal localBounded'
          have assembled :
              RoutesStrictlyAvoidEachOther localRoute
                (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
                  outputPlacement clearancePlacement data.sourceClause
                  data.generatedClause fanData slot clearanceRoute) := by
            rw [clearanceRouteEq]
            exact
              PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_fanInheritedRouteSuffix_of_extended_of_farTail
                outputPlacement clearancePlacement data.sourceClause
                data.generatedClause fanData slot first second rest localRoute
                fanValid slotActive firstUnit scaledHead directionEq
                extendedAvoid farAvoid
          exact assembled

/-- A normalized local route strictly avoids a relatively translated
inherited suffix whenever their normalized source gauges agree and their
advertised splice endpoints differ.  The finite connector is compared in
the common gauge, while the far source tail uses the same factor-144
clearance as the unshifted same-clause case. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_translatedInheritedSuffix_of_sourceGauge
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
    (localMetadataClause : localMetadata.clause = localClause)
    {inheritedClauseIndex inheritedLiteralIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        inheritedClauseIndex inheritedLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            data.sourceClause data.generatedClause))
    (endpointsDifferent :
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          localClauseIndex localLiteralIndex).getLast? ≠
        (PeriodicOrthocrossing.translatePolyline
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          ((PositionedPeriodicCNF.clauseExitFanData
              data.sourceClause data.sourceClauseIndex
              (retainedFigureNineClearanceIncidenceRoutes source)
            ).translatedExtendedRoute
              (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                  (retainedFigureNineClearancePositionedFormula source)
                  (retainedFigureNineClearancePlacement source))
                data.sourceClause data.generatedClause)
              (data.sourceSlot
                (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                  source sourceWidth)))).head?) :
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex)
      (PeriodicOrthocrossing.translatePolyline
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)).translation
            relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          (retainedFigureNineClearancePlacement source)
          data.sourceClause data.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            data.sourceClause data.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (data.sourceSlot
            (retainedFigureNineClearancePositionedFormula_widthAtMostThree
              source sourceWidth))
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
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
  let clearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] := by
    exact List.ne_nil_of_mem
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
  rcases exists_clockwiseClause_of_clearanceClause_mem
      data.sourceClauseMember with
    ⟨clockwiseClause, clockwiseClauseMember, sourceClauseEq⟩
  let originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  have originalLength : 2 ≤ originalRoute.length :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  have originalOrthogonal : OrthogonalPolyline originalRoute :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)).2.2
  have originalSimple :
      LocalIncidenceDrawing.RouteIsSimple originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  have originalUnitSteps :
      originalRoute.IsChain AxisDirection.IsUnitAxisStep :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  cases originalRouteEq : originalRoute with
  | nil => simp [originalRouteEq] at originalLength
  | cons first remaining =>
      cases remaining with
      | nil => simp [originalRouteEq] at originalLength
      | cons second rest =>
          have firstUnit : AxisDirection.IsUnitAxisStep first second :=
            (List.isChain_cons_cons.mp
              (originalRouteEq ▸ originalUnitSteps)).1
          have clearanceRouteEq :
              clearanceRoute =
                AxisDirection.unitSubdividePolyline
                  (scalePolyline 2 (first :: second :: rest)) := by
            simpa [clearanceRoute, originalRoute, originalRouteEq,
              retainedFigureNineSourceClearanceFactor] using
              retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty data.sourceClauseMember
                data.sourceLiteralMember
          have clearanceHead :=
            (retainedFigureNineClearanceIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty data.sourceClauseMember
              data.sourceLiteralMember).1
          have subdividedHead :
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (first :: second :: rest))).head? =
                  some (Cell.scale 2 first) := by
            simpa [scalePolyline] using
              AxisDirection.unitSubdividePolyline_head?
                (points := scalePolyline 2 (first :: second :: rest))
                (by simp)
          have scaledHead :
              Cell.scale 2 first =
                PositionedPeriodicCNF.canonicalClausePosition
                  clearancePlacement data.sourceClause := by
            apply Option.some.inj
            exact subdividedHead.symm.trans
              (clearanceRouteEq ▸ clearanceHead)
          have directionBase :
              AxisDirection.polylineFirstDirection
                  (retainedFigureNineClearanceIncidenceRoutes
                    source data.sourceClauseIndex
                    data.sourceLiteralIndex) =
                AxisDirection.between first second := by
            rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty data.sourceClauseMember
              data.sourceLiteralMember]
            simp [originalRoute, originalRouteEq]
          have directionEq :
              fanData.direction slot =
                AxisDirection.between first second := by
            simpa only [fanData,
              PositionedPeriodicCNF.clauseExitFanData, slot,
              PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
              using directionBase
          have localBounded :=
            normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
              clearanceSource clearancePlacement clearanceWidth
              localClauseMember localLiteralMember
              localMetadata localMetadataLookup
          have centerEq :
              Cell.scale
                  PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                  (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                    clearancePlacement localMetadata.sourceClause
                    localClause) =
                Cell.add
                  (Cell.add
                    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                      outputPlacement clearancePlacement data.sourceClause
                      data.generatedClause)
                    offset)
                  (Cell.scale 144 first) := by
            rw [← PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
              clearanceSource clearancePlacement
              localMetadata.sourceClause localClause]
            rw [sourceGaugesEqual]
            simp only [
              PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift]
            rw [← scaledHead]
            apply Prod.ext <;>
              simp [offset, outputPlacement,
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
                PlanarOneInThree.gadgetScale,
                PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
                Cell.add, Cell.sub, Cell.scale] <;>
              ring
          have localBounded' :
              ∀ point ∈ localRoute,
                WithinCoordinateRadius 72
                  (Cell.add
                    (Cell.add
                      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                        outputPlacement clearancePlacement data.sourceClause
                        data.generatedClause)
                      offset)
                    (Cell.scale 144 first)) point := by
            intro point pointMember
            rw [← centerEq]
            exact localBounded point
              (by simpa [localRoute] using pointMember)
          have localOrthogonal : OrthogonalPolyline localRoute :=
            PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
              clearanceSource clearancePlacement clearanceWidth
              (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty)
              localClauseMember localLiteralMember
          have extendedRouteEq :
              fanData.translatedExtendedRoute
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                    outputPlacement localMetadata.sourceClause
                    localMetadata.clause)
                  slot =
                PeriodicOrthocrossing.translatePolyline offset
                  (fanData.translatedExtendedRoute
                    (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                      outputPlacement data.sourceClause data.generatedClause)
                    slot) := by
            rw [localMetadataClause, sourceGaugesEqual]
            unfold
              PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.translatedExtendedRoute
              PeriodicOrthocrossing.translatePolyline
            rw [List.map_map]
            apply List.map_congr_left
            intro point pointMember
            rcases point with ⟨pointX, pointY⟩
            apply Prod.ext <;>
              simp [offset, outputPlacement, clearanceSource,
                clearancePlacement, Cell.add] <;>
              ring
          have endpointsDifferentMetadata :
              localRoute.getLast? ≠
                (fanData.translatedExtendedRoute
                  (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                    outputPlacement localMetadata.sourceClause
                    localMetadata.clause)
                  slot).head? := by
            rw [extendedRouteEq]
            simpa only [localRoute, fanData, slot, clearanceSource,
              clearancePlacement, clearanceWidth, outputPlacement, offset]
              using endpointsDifferent
          have extendedAvoidMetadata :=
            PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_strictlyAvoids_translatedExtendedExitConnector_of_members
              clearanceSource clearancePlacement clearanceWidth
              localClauseMember localLiteralMember
              localMetadata localMetadataLookup fanData slot
              fanValid slotActive endpointsDifferentMetadata
          have extendedAvoid :
              RoutesStrictlyAvoidEachOther localRoute
                (PeriodicOrthocrossing.translatePolyline offset
                  (fanData.translatedExtendedRoute
                    (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
                      outputPlacement data.sourceClause data.generatedClause)
                    slot)) := by
            rw [← extendedRouteEq]
            exact extendedAvoidMetadata
          have farAvoidCombined :
              RoutesStrictlyAvoidEachOther localRoute
                (PeriodicOrthocrossing.translatePolyline
                  (Cell.add
                    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                      outputPlacement clearancePlacement data.sourceClause
                      data.generatedClause)
                    offset)
                  (scalePolyline
                    PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                    (AxisDirection.unitSubdividePolyline
                      (scalePolyline 2 (second :: rest))))) :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail
              (Cell.add
                (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                  outputPlacement clearancePlacement data.sourceClause
                  data.generatedClause)
                offset)
              (by simpa [originalRoute, originalRouteEq] using originalOrthogonal)
              (by simpa [originalRoute, originalRouteEq] using originalSimple)
              localOrthogonal localBounded'
          have farAvoid :
              RoutesStrictlyAvoidEachOther localRoute
                (PeriodicOrthocrossing.translatePolyline offset
                  (PeriodicOrthocrossing.translatePolyline
                    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
                      outputPlacement clearancePlacement data.sourceClause
                      data.generatedClause)
                    (scalePolyline
                      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                      (AxisDirection.unitSubdividePolyline
                        (scalePolyline 2 (second :: rest)))))) := by
            rw [translatePolyline_add]
            exact farAvoidCombined
          have assembled :
              RoutesStrictlyAvoidEachOther localRoute
                (PeriodicOrthocrossing.translatePolyline offset
                  (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
                    outputPlacement clearancePlacement data.sourceClause
                    data.generatedClause fanData slot clearanceRoute)) := by
            rw [clearanceRouteEq]
            exact
              PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translated_fanInheritedRouteSuffix_of_extended_of_farTail
                outputPlacement clearancePlacement data.sourceClause
                data.generatedClause fanData slot first second rest localRoute
                offset fanValid slotActive firstUnit scaledHead directionEq
                extendedAvoid farAvoid
          exact assembled

end PeriodicOrthocrossing
end LeanTrominoes
