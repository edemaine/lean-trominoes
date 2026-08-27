/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureJoinPrefix
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalFarTailSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOwnTailSeparation

/-!
# Localized normalization of one retained inherited Figure 9 route

The complete local-plus-extended prefix may contain the fixed Figure 9
radial reversal.  Its inherited far tail is simple and meets that prefix only
at the outer source boundary, so normalization is confined to the finite
prefix.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

local instance ownRouteNormalizationVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Normalization of one retained route inherited from the original source
acts only on its complete local-plus-extended prefix. -/
theorem
    normalizeOrthogonalPolyline_retainedOrderedFixedEightFigureNineOwnInheritedRoute
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
        clauseIndex literalIndex)
    (first second : Cell)
    (rest : List Cell)
    (originalRouteEq :
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex =
        first :: second :: rest) :
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
        clearanceSource clearancePlacement clauseIndex literalIndex
    let fanData :=
      PositionedPeriodicCNF.clauseExitFanData
        data.sourceClause data.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source)
    let slot := data.sourceSlot clearanceWidth
    let origin :=
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement data.sourceClause data.generatedClause
    let farTail :=
      translatePolyline
        (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
          outputPlacement clearancePlacement data.sourceClause
          data.generatedClause)
        (scalePolyline
          PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))
    AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint localRoute
          (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
            outputPlacement clearancePlacement data.sourceClause
            data.generatedClause fanData slot
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (first :: second :: rest))))) =
      joinAtEndpoint
        (AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint localRoute
            (fanData.translatedExtendedRoute origin slot)))
        (AxisDirection.unitSubdividePolyline farTail) := by
  dsimp only
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
      clearanceSource clearancePlacement clauseIndex literalIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  let origin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement data.sourceClause data.generatedClause
  let extended := fanData.translatedExtendedRoute origin slot
  let shift :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
      outputPlacement clearancePlacement data.sourceClause
      data.generatedClause
  let farTail :=
    translatePolyline shift
      (scalePolyline
        PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest))))
  let boundary := Cell.add origin
    (PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.outerSourceExit
      (fanData.direction slot))
  let finitePrefix := joinAtEndpoint localRoute extended
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
  have firstUnit : AxisDirection.IsUnitAxisStep first second :=
    (List.isChain_cons_cons.mp
      (by simpa [originalRoute, originalRouteEq] using
        originalUnitSteps)).1
  have clearanceRouteEq :
      retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex =
        AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (first :: second :: rest)) := by
    simpa [originalRoute, originalRouteEq,
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
    exact subdividedHead.symm.trans (clearanceRouteEq ▸ clearanceHead)
  have directionBase :
      AxisDirection.polylineFirstDirection
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) =
        AxisDirection.between first second := by
    rw [retainedFigureNineClearanceIncidenceRoutes_firstDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember
      data.sourceLiteralMember]
    simp [originalRouteEq]
  have directionEq :
      fanData.direction slot = AxisDirection.between first second := by
    simpa only [fanData,
      PositionedPeriodicCNF.clauseExitFanData, slot,
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
      using directionBase
  have localEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      data.generatedClauseMember data.generatedLiteralMember
  have localNonempty : localRoute ≠ [] := by
    intro empty
    simp [localRoute, empty] at localEndpoints
  have localLast :
      localRoute.getLast? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) := by
    calc
      localRoute.getLast? =
          some
            (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
              clearanceSource clearancePlacement clauseIndex literalIndex) :=
        localEndpoints.2
      _ = some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement data.sourceClause data.generatedClause
            data.sourceLiteralIndex) := congrArg some data.localEndpoint
      _ = some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) := by
        simp only [
          PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
          origin, outputPlacement, slot,
          PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  have extendedHead :
      extended.head? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) := by
    simpa only [extended] using
      fanData.translatedExtendedRoute_head?
        origin fanValid slot slotActive
  have extendedNonempty : extended ≠ [] := by
    intro empty
    simp [empty] at extendedHead
  have localOrthogonal : OrthogonalPolyline localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      data.generatedClauseMember data.generatedLiteralMember
  have extendedOrthogonal : OrthogonalPolyline extended :=
    fanData.translatedExtendedRoute_orthogonal
      origin fanValid slot slotActive
  have extendedLast : extended.getLast? = some boundary := by
    simpa only [extended, boundary] using
      fanData.translatedExtendedRoute_getLast?
        origin fanValid slot slotActive
  have farTailHead : farTail.head? = some boundary := by
    simpa only [farTail, boundary, origin, shift] using
      PlanarOneInThreeNoUnitsFigureNine.translatedScaledDoubledSubdividedTail_head?
        outputPlacement clearancePlacement data.sourceClause
        data.generatedClause fanData slot first second rest
        firstUnit scaledHead directionEq
  have farTailNonempty : farTail ≠ [] := by
    intro empty
    simp [empty] at farTailHead
  have farTailOrthogonal : OrthogonalPolyline farTail := by
    have originalOrthogonal' :
        OrthogonalPolyline (first :: second :: rest) := by
      simpa [originalRoute, originalRouteEq] using originalOrthogonal
    have sourceTailOrthogonal : OrthogonalPolyline (second :: rest) :=
      (List.isChain_cons_cons.mp originalOrthogonal').2
    exact
      ((AxisDirection.unitSubdividePolyline_orthogonal
          (sourceTailOrthogonal.scalePolyline (by norm_num))).scalePolyline
        (by
          norm_num [
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
            PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale])).translate shift
  have farTailSimple :
      LocalIncidenceDrawing.RouteIsSimple farTail := by
    simpa only [farTail, shift] using
      PlanarOneInThreeNoUnitsFigureNine.farTail_isSimple
        outputPlacement clearancePlacement data.sourceClause
        data.generatedClause first second rest
        (by simpa [originalRoute, originalRouteEq] using originalOrthogonal)
        (by simpa [originalRoute, originalRouteEq] using originalSimple)
  have localFarStrict :
      RoutesStrictlyAvoidEachOther localRoute farTail := by
    simpa only [localRoute, farTail, shift, outputPlacement,
      clearanceSource, clearancePlacement] using
      retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_sameClauseFarTail
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data data.generatedLiteralMember
        first second rest originalRouteEq
  have extendedFarOnlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline extended →
        point ∈ AxisDirection.unitSubdividePolyline farTail →
        point = boundary := by
    simpa only [extended, farTail, boundary, origin, shift] using
      PlanarOneInThreeNoUnitsFigureNine.translatedExtendedRoute_farTail_onlyCommon
        outputPlacement clearancePlacement data.sourceClause
        data.generatedClause fanData slot first second rest
        fanValid slotActive firstUnit scaledHead directionEq
        (by simpa [originalRoute, originalRouteEq] using originalOrthogonal)
        (by simpa [originalRoute, originalRouteEq] using originalSimple)
  have finitePrefixFarOnlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline finitePrefix →
        point ∈ AxisDirection.unitSubdividePolyline farTail →
        point = boundary := by
    simpa only [finitePrefix] using
      AxisDirection.unitSubdividePolyline_only_common_of_join_left_strict
        localNonempty localLast extendedHead localOrthogonal
        farTailOrthogonal localFarStrict extendedFarOnlyCommon
  have finitePrefixNonempty : finitePrefix ≠ [] := by
    intro empty
    have joinedEmpty : localRoute ++ extended.tail = [] := by
      simpa [finitePrefix, joinAtEndpoint] using empty
    exact localNonempty (List.append_eq_nil_iff.mp joinedEmpty).1
  have finitePrefixOrthogonal : OrthogonalPolyline finitePrefix :=
    localOrthogonal.joinAtEndpoint extendedOrthogonal
      localLast extendedHead
  have finitePrefixLast : finitePrefix.getLast? = some boundary :=
    joinAtEndpoint_getLast? localLast extendedHead extendedLast
  rw [PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix_eq_extended_join_farTail
    outputPlacement clearancePlacement data.sourceClause
    data.generatedClause fanData slot first second rest
    firstUnit scaledHead directionEq]
  rw [joinAtEndpoint_assoc_of_middle_ne_nil extendedNonempty]
  exact
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
      finitePrefixNonempty farTailNonempty finitePrefixOrthogonal
      farTailOrthogonal farTailSimple finitePrefixLast farTailHead
      finitePrefixFarOnlyCommon

end PeriodicOrthocrossing
end LeanTrominoes
