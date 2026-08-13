/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalInheritedSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineTerminalDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin

/-!
# Variable-endpoint isolation for inherited ordered Figure 9 routes

The final endpoint of a twice-inherited raw route cannot occur earlier in
its ordered unit subdivision.  The transformed tail inherits this property
from the simple clearance-source route.  Its new local-and-fan prefix stays
in a radius-`73` neighborhood of the source clause, while the unchanged far
tail is separated at the combined scale `144`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

private theorem value_eq_of_mem_zipIdx_same_index
    {Value : Type*} {values : List Value}
    {first second : Value} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- Every twice-inherited ordered Figure 9 route has an isolated variable
endpoint after ordered unit subdivision. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_lastNotInDropLast_of_inherited
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
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex)) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement := retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, _dataLookup, suffixShape⟩
  have generatedClauseEqual : data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  subst clause
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex literalIndex
  let clearanceRoute :=
    retainedFigureNineClearanceIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  let origin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement data.sourceClause data.generatedClause
  let connector := fanData.translatedRoute origin slot
  let shift :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
      outputPlacement clearancePlacement data.sourceClause
      data.generatedClause
  let transformed :=
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement data.sourceClause
      data.generatedClause clearanceRoute
  let routePrefix := joinAtEndpoint localRoute connector
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
    unfold
      PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact data.sourceLiteralIndex_lt
  have directionEq :
      fanData.direction slot =
        AxisDirection.polylineFirstDirection clearanceRoute := by
    dsimp only [fanData, slot,
      PositionedPeriodicCNF.clauseExitFanData]
    rw [PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  have clearanceValid :=
    retainedFigureNineClearanceIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember
      data.sourceLiteralMember
  have clearanceLength : 3 ≤ clearanceRoute.length := by
    simpa only [clearanceRoute] using
      retainedFigureNineClearanceIncidenceRoutes_length_ge_three
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  have clearanceSimple :
      LocalIncidenceDrawing.RouteIsSimple clearanceRoute := by
    simpa only [clearanceRoute] using
      retainedFigureNineClearanceIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  have clearanceUnitSteps :
      clearanceRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa only [clearanceRoute] using
      retainedFigureNineClearanceIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  rcases
      retainedFigureNineClearanceIncidenceRoutes_exits
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember with
    ⟨sourceExit, clearanceTailHead⟩
  have transformedTailHead :
      transformed.tail.head? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.sourceExit
              (fanData.direction slot))) := by
    rw [directionEq]
    exact
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute_tail_head?_of_unitSteps
        outputPlacement clearancePlacement data.sourceClause
        data.generatedClause clearanceRoute clearanceValid.1
        ⟨sourceExit, clearanceTailHead⟩ clearanceUnitSteps
  have connectorHead :
      connector.head? =
        some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement data.sourceClause data.generatedClause
            slot.val) := by
    simpa [connector, origin,
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort] using
      fanData.translatedRoute_head? origin fanValid slot slotActive
  have connectorLast :
      connector.getLast? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.sourceExit
              (fanData.direction slot))) := by
    simpa only [connector] using
      fanData.translatedRoute_getLast? origin fanValid slot slotActive
  have localEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth clearanceDistinct
      data.generatedClauseMember literalMember
  have localHead :
      localRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            outputPlacement data.generatedClause) := by
    simpa only [localRoute, outputPlacement] using localEndpoints.1
  have localLast :
      localRoute.getLast? =
        some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement data.sourceClause data.generatedClause
            slot.val) := by
    simpa [localRoute, outputPlacement, clearanceSource,
      clearancePlacement, slot,
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val,
      data.localEndpoint] using localEndpoints.2
  have connectorNe : connector ≠ [] := by
    intro empty
    rw [empty] at connectorHead
    simp at connectorHead
  have localNe : localRoute ≠ [] := by
    intro empty
    rw [empty] at localHead
    simp at localHead
  have routePrefixNe : routePrefix ≠ [] := by
    intro empty
    have joinedHead :=
      joinAtEndpoint_head? (second := connector) localHead
    rw [show joinAtEndpoint localRoute connector = routePrefix by rfl,
      empty] at joinedHead
    simp at joinedHead
  have connectorOrthogonal : OrthogonalPolyline connector := by
    simpa only [connector] using
      fanData.translatedRoute_orthogonal origin fanValid slot slotActive
  have localOrthogonal : OrthogonalPolyline localRoute := by
    simpa only [localRoute] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        data.generatedClauseMember literalMember
  have routePrefixOrthogonal : OrthogonalPolyline routePrefix := by
    exact localOrthogonal.joinAtEndpoint connectorOrthogonal
      localLast connectorHead
  have routePrefixLast :
      routePrefix.getLast? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.sourceExit
              (fanData.direction slot))) := by
    exact joinAtEndpoint_getLast? localLast connectorHead connectorLast
  have clearanceTailLength : 2 ≤ clearanceRoute.tail.length := by
    rw [List.length_tail]
    omega
  have clearanceTailOrthogonal : OrthogonalPolyline clearanceRoute.tail :=
    clearanceValid.2.2.tail
  have clearanceTailFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline clearanceRoute.tail) :=
    AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
      clearanceTailOrthogonal clearanceSimple.tail
  have transformedTailLength : 2 ≤ transformed.tail.length := by
    simpa [transformed,
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, scalePolyline] using
      clearanceTailLength
  have transformedTailOrthogonal : OrthogonalPolyline transformed.tail := by
    simpa [transformed,
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, scalePolyline,
      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale] using
      (clearanceTailOrthogonal.scalePolyline
        (factor := 72) (by norm_num)).translate shift
  have transformedTailFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline transformed.tail) := by
    have scaled :=
      clearanceTailFresh.unitSubdividePolyline_scalePolyline
        (factor := 72) (by norm_num) clearanceTailOrthogonal
    have translated := scaled.unitSubdividePolyline_map_add shift
    simpa [transformed, shift,
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, scalePolyline,
      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale] using translated
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
  have originalSimple : LocalIncidenceDrawing.RouteIsSimple originalRoute :=
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
              (clearanceRouteEq ▸ clearanceValid.1)
          have originEq :
              origin = Cell.add shift (Cell.scale 144 first) := by
            rw [show origin =
                Cell.add shift
                  (Cell.scale
                    PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                    (Cell.scale 2 first)) by
              rw [scaledHead]
              apply Prod.ext <;>
                simp [origin, shift,
                  PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift,
                  Cell.add, Cell.sub, Cell.scale]]
            apply congrArg (Cell.add shift)
            apply Prod.ext <;>
              simp [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
                PlanarOneInThree.gadgetScale,
                PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
                Cell.scale] <;>
              ring
          have localBounded :=
            normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
              clearanceSource clearancePlacement clearanceWidth
              data.generatedClauseMember literalMember
              data.metadata data.metadataLookup
          have localCenterEq :
              Cell.scale
                  PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                  (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                    clearancePlacement data.metadata.sourceClause
                    data.generatedClause) = origin := by
            rw [data.metadataSourceClause,
              ← PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
                clearanceSource clearancePlacement data.sourceClause
                data.generatedClause]
          have routePrefixBounded :
              ∀ point ∈ routePrefix,
                WithinCoordinateRadius 73
                  (Cell.add shift (Cell.scale 144 first)) point := by
            intro point pointMember
            rw [← originEq]
            have parts : point ∈ localRoute ∨ point ∈ connector := by
              change point ∈ joinAtEndpoint localRoute connector at pointMember
              rw [joinAtEndpoint, List.mem_append] at pointMember
              exact pointMember.imp_right List.mem_of_mem_tail
            rcases parts with localMember | connectorMember
            · rw [← localCenterEq]
              exact (localBounded point
                (by simpa [localRoute] using localMember)).mono
                  (secondRadius := 73) (by norm_num)
            · exact fanData.translatedRoute_points_within_sourceNeighborhood
                origin fanValid slot slotActive connectorMember
          let farTail :=
            PeriodicOrthocrossing.translatePolyline shift
              (scalePolyline
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                (AxisDirection.unitSubdividePolyline
                  (scalePolyline 2 (second :: rest))))
          have originalTailOrthogonal :
              OrthogonalPolyline (second :: rest) :=
            (List.isChain_cons_cons.mp
              (originalRouteEq ▸ originalOrthogonal)).2
          have farTailOrthogonal : OrthogonalPolyline farTail := by
            exact
              (((originalTailOrthogonal.scalePolyline
                  (factor := 2) (by norm_num))
                |> AxisDirection.unitSubdividePolyline_orthogonal)
                |>.scalePolyline (factor := 72) (by norm_num)
                |>.translate shift)
          have farAvoid : RoutesStrictlyAvoidEachOther routePrefix farTail :=
            PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail_of_radius
              shift 73 (by norm_num)
              (by simpa [originalRoute, originalRouteEq] using
                originalOrthogonal)
              (by simpa [originalRoute, originalRouteEq] using originalSimple)
              routePrefixOrthogonal routePrefixBounded
          have subdivisionsDisjoint :
              List.Disjoint
                (AxisDirection.unitSubdividePolyline routePrefix)
                (AxisDirection.unitSubdividePolyline farTail) :=
            farAvoid.unitSubdividePolyline_disjoint
              routePrefixOrthogonal farTailOrthogonal
          have originalTailNe : second :: rest ≠ [] := by simp
          let originalLast := (second :: rest).getLast originalTailNe
          let target := Cell.add shift (Cell.scale 144 originalLast)
          have originalLastLookup :
              (first :: second :: rest).getLast? = some originalLast := by
            simpa [originalLast] using
              List.getLast?_eq_some_getLast originalTailNe
          have tailLastLookup :
              (second :: rest).getLast? = some originalLast := by
            exact List.getLast?_eq_some_getLast originalTailNe
          have farTailLast : farTail.getLast? = some target := by
            have doubledTailOrthogonal :
                OrthogonalPolyline (scalePolyline 2 (second :: rest)) :=
              originalTailOrthogonal.scalePolyline
                (factor := 2) (by norm_num)
            have subdividedLast :
                (AxisDirection.unitSubdividePolyline
                  (scalePolyline 2 (second :: rest))).getLast? =
                    some (Cell.scale 2 originalLast) := by
              rw [AxisDirection.unitSubdividePolyline_getLast?
                (by simp [scalePolyline]) doubledTailOrthogonal,
                scalePolyline_getLast?, tailLastLookup]
              rfl
            unfold farTail PeriodicOrthocrossing.translatePolyline
            rw [List.getLast?_map, scalePolyline_getLast?, subdividedLast]
            simp [target,
              PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
              PlanarOneInThree.gadgetScale,
              PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
              Cell.scale_scale]
          have farTailNe : farTail ≠ [] := by
            intro empty
            rw [empty] at farTailLast
            simp at farTailLast
          have targetInFarSubdivision :
              target ∈ AxisDirection.unitSubdividePolyline farTail := by
            apply mem_of_getLast?_eq_some
            rw [AxisDirection.unitSubdividePolyline_getLast?
              farTailNe farTailOrthogonal, farTailLast]
          have targetNotInPrefix :
              target ∉ AxisDirection.unitSubdividePolyline routePrefix := by
            intro targetMember
            exact (List.disjoint_left.mp subdivisionsDisjoint)
              targetMember targetInFarSubdivision
          have clearanceLast : clearanceRoute.getLast? =
              some (Cell.scale 2 originalLast) := by
            rw [clearanceRouteEq,
              AxisDirection.unitSubdividePolyline_getLast?
                (by simp [scalePolyline])
                ((originalRouteEq ▸ originalOrthogonal).scalePolyline
                  (factor := 2) (by norm_num))]
            rw [scalePolyline_getLast?, originalLastLookup]
            rfl
          have transformedLast : transformed.getLast? = some target := by
            simp [transformed, shift,
              PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute,
              PeriodicOrthocrossing.translatePolyline, scalePolyline,
              clearanceLast, target,
              PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
              PlanarOneInThree.gadgetScale,
              PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
              Cell.scale_scale]
          have transformedTailLast : transformed.tail.getLast? = some target :=
            List.getLast?_tail_eq_getLast?
              transformedTailHead transformedLast
          have joinedFresh :=
            AxisDirection.LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
              transformedTailFresh routePrefixNe transformedTailLength
              routePrefixOrthogonal transformedTailOrthogonal routePrefixLast
              transformedTailHead transformedTailLast targetNotInPrefix
          have rawShape :
              retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty clauseIndex literalIndex =
                joinAtEndpoint routePrefix transformed.tail := by
            change joinAtEndpoint localRoute
                ((PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
                  clearanceSource clearancePlacement clearanceWidth
                  clearanceDistinct
                  (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                    source sourceLocal sourceWidth sourceOccurrences
                    sourceClausesNonempty)).routes
                  clauseIndex literalIndex) = _
            rw [suffixShape]
            unfold PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
              replacePolylineHead
            exact joinAtEndpoint_assoc_of_middle_ne_nil connectorNe
          rw [rawShape]
          exact joinedFresh

end PeriodicOrthocrossing
end LeanTrominoes
