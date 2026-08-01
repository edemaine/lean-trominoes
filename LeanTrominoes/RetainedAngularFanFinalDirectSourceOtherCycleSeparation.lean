import LeanTrominoes.RetainedAngularFanFinalFallbackCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final direct occurrences avoid cycles at other source centers

The direct-source atlas replaces a two-point source incidence by a
coordinated outer fan.  A finite certificate bounds every such replacement
inside the radius-288 expansion of the fully refined source segment.  This
lets the retained source drawing's vertex/segment separation clear every
cycle centered at a different source atom.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every finite direct-source atlas route stays within the radius-288
expansion of its fully refined two-point local source segment. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

/-- The original positioned two-point source segment represented by a
successful direct-source choice. -/
def RetainedDirectSourceRouteChoice.sourceSegment
    (choice : RetainedDirectSourceRouteChoice) :
    GridSegment :=
  ⟨Cell.add choice.origin
      ((retainedDirectSourceLocalRouteAt
        choice.kind choice.index).headD (0, 0)),
    Cell.add choice.origin
      ((retainedDirectSourceLocalRouteAt
        choice.kind choice.index).getLastD (0, 0))⟩

/-- The common coordinate calculation transporting any local atlas point
bound through a choice's physical component translation. -/
private theorem
    RetainedDirectSourceRouteChoice.translatedPoint_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (localPoint : Cell)
    (localBound :
      let localSegment : GridSegment :=
        ⟨(retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0)⟩
      InClosedGridRectangle
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            localSegment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            localSegment.coordinateUpper))
        localPoint) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      (Cell.add
        (retainedDirectSourceFanPositioningOffset choice.origin)
        localPoint) := by
  let localSegment : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt
        choice.kind choice.index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt
        choice.kind choice.index).getLastD (0, 0)⟩
  let positioningOffset :=
    retainedDirectSourceFanPositioningOffset choice.origin
  have lowerEq :
      Cell.add positioningOffset
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower)) =
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateLower, coordinateRadiusLower,
      Cell.add, Cell.scale,
      min_add_add_left]
    constructor <;> ring
  have upperEq :
      Cell.add positioningOffset
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper)) =
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateUpper, coordinateRadiusUpper,
      Cell.add, Cell.scale,
      max_add_add_left]
    constructor <;> ring
  rw [← lowerEq, ← upperEq]
  simpa [localSegment, positioningOffset] using
    PeriodicOrthocrossing.InClosedGridRectangle.add localBound
      positioningOffset

/-- Positioning a direct atlas choice transports its finite radius-288
bound to the fully refined represented source segment. -/
theorem RetainedDirectSourceRouteChoice.completeRoute_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
    translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle
      choice.kind choice.index slot localPoint localPointMember
  exact choice.translatedPoint_in_sourceSegmentRectangle
    localPoint localBound

/-- The local Figure 7 spoke appended to a direct route stays inside the
same conservative source-segment rectangle. -/
theorem
    retainedDirectSourceFigure7SpokeAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFigure7SpokeAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

/-- The positioned direct Figure 7 spoke inherits the same source-segment
rectangle. -/
theorem RetainedDirectSourceRouteChoice.figure7Spoke_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.figure7Spoke slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  unfold RetainedDirectSourceRouteChoice.figure7Spoke
    translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  exact choice.translatedPoint_in_sourceSegmentRectangle
    localPoint
    (retainedDirectSourceFigure7SpokeAt_point_in_scaledLocalSegmentRectangle
      choice.kind choice.index slot localPoint localPointMember)

/-- The direct source prefix joined to its matching Figure 7 spoke stays
inside the same source-segment rectangle. -/
theorem
    RetainedDirectSourceRouteChoice.completeFigure7Route_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.completeFigure7Route slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  rcases mem_joinAtEndpoint pointMember with
    prefixMember | spokeMember
  · exact choice.completeRoute_point_in_sourceSegmentRectangle
      slot prefixMember
  · exact choice.figure7Spoke_point_in_sourceSegmentRectangle
      slot spokeMember

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- If the represented direct source-segment rectangle is separated from a
cycle metadata center, the complete direct occurrence is strictly separated
from that flattened cycle route. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
        (coordinateRadiusLower 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
        (coordinateRadiusUpper 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  have routeEqual :=
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  rw [routeEqual]
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
      (secondUpper :=
        coordinateRadiusUpper 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
  · intro point pointMember
    exact
      choice.completeFigure7Route_point_in_sourceSegmentRectangle
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)
        pointMember
  · intro point pointMember
    exact
      retainedFinalSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
        formula metadataLookup cycleLiteralIndex pointMember
  · exact rectanglesSeparated

/-- A successful direct occurrence avoids a flattened cycle route at the
same canonical source center. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  have routeEqual :=
    retainedFinalScaledAllCycleRoute_eq_matchingCycleLift_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadataLookup cycleLiteralIndex
      (centersEqual metadata metadataLookup)
  have localClauseIndexLt :
      metadata.localClauseIndex <
        presentedCycleVertices.length :=
    positionedCycleClause_localIndex_lt
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember
  have localLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using cycleLiteralMember
  have cycleLiteralIndexLt :
      cycleLiteralIndex < 2 :=
    positionedCycleClause_literalIndex_lt_two
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember localLiteralMember
  have avoids :=
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_matchingCycleLift
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadata.localClauseIndex cycleLiteralIndex
      localClauseIndexLt cycleLiteralIndexLt
  dsimp only at avoids
  rw [routeEqual]
  exact avoids

/-- The public coordinated route selected by a successful direct choice
inherits the same-center cycle certificate. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      cycleClauseMember cycleLiteralMember centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
