import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseFanMacrocellSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSeparation

/-!
# Separating corridor cores from coordinated clause fans

A clause fan can reach a neighboring corridor tile only at the final source
step on the same physical lane.  For one occurrence, distinct semantic
strands use distinct physical lanes at that join.  For unequal occurrences,
endpoint-only contact of the source routes prevents every interior tile
center from being the clause target or its final neighbor.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 10000

/-- A one-edge core is the initial point of its coordinated clause fan, so
global clause-fan separation also separates it from every other strand's
clause fan. -/
theorem occurrenceRibbonPairCore_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor)
    (firstStart firstTarget : Cell)
    (firstRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first =
        [firstStart, firstTarget]) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  have stubsAvoid :=
    occurrenceCoordinatedRibbonClauseStubs_strictlyAvoidEachOther
      presentation width compatible different
  have endpointMember :
      ribbonCorridorRouteEnd
          (routedRibbonLane source.erase first firstColor)
          (occurrenceUnitSourceRoute planar first) ∈
        occurrenceCoordinatedRibbonClauseStub
          planar first firstColor :=
    List.mem_of_head?
      (occurrenceCoordinatedRibbonClauseStub_endpoints
        planar width compatible first firstColor).1
  have restricted := stubsAvoid.singleton_left endpointMember
  simpa [occurrenceRibbonCorridorCore, firstRouteEquation,
    ribbonCorridorRouteEnd, ribbonCorridorCoreEnd,
    ribbonCorridorCore, planar] using restricted

/-- A coordinated clause fan avoids one legal tile whose center is neither
its clause target nor the preceding point of its source route. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor)
    (routeLeading : List Cell)
    (before target : Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        routeLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (center : Cell)
    (centerNeTarget : center ≠ target)
    (centerNeBefore : center ≠ before)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry fanColor)
      (ribbonMacrocellRoute center incoming outgoing tileColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  have targetEq : target = occurrenceSourceClauseTarget planar entry := by
    have endpoint :=
      (occurrenceUnitSourceRoute_endpoints planar entry).2
    rw [routeEquation] at endpoint
    simpa [occurrenceSourceClauseTarget] using endpoint
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry fanColor
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      planar clauseIndex entry entry.mem_activeClauseOccurrenceEntries
  have directionEq :
      data.direction group = AxisDirection.between before target := by
    rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
      planar width entry]
    change AxisDirection.polylineLastDirection
        (occurrenceUnitSourceRoute planar entry) =
      AxisDirection.between before target
    rw [routeEquation,
      AxisDirection.polylineLastDirection_append_pair
        routeLeading finalUnit]
  have directionGenuine : (data.direction group).IsGenuine := by
    rw [directionEq]
    exact AxisDirection.between_isGenuine_of_unitAxisStep finalUnit
  have beforeStep :
      before = Cell.add target (data.direction group).opposite.step := by
    have forward :=
      AxisDirection.add_between_step_eq_of_unitAxisStep finalUnit
    rw [← directionEq] at forward
    apply Cell.add_left_injective (data.direction group).step
    calc
      Cell.add (data.direction group).step before =
          Cell.add before (data.direction group).step := by
        rcases before with ⟨beforeX, beforeY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        simp [Cell.add, add_comm]
      _ = target := forward.symm
      _ = Cell.add
          (Cell.add target (data.direction group).opposite.step)
          (data.direction group).step :=
        (AxisDirection.add_opposite_step_add_step
          target directionGenuine).symm
      _ = Cell.add (data.direction group).step
          (Cell.add target (data.direction group).opposite.step) := by
        rcases target with ⟨targetX, targetY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        rcases (data.direction group).opposite.step with ⟨oppositeX, oppositeY⟩
        simp [Cell.add, add_comm]
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent target center with
    centersEqual | centersFar | centersAdjacent
  · exact (centerNeTarget centersEqual.symm).elim
  · rw [targetEq] at centersFar
    exact
      routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
        (fun point member =>
          occurrenceCoordinatedRibbonClauseStub_points_bounded
            planar compatible entry fanColor member)
        (fun point member =>
          ribbonMacrocellRoute_points_bounded
            center incoming outgoing tileColor point member)
        centersFar
  · let offset := Cell.sub center target
    have centerEq : center = Cell.add target offset := by
      rcases target with ⟨targetX, targetY⟩
      rcases center with ⟨centerX, centerY⟩
      simp [offset, Cell.add, Cell.sub]
    have offsetNe : offset ≠ (data.direction group).opposite.step := by
      intro offsetEq
      apply centerNeBefore
      calc
        center = Cell.add target offset := centerEq
        _ = Cell.add target (data.direction group).opposite.step := by
          rw [offsetEq]
        _ = before := beforeStep.symm
    have localAvoid :=
      data.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
        (compatible.2 entry) group active lane offset centersAdjacent
        incoming outgoing incomingGenuine outgoingGenuine noReverse tileColor
        ⟨Or.inl offsetNe, Or.inl offsetNe⟩
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin target)
    have tileTranslation :
        translatePolyline (ribbonMacrocellOrigin target)
            (ribbonMacrocellRoute offset incoming outgoing tileColor) =
          ribbonMacrocellRoute center incoming outgoing tileColor := by
      unfold translatePolyline
      rw [← ribbonMacrocellRoute_add_center]
      rw [← centerEq]
    rw [tileTranslation] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonClauseStub, targetEq,
      planar, clauseIndex, data, group, lane] using translatedAvoid

/-- At the final source tile, distinct physical lanes remove the sole
possible tile/fan contact. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_finalRibbonMacrocellRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor tileSemanticColor : WireColor)
    (colorsDifferent : fanColor ≠ tileSemanticColor)
    (routeLeading : List Cell)
    (previous before target : Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        routeLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (previousUnit : AxisDirection.IsUnitAxisStep previous before)
    (noReverse :
      AxisDirection.between before target ≠
        (AxisDirection.between previous before).opposite) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry fanColor)
      (ribbonMacrocellRoute before
        (AxisDirection.between previous before)
        (AxisDirection.between before target)
        (routedRibbonLane source.erase entry tileSemanticColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  have targetEq : target = occurrenceSourceClauseTarget planar entry := by
    have endpoint :=
      (occurrenceUnitSourceRoute_endpoints planar entry).2
    rw [routeEquation] at endpoint
    simpa [occurrenceSourceClauseTarget] using endpoint
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  let group := occurrenceClauseTerminalGroup source.erase entry
  let fanLane := routedRibbonLane source.erase entry fanColor
  let tileLane := routedRibbonLane source.erase entry tileSemanticColor
  let offset := Cell.sub before target
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      planar clauseIndex entry entry.mem_activeClauseOccurrenceEntries
  have directionEq :
      data.direction group = AxisDirection.between before target := by
    rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
      planar width entry]
    change AxisDirection.polylineLastDirection
        (occurrenceUnitSourceRoute planar entry) =
      AxisDirection.between before target
    rw [routeEquation,
      AxisDirection.polylineLastDirection_append_pair
        routeLeading finalUnit]
  have directionGenuine : (data.direction group).IsGenuine := by
    rw [directionEq]
    exact AxisDirection.between_isGenuine_of_unitAxisStep finalUnit
  have beforeStep :
      before = Cell.add target (data.direction group).opposite.step := by
    have forward :=
      AxisDirection.add_between_step_eq_of_unitAxisStep finalUnit
    rw [← directionEq] at forward
    apply Cell.add_left_injective (data.direction group).step
    calc
      Cell.add (data.direction group).step before =
          Cell.add before (data.direction group).step := by
        rcases before with ⟨beforeX, beforeY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        simp [Cell.add, add_comm]
      _ = target := forward.symm
      _ = Cell.add
          (Cell.add target (data.direction group).opposite.step)
          (data.direction group).step :=
        (AxisDirection.add_opposite_step_add_step
          target directionGenuine).symm
      _ = Cell.add (data.direction group).step
          (Cell.add target (data.direction group).opposite.step) := by
        rcases target with ⟨targetX, targetY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        rcases (data.direction group).opposite.step with ⟨oppositeX, oppositeY⟩
        simp [Cell.add, add_comm]
  have offsetEq : offset = (data.direction group).opposite.step := by
    have reconstruct : before = Cell.add target offset := by
      rcases target with ⟨targetX, targetY⟩
      rcases before with ⟨beforeX, beforeY⟩
      simp [offset, Cell.add, Cell.sub]
    apply Cell.add_left_injective target
    calc
      Cell.add target offset = before := reconstruct.symm
      _ = Cell.add target (data.direction group).opposite.step := beforeStep
  have adjacent : RibbonMacrocellOffsetAdjacent offset := by
    rw [offsetEq]
    have oppositeAdjacent :
        ∀ direction : AxisDirection, direction.IsGenuine →
          RibbonMacrocellOffsetAdjacent direction.opposite.step := by
      decide
    exact oppositeAdjacent (data.direction group) directionGenuine
  have lanesDifferent : fanLane ≠ tileLane :=
    (routedRibbonLane_injective source.erase entry).ne colorsDifferent
  have localAvoid :=
    data.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
      (compatible.2 entry) group active fanLane offset adjacent
      (AxisDirection.between previous before)
      (AxisDirection.between before target)
      (AxisDirection.between_isGenuine_of_unitAxisStep previousUnit)
      (AxisDirection.between_isGenuine_of_unitAxisStep finalUnit)
      noReverse tileLane
      ⟨Or.inr directionEq.symm, Or.inr lanesDifferent⟩
  have translatedAvoid :=
    localAvoid.translatePolyline (ribbonMacrocellOrigin target)
  have centerEq : before = Cell.add target offset := by
    rcases target with ⟨targetX, targetY⟩
    rcases before with ⟨beforeX, beforeY⟩
    simp [offset, Cell.add, Cell.sub]
  have tileTranslation :
      translatePolyline (ribbonMacrocellOrigin target)
          (ribbonMacrocellRoute offset
            (AxisDirection.between previous before)
            (AxisDirection.between before target) tileLane) =
        ribbonMacrocellRoute before
          (AxisDirection.between previous before)
          (AxisDirection.between before target) tileLane := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center]
    rw [← centerEq]
  rw [tileTranslation] at translatedAvoid
  simpa [occurrenceCoordinatedRibbonClauseStub, targetEq,
    planar, clauseIndex, data, group, fanLane, tileLane] using translatedAvoid

/-- A duplicate-free corridor ending in the advertised clause edge avoids
the clause fan on every different semantic strand.  Induction peels tiles
from the variable side; the base case is exactly the final tile handled
above. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonCorridorCore_append_pair
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor tileSemanticColor : WireColor)
    (colorsDifferent : fanColor ≠ tileSemanticColor)
    (sourceLeading : List Cell)
    (before target : Cell)
    (sourceRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        sourceLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (first : Cell)
    (rest : List Cell)
    (unitSteps :
      ((first :: rest) ++ [before, target]).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        ((first :: rest) ++ [before, target]))
    (nodup : ((first :: rest) ++ [before, target]).Nodup) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry fanColor)
      (ribbonCorridorCore
        (routedRibbonLane source.erase entry tileSemanticColor)
        ((first :: rest) ++ [before, target])) := by
  induction rest generalizing first with
  | nil =>
      have displayedUnitSteps :
          (first :: before :: target :: []).IsChain
            AxisDirection.IsUnitAxisStep := by
        simpa using unitSteps
      have parts := unitSteps_cons_cons_cons displayedUnitSteps
      have displayedNoReversal :
          SourceRouteHasNoImmediateReversal
            (first :: before :: target :: []) := by
        simpa using noReversal
      rw [show
        ([first] ++ [before, target]) =
          first :: before :: target :: [] by rfl,
        ribbonCorridorCore]
      exact
        occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_finalRibbonMacrocellRoute
          presentation width compatible entry fanColor tileSemanticColor
          colorsDifferent sourceLeading first before target
          sourceRouteEquation finalUnit parts.1 displayedNoReversal.1
  | cons second remaining tailInduction =>
      cases remaining with
      | nil =>
          have displayedUnitSteps :
              (first :: second :: before :: target :: []).IsChain
                AxisDirection.IsUnitAxisStep := by
            simpa using unitSteps
          have parts := unitSteps_cons_cons_cons displayedUnitSteps
          have displayedNoReversal :
              SourceRouteHasNoImmediateReversal
                (first :: second :: before :: target :: []) := by
            simpa using noReversal
          have displayedNodup :
              (first :: second :: before :: target :: []).Nodup := by
            simpa using nodup
          have secondFresh : second ∉ [before, target] :=
            (List.nodup_cons.mp
              (List.nodup_cons.mp displayedNodup).2).1
          have secondNeBefore : second ≠ before := by
            simpa using (show second ≠ before ∧ second ≠ target by
              simpa using secondFresh).1
          have secondNeTarget : second ≠ target := by
            simpa using (show second ≠ before ∧ second ≠ target by
              simpa using secondFresh).2
          have headAvoid :=
            occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
              presentation width compatible entry fanColor
              sourceLeading before target sourceRouteEquation finalUnit
              second secondNeTarget secondNeBefore
              (AxisDirection.between first second)
              (AxisDirection.between second before)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
              displayedNoReversal.1
              (routedRibbonLane source.erase entry tileSemanticColor)
          have tailAvoid :=
            tailInduction second parts.2.2 displayedNoReversal.2
              (List.nodup_cons.mp displayedNodup).2
          have shared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep
              parts.2.1
              (routedRibbonLane source.erase entry tileSemanticColor)
          rw [show
            ((first :: second :: []) ++ [before, target]) =
              first :: second :: before :: target :: [] by rfl,
            ribbonCorridorCore]
          apply headAvoid.join_right tailAvoid
            (ribbonMacrocellRoute_getLast? second
              (AxisDirection.between first second)
              (AxisDirection.between second before)
              (routedRibbonLane source.erase entry tileSemanticColor))
          rw [shared]
          exact ribbonCorridorCore_head?
            (routedRibbonLane source.erase entry tileSemanticColor)
            second before target []
      | cons third remaining =>
          have displayedUnitSteps :
              (first :: second :: third ::
                (remaining ++ [before, target])).IsChain
                  AxisDirection.IsUnitAxisStep := by
            simpa using unitSteps
          have parts := unitSteps_cons_cons_cons displayedUnitSteps
          have displayedNoReversal :
              SourceRouteHasNoImmediateReversal
                (first :: second :: third ::
                  (remaining ++ [before, target])) := by
            simpa using noReversal
          have displayedNodup :
              (first :: second :: third ::
                (remaining ++ [before, target])).Nodup := by
            simpa using nodup
          have secondFresh :
              second ∉ third :: (remaining ++ [before, target]) :=
            (List.nodup_cons.mp
              (List.nodup_cons.mp displayedNodup).2).1
          have secondNeBefore : second ≠ before := by
            intro equal
            apply secondFresh
            simp [equal]
          have secondNeTarget : second ≠ target := by
            intro equal
            apply secondFresh
            simp [equal]
          have headAvoid :=
            occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
              presentation width compatible entry fanColor
              sourceLeading before target sourceRouteEquation finalUnit
              second secondNeTarget secondNeBefore
              (AxisDirection.between first second)
              (AxisDirection.between second third)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
              displayedNoReversal.1
              (routedRibbonLane source.erase entry tileSemanticColor)
          have tailAvoid :=
            tailInduction second parts.2.2 displayedNoReversal.2
              (List.nodup_cons.mp displayedNodup).2
          have shared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep
              parts.2.1
              (routedRibbonLane source.erase entry tileSemanticColor)
          have assembled :=
            headAvoid.join_right tailAvoid
              (ribbonMacrocellRoute_getLast? second
                (AxisDirection.between first second)
                (AxisDirection.between second third)
                (routedRibbonLane source.erase entry tileSemanticColor))
              (by
                rw [shared]
                cases remaining with
                | nil =>
                    simpa using ribbonCorridorCore_head?
                      (routedRibbonLane source.erase entry tileSemanticColor)
                      second third before [target]
                | cons fourth remaining =>
                    simpa using ribbonCorridorCore_head?
                      (routedRibbonLane source.erase entry tileSemanticColor)
                      second third fourth (remaining ++ [before, target]))
          cases remaining with
          | nil =>
              simpa [ribbonCorridorCore] using assembled
          | cons fourth remaining =>
              simpa [ribbonCorridorCore] using assembled

/-- If every displayed interior center of a source route differs from a
clause target and its final neighbor, the corresponding complete corridor
core strictly avoids that clause fan. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor)
    (routeLeading : List Cell)
    (before target : Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        routeLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (secondRoute : List Cell)
    (interiorCentersNe :
      ∀ (leading : List Cell) (previous center next : Cell)
        (rest : List Cell),
        secondRoute = leading ++ previous :: center :: next :: rest →
          center ≠ target ∧ center ≠ before)
    (secondLeading : List Cell)
    (secondPrevious secondCenter secondNext : Cell)
    (secondRest : List Cell)
    (secondRouteEquation :
      secondRoute = secondLeading ++
        secondPrevious :: secondCenter :: secondNext :: secondRest)
    (secondUnitSteps :
      (secondPrevious :: secondCenter :: secondNext :: secondRest).IsChain
        AxisDirection.IsUnitAxisStep)
    (secondNoReversal :
      SourceRouteHasNoImmediateReversal
        (secondPrevious :: secondCenter :: secondNext :: secondRest))
    (secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry fanColor)
      (ribbonCorridorCore secondColor
        (secondPrevious :: secondCenter :: secondNext :: secondRest)) := by
  induction secondRest generalizing
      secondLeading secondPrevious secondCenter secondNext with
  | nil =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons secondUnitSteps
      have centersNe :=
        interiorCentersNe secondLeading secondPrevious
          secondCenter secondNext [] secondRouteEquation
      exact
        occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation width compatible entry fanColor
          routeLeading before target routeEquation finalUnit
          secondCenter centersNe.1 centersNe.2
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          secondNoReversal.1 secondColor
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons secondUnitSteps
      have centersNe :=
        interiorCentersNe secondLeading secondPrevious
          secondCenter secondNext (fourth :: rest) secondRouteEquation
      have headAvoid :=
        occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation width compatible entry fanColor
          routeLeading before target routeEquation finalUnit
          secondCenter centersNe.1 centersNe.2
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          secondNoReversal.1 secondColor
      have tailRouteEquation :
          secondRoute = (secondLeading ++ [secondPrevious]) ++
            secondCenter :: secondNext :: fourth :: rest := by
        calc
          secondRoute = secondLeading ++ secondPrevious :: secondCenter ::
              secondNext :: fourth :: rest := secondRouteEquation
          _ = (secondLeading ++ [secondPrevious]) ++
              secondCenter :: secondNext :: fourth :: rest := by simp
      have tailAvoid :=
        tailInduction (secondLeading ++ [secondPrevious])
          secondCenter secondNext fourth tailRouteEquation
          parts.2.2 secondNoReversal.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep parts.2.1 secondColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext) secondColor)
      rw [shared]
      exact ribbonCorridorCore_head? secondColor
        secondCenter secondNext fourth rest

/-- Every corridor core strictly avoids the coordinated clause-side stub of
a different colored strand.  This is the `coreClause` obligation for the
coordinated endpoint-fan system. -/
theorem occurrenceRibbonCorridorCore_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  by_cases sameOccurrence : first = second
  · subst second
    have colorsDifferent : firstColor ≠ secondColor := by
      intro colorsEqual
      exact different (Prod.ext rfl colorsEqual)
    let route := occurrenceUnitSourceRoute planar first
    have routeLength : 2 ≤ route.length := by
      simpa [route] using occurrenceUnitSourceRoute_length planar first
    have routeUnitSteps :
        route.IsChain AxisDirection.IsUnitAxisStep := by
      simpa [route] using occurrenceUnitSourceRoute_unitSteps planar first
    rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
        routeLength with
      ⟨leading, before, target, routeEquation⟩
    have actualRouteEquation :
        occurrenceUnitSourceRoute planar first =
          leading ++ [before, target] := by
      simpa [route] using routeEquation
    have finalUnit : AxisDirection.IsUnitAxisStep before target := by
      rw [routeEquation] at routeUnitSteps
      exact (List.isChain_append_cons_cons.mp routeUnitSteps).2.1
    cases leading with
    | nil =>
        exact
          occurrenceRibbonPairCore_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
            presentation width compatible different before target
            (by simpa using actualRouteEquation)
    | cons firstPoint rest =>
        have displayedUnitSteps :
            ((firstPoint :: rest) ++ [before, target]).IsChain
              AxisDirection.IsUnitAxisStep := by
          rw [← actualRouteEquation]
          exact occurrenceUnitSourceRoute_unitSteps planar first
        have displayedNoReversal :
            SourceRouteHasNoImmediateReversal
              ((firstPoint :: rest) ++ [before, target]) := by
          rw [← actualRouteEquation]
          exact occurrenceUnitSourceRoute_hasNoImmediateReversal
            presentation.toContinuousPlanarIncidencePresentation first
        have displayedNodup :
            ((firstPoint :: rest) ++ [before, target]).Nodup := by
          rw [← actualRouteEquation]
          exact occurrenceUnitSourceRoute_nodup presentation first
        have avoid :=
          occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonCorridorCore_append_pair
            presentation width compatible first secondColor firstColor
            colorsDifferent.symm (firstPoint :: rest) before target
            actualRouteEquation finalUnit firstPoint rest
            displayedUnitSteps displayedNoReversal displayedNodup
        change RoutesStrictlyAvoidEachOther
          (ribbonCorridorCore
            (routedRibbonLane source.erase first firstColor)
            (occurrenceUnitSourceRoute planar first))
          (occurrenceCoordinatedRibbonClauseStub planar first secondColor)
        rw [actualRouteEquation]
        simpa using avoid.symm
  · let firstRoute := occurrenceUnitSourceRoute planar first
    let secondRoute := occurrenceUnitSourceRoute planar second
    have firstLength : 2 ≤ firstRoute.length := by
      simpa [firstRoute] using occurrenceUnitSourceRoute_length planar first
    have secondLength : 2 ≤ secondRoute.length := by
      simpa [secondRoute] using occurrenceUnitSourceRoute_length planar second
    have secondUnitSteps :
        secondRoute.IsChain AxisDirection.IsUnitAxisStep := by
      simpa [secondRoute] using occurrenceUnitSourceRoute_unitSteps planar second
    rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
        secondLength with
      ⟨secondLeading, secondBefore, secondTarget, secondEquation⟩
    have secondRouteEquation :
        occurrenceUnitSourceRoute planar second =
          secondLeading ++ [secondBefore, secondTarget] := by
      simpa [secondRoute] using secondEquation
    have secondFinalUnit :
        AxisDirection.IsUnitAxisStep secondBefore secondTarget := by
      rw [secondEquation] at secondUnitSteps
      exact (List.isChain_append_cons_cons.mp secondUnitSteps).2.1
    cases firstEquation : firstRoute with
    | nil =>
        simp [firstEquation] at firstLength
    | cons firstStart firstTail =>
        cases firstTail with
        | nil =>
            simp [firstEquation] at firstLength
        | cons firstNext firstRest =>
            have firstRouteEquation :
                occurrenceUnitSourceRoute planar first =
                  firstStart :: firstNext :: firstRest := by
              simpa [firstRoute] using firstEquation
            cases firstRest with
            | nil =>
                exact
                  occurrenceRibbonPairCore_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
                    presentation width compatible different
                    firstStart firstNext firstRouteEquation
            | cons firstThird firstRest =>
                have firstNodup : firstRoute.Nodup := by
                  simpa [firstRoute] using
                    occurrenceUnitSourceRoute_nodup presentation first
                have meetOnly :
                    RoutesMeetOnlyAtEndpoints firstRoute secondRoute := by
                  simpa [firstRoute, secondRoute, planar] using
                    occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
                      presentation sameOccurrence
                have secondBeforeMember : secondBefore ∈ secondRoute := by
                  rw [secondEquation]
                  simp
                have secondTargetMember : secondTarget ∈ secondRoute := by
                  rw [secondEquation]
                  simp
                have interiorCentersNe :
                    ∀ (leading : List Cell)
                      (previous center next : Cell)
                      (remaining : List Cell),
                      firstRoute = leading ++
                          previous :: center :: next :: remaining →
                        center ≠ secondTarget ∧
                          center ≠ secondBefore := by
                  intro leading previous center next remaining equation
                  have centerMember : center ∈ firstRoute := by
                    rw [equation]
                    simp
                  have centerInternal :
                      ¬RoutePointIsEndpoint firstRoute center :=
                    routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                      equation firstNodup
                  constructor
                  · exact
                      routePoints_ne_of_routesMeetOnlyAtEndpoints
                        meetOnly centerMember secondTargetMember
                        (Or.inl centerInternal)
                  · exact
                      routePoints_ne_of_routesMeetOnlyAtEndpoints
                        meetOnly centerMember secondBeforeMember
                        (Or.inl centerInternal)
                have firstUnitSteps :
                    (firstStart :: firstNext :: firstThird ::
                      firstRest).IsChain
                        AxisDirection.IsUnitAxisStep := by
                  rw [← firstRouteEquation]
                  exact occurrenceUnitSourceRoute_unitSteps planar first
                have firstNoReversal :
                    SourceRouteHasNoImmediateReversal
                      (firstStart :: firstNext :: firstThird :: firstRest) := by
                  rw [← firstRouteEquation]
                  exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                    presentation.toContinuousPlanarIncidencePresentation first
                have avoid :=
                  occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
                    presentation width compatible second secondColor
                    secondLeading secondBefore secondTarget
                    secondRouteEquation secondFinalUnit
                    firstRoute interiorCentersNe []
                    firstStart firstNext firstThird firstRest
                    (by simpa [firstRoute] using firstEquation)
                    firstUnitSteps firstNoReversal
                    (routedRibbonLane source.erase first firstColor)
                change RoutesStrictlyAvoidEachOther
                  (ribbonCorridorCore
                    (routedRibbonLane source.erase first firstColor)
                    (occurrenceUnitSourceRoute planar first))
                  (occurrenceCoordinatedRibbonClauseStub
                    planar second secondColor)
                rw [firstRouteEquation]
                exact avoid.symm

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
