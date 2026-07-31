import LeanTrominoes.RetainedTerminalCheckpointRasterization
import LeanTrominoes.PlanarThreeSATCornerEqualityCarrierInterface

/-!
# Refined terminal checkpoints at carrier boundaries

A local component route stays on the closed inside of each incident carrier
port, while its carrier lens stays on the closed outside.  These two regions
meet only at the port.  The exact refined checkpoints lie on the discarded
terminal segment, so a checkpoint contact across this boundary can occur
only at one of the terminal endpoints.

The statements below are independent of a particular planar-SAT gadget.
They are the arithmetic bridge from carrier-boundary certificates to the
finite checkpoint certificate for the mixed source-prefix corridor.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

set_option maxHeartbeats 2000000

local macro "solve_terminal_boundary" : tactic =>
  `(tactic|
    simp only [CornerPort.InsideCarrierBoundaryAt,
        CornerPort.OutsideCarrierBoundaryAt,
        CornerPort.InsideCarrierBoundary,
        CornerPort.OutsideCarrierBoundary,
        CornerPort.position,
        retainedTerminalFanTotalRefinement_eq,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        GridSegment.scale,
        GridSegment.Contains,
        GridSegment.IsHorizontal,
        GridSegment.IsVertical,
        GridSegment.Between,
        Cell.add, Cell.sub, Cell.scale,
        Prod.mk.injEq] at * <;>
      omega)

/-- The local carrier boundary with every coordinate multiplied by the
common terminal refinement. -/
def RefinedInsideCarrierBoundaryAt
    (port : CornerPort) (origin point : Cell) : Prop :=
  match port with
  | .west =>
      retainedTerminalFanTotalRefinement * (origin.1 + 1) ≤ point.1 ∧
        (point.1 =
            retainedTerminalFanTotalRefinement * (origin.1 + 1) →
          retainedTerminalFanTotalRefinement * (origin.2 + 6) ≤ point.2)
  | .east =>
      point.1 ≤
          retainedTerminalFanTotalRefinement * (origin.1 + 11) ∧
        (point.1 =
            retainedTerminalFanTotalRefinement * (origin.1 + 11) →
          point.2 ≤
            retainedTerminalFanTotalRefinement * (origin.2 + 6))
  | .south =>
      retainedTerminalFanTotalRefinement * (origin.2 + 1) ≤ point.2 ∧
        (point.2 =
            retainedTerminalFanTotalRefinement * (origin.2 + 1) →
          point.1 ≤
            retainedTerminalFanTotalRefinement * (origin.1 + 6))
  | .north =>
      point.2 ≤
          retainedTerminalFanTotalRefinement * (origin.2 + 11) ∧
        (point.2 =
            retainedTerminalFanTotalRefinement * (origin.2 + 11) →
          retainedTerminalFanTotalRefinement * (origin.1 + 6) ≤ point.1)

/-- The external side of the carrier boundary at the common terminal
refinement. -/
def RefinedOutsideCarrierBoundaryAt
    (port : CornerPort) (origin point : Cell) : Prop :=
  match port with
  | .west =>
      point.1 ≤
          retainedTerminalFanTotalRefinement * (origin.1 + 1) ∧
        (point.1 =
            retainedTerminalFanTotalRefinement * (origin.1 + 1) →
          point.2 ≤
            retainedTerminalFanTotalRefinement * (origin.2 + 6))
  | .east =>
      retainedTerminalFanTotalRefinement * (origin.1 + 11) ≤ point.1 ∧
        (point.1 =
            retainedTerminalFanTotalRefinement * (origin.1 + 11) →
          retainedTerminalFanTotalRefinement * (origin.2 + 6) ≤ point.2)
  | .south =>
      point.2 ≤
          retainedTerminalFanTotalRefinement * (origin.2 + 1) ∧
        (point.2 =
            retainedTerminalFanTotalRefinement * (origin.2 + 1) →
          retainedTerminalFanTotalRefinement * (origin.1 + 6) ≤ point.1)
  | .north =>
      retainedTerminalFanTotalRefinement * (origin.2 + 11) ≤ point.2 ∧
        (point.2 =
            retainedTerminalFanTotalRefinement * (origin.2 + 11) →
          point.1 ≤
            retainedTerminalFanTotalRefinement * (origin.1 + 6))

/-- Every exact checkpoint between two inside terminal endpoints remains
inside the carrier boundary after refinement. -/
theorem retainedTerminalRefinedCheckpoint_insideCarrierBoundary
    (port : CornerPort)
    (origin : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (startInside :
      port.InsideCarrierBoundaryAt origin
        (polylineLastEntrance route))
    (finishInside :
      port.InsideCarrierBoundaryAt origin
        (route.getLastD (0, 0)))
    (point : Cell)
    (checkpoint :
      IsRetainedTerminalRefinedCheckpoint
        route terminal point) :
    RefinedInsideCarrierBoundaryAt port origin point := by
  have startEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  rcases checkpoint with
    ⟨index, indexBound, checkpointEq⟩
  generalize centerEq :
      route.getLastD (0, 0) = center at startEq finishInside checkpointEq
  rw [startEq] at startInside
  rcases origin with ⟨originX, originY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases terminal with ⟨direction, length⟩
  simp only [retainedTerminalSplicePoint] at startInside
  cases direction with
  | compass terminalPort =>
      cases terminalPort <;> cases port <;>
        simp_all [RefinedInsideCarrierBoundaryAt,
          CornerPort.InsideCarrierBoundaryAt,
          CornerPort.InsideCarrierBoundary,
          retainedTerminalFanTotalRefinement_eq,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.sub, Cell.scale,
          Prod.mk.injEq] <;>
        omega
  | routedClause arm =>
      cases arm <;> cases port <;>
        simp_all [RefinedInsideCarrierBoundaryAt,
          CornerPort.InsideCarrierBoundaryAt,
          CornerPort.InsideCarrierBoundary,
          retainedTerminalFanTotalRefinement_eq,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          Cell.add, Cell.sub, Cell.scale,
          Prod.mk.injEq] <;>
        omega

/-- Every point of a refined axis segment whose original endpoints are
outside stays on the refined outside. -/
theorem refinedOutsideCarrierBoundary_of_scale_contains
    (port : CornerPort)
    (origin : Cell)
    (source : GridSegment)
    (sourceStartOutside :
      port.OutsideCarrierBoundaryAt origin source.start)
    (sourceFinishOutside :
      port.OutsideCarrierBoundaryAt origin source.finish)
    (point : Cell)
    (contains :
      (source.scale retainedTerminalFanTotalRefinement).Contains point) :
    RefinedOutsideCarrierBoundaryAt port origin point := by
  rcases origin with ⟨originX, originY⟩
  rcases source with
    ⟨⟨sourceStartX, sourceStartY⟩,
      ⟨sourceFinishX, sourceFinishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  cases port <;>
    simp_all [RefinedOutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      retainedTerminalFanTotalRefinement_eq,
      GridSegment.scale, GridSegment.Contains,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.Between, Cell.sub, Cell.scale] <;>
    omega

/-- The two refined closed sides meet only at the refined physical port. -/
theorem eq_scale_add_position_of_refinedInside_of_refinedOutside
    (port : CornerPort)
    (origin point : Cell)
    (inside :
      RefinedInsideCarrierBoundaryAt port origin point)
    (outside :
      RefinedOutsideCarrierBoundaryAt port origin point) :
    point =
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.add origin port.position) := by
  rcases origin with ⟨originX, originY⟩
  rcases point with ⟨pointX, pointY⟩
  cases port <;>
    simp_all [RefinedInsideCarrierBoundaryAt,
      RefinedOutsideCarrierBoundaryAt,
      CornerPort.position,
      retainedTerminalFanTotalRefinement_eq,
      Cell.add, Cell.scale, Prod.mk.injEq] <;>
    omega

/-- A refined terminal checkpoint equal to the scale of an outside lattice
point, while both terminal endpoints lie inside, must scale one of those
endpoints. -/
theorem
    retainedTerminalRefinedCheckpoint_eq_scaledEndpoint_of_boundary
    (port : CornerPort)
    (origin : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (startInside :
      port.InsideCarrierBoundaryAt origin
        (polylineLastEntrance route))
    (finishInside :
      port.InsideCarrierBoundaryAt origin
        (route.getLastD (0, 0)))
    (point : Cell)
    (pointOutside :
      port.OutsideCarrierBoundaryAt origin point)
    (checkpoint :
      IsRetainedTerminalRefinedCheckpoint
        route terminal
        (Cell.scale retainedTerminalFanTotalRefinement point)) :
    point = polylineLastEntrance route ∨
      point = route.getLastD (0, 0) := by
  have startEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  rcases checkpoint with
    ⟨index, indexBound, checkpointEq⟩
  generalize centerEq :
      route.getLastD (0, 0) = center at startEq finishInside checkpointEq ⊢
  rw [startEq] at startInside ⊢
  rcases origin with ⟨originX, originY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases terminal with ⟨direction, length⟩
  simp only [retainedTerminalSplicePoint] at startInside checkpointEq ⊢
  cases direction with
  | compass terminalPort =>
      cases terminalPort <;> cases port <;>
        solve_terminal_boundary
  | routedClause arm =>
      cases arm <;> cases port <;>
        solve_terminal_boundary

/-- If a scaled outside axis segment contains a refined checkpoint of a
classified terminal whose endpoints are inside the carrier boundary, then
the original outside segment contains one of those endpoints. -/
theorem
    axisSegmentContainsRetainedTerminalRefinedCheckpoint_contains_endpoint_of_boundary
    (port : CornerPort)
    (origin : Cell)
    (source : GridSegment)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (sourceStartOutside :
      port.OutsideCarrierBoundaryAt origin source.start)
    (sourceFinishOutside :
      port.OutsideCarrierBoundaryAt origin source.finish)
    (referenceStartInside :
      port.InsideCarrierBoundaryAt origin
        (polylineLastEntrance route))
    (referenceFinishInside :
      port.InsideCarrierBoundaryAt origin
        (route.getLastD (0, 0)))
    (checkpoint :
      AxisSegmentContainsRetainedTerminalRefinedCheckpoint
        source route terminal) :
    source.Contains (polylineLastEntrance route) ∨
      source.Contains (route.getLastD (0, 0)) := by
  rcases checkpoint with
    ⟨index, indexBound, checkpointContains⟩
  let checkpointPoint :=
    Cell.add
      (Cell.scale retainedTerminalFanTotalRefinement
        (route.getLastD (0, 0)))
      (Cell.scale index terminal.1.primitive)
  have checkpoint' :
      IsRetainedTerminalRefinedCheckpoint
        route terminal checkpointPoint :=
    ⟨index, indexBound, rfl⟩
  have checkpointInside :=
    retainedTerminalRefinedCheckpoint_insideCarrierBoundary
      port origin route terminal routeLength classified
      referenceStartInside referenceFinishInside
      checkpointPoint checkpoint'
  have checkpointOutside :=
    refinedOutsideCarrierBoundary_of_scale_contains
      port origin source sourceStartOutside sourceFinishOutside
      checkpointPoint checkpointContains
  let portPoint := Cell.add origin port.position
  have checkpointEq :
      checkpointPoint =
        Cell.scale retainedTerminalFanTotalRefinement portPoint := by
    exact
      eq_scale_add_position_of_refinedInside_of_refinedOutside
        port origin checkpointPoint checkpointInside checkpointOutside
  have portOutside :
      port.OutsideCarrierBoundaryAt origin portPoint := by
    apply port.outsideCarrierBoundaryAt_add
    cases port <;>
      simp [CornerPort.OutsideCarrierBoundary, CornerPort.position]
  have portCheckpoint :
      IsRetainedTerminalRefinedCheckpoint
        route terminal
        (Cell.scale retainedTerminalFanTotalRefinement portPoint) := by
    rw [← checkpointEq]
    exact checkpoint'
  have endpoint :=
    retainedTerminalRefinedCheckpoint_eq_scaledEndpoint_of_boundary
      port origin route terminal routeLength classified
      referenceStartInside referenceFinishInside
      portPoint portOutside portCheckpoint
  have scaledContains :
      (source.scale retainedTerminalFanTotalRefinement).Contains
        (Cell.scale retainedTerminalFanTotalRefinement portPoint) := by
    rw [← checkpointEq]
    exact checkpointContains
  have sourceContains : source.Contains portPoint :=
    (GridSegment.contains_scale_iff
      (by
        rw [retainedTerminalFanTotalRefinement_eq]
        omega)
      source portPoint).mp scaledContains
  rcases endpoint with portEq | portEq
  · left
    rwa [← portEq]
  · right
    rwa [← portEq]

/-- Opposite carrier-boundary bounds and strict separation of the retained
source prefix from the reference route discharge every refined terminal
checkpoint obligation. -/
theorem sourcePrefixCorridorSeparated_of_outside_insideCarrierBoundary
    (port : CornerPort)
    (origin : Cell)
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceOutside :
      ∀ point ∈ sourceRoute.dropLast,
        port.OutsideCarrierBoundaryAt origin point)
    (referenceInside :
      ∀ point ∈ referenceRoute,
        port.InsideCarrierBoundaryAt origin point)
    (strictlyAvoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        sourceRoute.dropLast referenceRoute) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  have finalMember :
      (⟨polylineLastEntrance referenceRoute,
        referenceRoute.getLastD (0, 0)⟩ : GridSegment) ∈
          gridPolylineSegments referenceRoute :=
    finalGridSegment_mem referenceRoute referenceLength
  have referenceEndpoints :=
    gridPolylineSegments_endpoints_mem finalMember
  have referenceStartInside :=
    referenceInside
      (polylineLastEntrance referenceRoute)
      referenceEndpoints.1
  have referenceFinishInside :=
    referenceInside
      (referenceRoute.getLastD (0, 0))
      referenceEndpoints.2
  apply
    sourcePrefixCorridorSeparated_of_avoids_refinedCheckpoints
      sourceRoute referenceRoute referenceTerminal
      referenceLength referenceClassified
  constructor
  · intro sourcePoint sourcePointMember checkpoint
    have endpoint :=
      retainedTerminalRefinedCheckpoint_eq_scaledEndpoint_of_boundary
        port origin referenceRoute referenceTerminal
        referenceLength referenceClassified
        referenceStartInside referenceFinishInside
        sourcePoint
        (sourceOutside sourcePoint sourcePointMember)
        checkpoint
    rcases endpoint with endpointEq | endpointEq
    · exact
        (strictlyAvoid.2.2.2
          sourcePoint sourcePointMember
          (polylineLastEntrance referenceRoute)
          referenceEndpoints.1)
          endpointEq
    · exact
        (strictlyAvoid.2.2.2
          sourcePoint sourcePointMember
          (referenceRoute.getLastD (0, 0))
          referenceEndpoints.2)
          endpointEq
  · intro sourceSegment sourceSegmentMember checkpoint
    have sourceEndpoints :=
      gridPolylineSegments_endpoints_mem sourceSegmentMember
    have endpointContains :=
      axisSegmentContainsRetainedTerminalRefinedCheckpoint_contains_endpoint_of_boundary
        port origin sourceSegment referenceRoute referenceTerminal
        referenceLength referenceClassified
        (sourceOutside sourceSegment.start sourceEndpoints.1)
        (sourceOutside sourceSegment.finish sourceEndpoints.2)
        referenceStartInside referenceFinishInside checkpoint
    have noContains
        (point : Cell)
        (pointMember : point ∈ referenceRoute)
        (contains : sourceSegment.Contains point) :
        False := by
      rcases
          GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
            contains with
        interior | endpoint
      · exact
          (strictlyAvoid.2.2.1
            point pointMember sourceSegment sourceSegmentMember)
            interior
      · rcases endpoint with atStart | atFinish
        · exact
            (strictlyAvoid.2.2.2
              sourceSegment.start sourceEndpoints.1
              point pointMember)
              atStart.symm
        · exact
            (strictlyAvoid.2.2.2
              sourceSegment.finish sourceEndpoints.2
              point pointMember)
              atFinish.symm
    rcases endpointContains with startContains | finishContains
    · exact noContains
        (polylineLastEntrance referenceRoute)
        referenceEndpoints.1 startContains
    · exact noContains
        (referenceRoute.getLastD (0, 0))
        referenceEndpoints.2 finishContains

end PeriodicEightOccurrenceSplit
end LeanTrominoes
