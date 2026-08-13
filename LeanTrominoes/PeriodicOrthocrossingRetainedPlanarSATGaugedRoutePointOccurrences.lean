/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences
import LeanTrominoes.PeriodicGridDrawingEndpointContacts
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage

/-!
# Physical representatives of gauged retained route-point occurrences

The final periodic quotient stores bend points as well as segments.  Before
the drawing can be thickened into ribbons, a coincident pair of such listed
points must be transferred back to the finite retained drawing without
losing either route index or endpoint status.

This file refines the existing segment-occurrence witness to one indexed
route point.  A fixed first segment of the same route carries the already
proved quotient-index correspondence, while equality of translated whole
routes identifies the point at its unchanged within-route index.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Translating equal polylines identifies their points at every common
syntactic point index. -/
private theorem exists_point_of_translatePolyline_eq
    {source target : List Cell}
    {sourceOffset targetOffset : Cell}
    {point : Cell}
    {pointIndex : Nat}
    (pointMember :
      (point, pointIndex) ∈ source.zipIdx)
    (routeEq :
      translatePolyline sourceOffset source =
        translatePolyline targetOffset target) :
    ∃ targetPoint : Cell,
      (targetPoint, pointIndex) ∈ target.zipIdx ∧
        Cell.add sourceOffset point =
          Cell.add targetOffset targetPoint := by
  have translatedMember :
      (Cell.add sourceOffset point, pointIndex) ∈
        (translatePolyline sourceOffset source).zipIdx := by
    rw [translatePolyline, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(point, pointIndex), pointMember, rfl⟩
  rw [routeEq, translatePolyline, List.zipIdx_map] at translatedMember
  rcases List.mem_map.mp translatedMember with
    ⟨taggedTarget, taggedTargetMember, taggedTargetEq⟩
  rcases taggedTarget with ⟨targetPoint, targetIndex⟩
  have indexEq : targetIndex = pointIndex :=
    congrArg Prod.snd taggedTargetEq
  have pointEq :
      Cell.add targetOffset targetPoint =
        Cell.add sourceOffset point :=
    congrArg Prod.fst taggedTargetEq
  refine ⟨targetPoint, ?_, pointEq.symm⟩
  simpa only [indexEq] using taggedTargetMember

/-- The segment at index zero of a route, tagged with the route index of a
listed point.  Every final incidence route is nondegenerate, so the segment
exists whenever the point is listed. -/
def firstSegmentForRoutePoint
    (indexed : IndexedRoutePoint)
    (segment : GridSegment) :
    IndexedGridSegment where
  routeIndex := indexed.routeIndex
  segmentIndex := 0
  segment := segment

/-- The final periodic drawing and its positioned placement use the same
physical translation for every lattice shift. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_periodTranslation_eq_placement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (shift : Cell) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).periodTranslation shift =
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation shift := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq : drawing.gridSize = placement.period := by
    simpa [drawing, placement,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
      using
        PositionedPeriodicCNF.incidenceDrawing_gridSize
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          periodPositive
  change
    Cell.scale (drawing.gridSize : Int) shift =
      Cell.scale (placement.period : Int) shift
  rw [gridSizeEq]

/-- A final listed route-point occurrence and its same-indexed point in one
translated finite retained route.  The first segment witness supplies an
injective bridge between final and physical route-occurrence identities. -/
structure FinalGaugedRoutePointOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedRoutePoint)
    (shift : Cell) where
  finalRoute : List Cell
  finalRouteMember :
    (finalRoute, indexed.routeIndex) ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).edgeRoutes.zipIdx
  finalPointMember :
    (indexed.point, indexed.pointIndex) ∈ finalRoute.zipIdx
  finalRouteLengthEq :
    finalRoute.length = indexed.routeLength
  firstSegment : GridSegment
  firstSegmentMember :
    (firstSegment, 0) ∈
      (gridPolylineSegments finalRoute).zipIdx
  firstIndexedMember :
    firstSegmentForRoutePoint indexed firstSegment ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).indexedSegments
  segmentWitness :
    FinalGaugedSegmentOccurrenceWitness
      formula (firstSegmentForRoutePoint indexed firstSegment) shift
  segmentWitnessFinalRouteEq :
    segmentWitness.finalRoute = finalRoute
  physicalPoint : Cell
  physicalPointMember :
    (physicalPoint, indexed.pointIndex) ∈
      ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
        (metadataPhysicalIncidence
          segmentWitness.routeWitness.metadata
          segmentWitness.routeWitness.metadataIndex
          segmentWitness.routeWitness.literal
          segmentWitness.taggedLiteral.2)).zipIdx
  physicalRouteLengthEq :
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
        (metadataPhysicalIncidence
          segmentWitness.routeWitness.metadata
          segmentWitness.routeWitness.metadataIndex
          segmentWitness.routeWitness.literal
          segmentWitness.taggedLiteral.2)).length =
      indexed.routeLength
  pointEq :
    Cell.add indexed.point
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift) =
      Cell.add physicalPoint
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation segmentWitness.physicalShift)

/-- Every listed point in a genuine final route occurrence has a
same-indexed representative in a translated finite retained route. -/
theorem
    exists_retainedPhysicalPoint_of_finalRoutePointOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (indexed : IndexedRoutePoint)
    (indexedMember :
      indexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedRoutePoints)
    (shift : Cell) :
    Nonempty
      (FinalGaugedRoutePointOccurrenceWitness
        formula indexed shift) := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  unfold PeriodicGridDrawing.indexedRoutePoints at indexedMember
  rcases List.mem_flatMap.mp indexedMember with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedPoint, taggedPointMember, indexedEq⟩
  subst indexed
  have routeMember : taggedRoute.1 ∈ drawing.edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMember
  have compatible :
      drawing.IsCompatible
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceGraph := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal clausesNonempty
  have routeLength : 2 ≤ taggedRoute.1.length := by
    exact
      PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceGraph
        drawing compatible
        (PeriodicCNF.incidenceGraph_edgesAreLoopless
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase)
        routeMember
  have firstSegmentIndexLt :
      0 < (gridPolylineSegments taggedRoute.1).length := by
    rw [gridPolylineSegments_length]
    omega
  let firstSegment :=
    (gridPolylineSegments taggedRoute.1)[0]
  have firstSegmentMember :
      (firstSegment, 0) ∈
        (gridPolylineSegments taggedRoute.1).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨firstSegmentIndexLt, rfl⟩
  let firstIndexed :=
    firstSegmentForRoutePoint
      ({ routeIndex := taggedRoute.2
         pointIndex := taggedPoint.2
         routeLength := taggedRoute.1.length
         point := taggedPoint.1 } : IndexedRoutePoint)
      firstSegment
  have firstIndexedMember : firstIndexed ∈ drawing.indexedSegments := by
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨taggedRoute, taggedRouteMember, ?_⟩
    exact List.mem_map.mpr
      ⟨(firstSegment, 0), firstSegmentMember, rfl⟩
  rcases
      exists_retainedPhysicalSegment_of_finalSegmentOccurrence
        formula wellFormed degree isLocal clausesNonempty
        firstIndexed (by simpa only [drawing] using firstIndexedMember)
        shift with
    ⟨segmentWitness⟩
  have segmentWitnessFinalRouteEq :
      segmentWitness.finalRoute = taggedRoute.1 := by
    have witnessLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        segmentWitness.finalRouteMember
    have routeLookup :=
      (List.mem_zipIdx_iff_getElem?).mp taggedRouteMember
    exact Option.some.inj
      (witnessLookup.symm.trans routeLookup)
  have routeOccurrenceEq :
      translatePolyline
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).translation shift)
          taggedRoute.1 =
        metadataPhysicalRouteOccurrence
          formula
          segmentWitness.routeWitness.metadata
          segmentWitness.routeWitness.metadataIndex
          segmentWitness.routeWitness.literal
          segmentWitness.taggedLiteral.2 shift := by
    calc
      translatePolyline
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).translation shift)
          taggedRoute.1 =
        translatePolyline
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).translation shift)
          segmentWitness.finalRoute := by
            rw [segmentWitnessFinalRouteEq]
      _ =
        finalGaugedRouteOccurrence
          formula segmentWitness.taggedClause.2
            segmentWitness.taggedLiteral.2 shift := by
          unfold finalGaugedRouteOccurrence
          rw [segmentWitness.finalRouteEq]
      _ =
        metadataPhysicalRouteOccurrence
          formula
          segmentWitness.routeWitness.metadata
          segmentWitness.routeWitness.metadataIndex
          segmentWitness.routeWitness.literal
          segmentWitness.taggedLiteral.2 shift :=
        segmentWitness.routeWitness.routeEq
  rcases exists_point_of_translatePolyline_eq
      taggedPointMember routeOccurrenceEq with
    ⟨physicalPoint, physicalPointMember, pointEq⟩
  have physicalRouteLengthEq :
      ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence
            segmentWitness.routeWitness.metadata
            segmentWitness.routeWitness.metadataIndex
            segmentWitness.routeWitness.literal
            segmentWitness.taggedLiteral.2)).length =
        taggedRoute.1.length := by
    have lengths := congrArg List.length routeOccurrenceEq
    simpa [translatePolyline, metadataPhysicalRouteOccurrence] using
      lengths.symm
  refine ⟨{
    finalRoute := taggedRoute.1
    finalRouteMember := taggedRouteMember
    finalPointMember := taggedPointMember
    finalRouteLengthEq := rfl
    firstSegment := firstSegment
    firstSegmentMember := firstSegmentMember
    firstIndexedMember := by
      simpa only [firstIndexed, drawing] using firstIndexedMember
    segmentWitness := by
      simpa only [firstIndexed] using segmentWitness
    segmentWitnessFinalRouteEq := segmentWitnessFinalRouteEq
    physicalPoint := physicalPoint
    physicalPointMember := by
      simpa [metadataPhysicalRouteOccurrence] using
        physicalPointMember
    physicalRouteLengthEq := physicalRouteLengthEq
    pointEq := ?_
  }⟩
  simpa [metadataPhysicalRouteOccurrence,
    FinalGaugedSegmentOccurrenceWitness.physicalShift,
    retainedDeduplicatedGaugedWrappedDrawing_periodTranslation_eq_placement,
    Cell.add, add_comm] using pointEq

/-- The corresponding finite route point, retaining the original
within-route point index and the physical route length. -/
def FinalGaugedRoutePointOccurrenceWitness.physicalIndexedPoint
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    IndexedRoutePoint where
  routeIndex := witness.segmentWitness.physicalIncidenceIndex
  pointIndex := indexed.pointIndex
  routeLength :=
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
      (metadataPhysicalIncidence
        witness.segmentWitness.routeWitness.metadata
        witness.segmentWitness.routeWitness.metadataIndex
        witness.segmentWitness.routeWitness.literal
        witness.segmentWitness.taggedLiteral.2)).length
  point := witness.physicalPoint

/-- Undoing quotient normalization preserves whether a listed point is an
outer endpoint of its route. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.physicalIndexedPoint_isEndpoint_iff
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    witness.physicalIndexedPoint.IsEndpoint ↔ indexed.IsEndpoint := by
  simp only [IndexedRoutePoint.IsEndpoint,
    FinalGaugedRoutePointOccurrenceWitness.physicalIndexedPoint]
  rw [witness.physicalRouteLengthEq]

/-- The physical occurrence key of a listed route point. -/
def FinalGaugedRoutePointOccurrenceWitness.physicalKey
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    Nat × Nat × Cell :=
  (witness.segmentWitness.physicalIncidenceIndex,
    indexed.pointIndex, witness.segmentWitness.physicalShift)

/-- The anchor-adjusted physical key preserves and reflects the identity of
a final periodic route-point occurrence. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.physicalKey_eq_iff_routePointOccurrenceKey_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift) :
    first.physicalKey = second.physicalKey ↔
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift =
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift := by
  constructor
  · intro physicalPointKeyEq
    have physicalIncidenceIndexEq :
        first.segmentWitness.physicalIncidenceIndex =
          second.segmentWitness.physicalIncidenceIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.1)
        physicalPointKeyEq
    have pointIndexEq :
        firstIndexed.pointIndex = secondIndexed.pointIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.2.1)
        physicalPointKeyEq
    have physicalShiftEq :
        first.segmentWitness.physicalShift =
          second.segmentWitness.physicalShift :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        physicalPointKeyEq
    have physicalSegmentKeyEq :
        first.segmentWitness.physicalKey =
          second.segmentWitness.physicalKey := by
      simp only [
        FinalGaugedSegmentOccurrenceWitness.physicalKey,
        Prod.mk.injEq]
      exact ⟨physicalIncidenceIndexEq, rfl, physicalShiftEq⟩
    have segmentOccurrenceKeyEq :=
      (FinalGaugedSegmentOccurrenceWitness.physicalKey_eq_iff_segmentOccurrenceKey_eq
        first.segmentWitness second.segmentWitness).mp
        physicalSegmentKeyEq
    have routeIndexEq :
        firstIndexed.routeIndex = secondIndexed.routeIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.1)
        segmentOccurrenceKeyEq
    have shiftEq : firstShift = secondShift :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        segmentOccurrenceKeyEq
    simp only [PeriodicGridDrawing.RoutePointOccurrenceKey,
      Prod.mk.injEq]
    exact ⟨routeIndexEq, pointIndexEq, shiftEq⟩
  · intro routePointOccurrenceKeyEq
    have routeIndexEq :
        firstIndexed.routeIndex = secondIndexed.routeIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.1)
        routePointOccurrenceKeyEq
    have pointIndexEq :
        firstIndexed.pointIndex = secondIndexed.pointIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.2.1)
        routePointOccurrenceKeyEq
    have shiftEq : firstShift = secondShift :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        routePointOccurrenceKeyEq
    have segmentOccurrenceKeyEq :
        PeriodicGridDrawing.SegmentOccurrenceKey
            (firstSegmentForRoutePoint
              firstIndexed first.firstSegment) firstShift =
          PeriodicGridDrawing.SegmentOccurrenceKey
            (firstSegmentForRoutePoint
              secondIndexed second.firstSegment) secondShift := by
      simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
        firstSegmentForRoutePoint, Prod.mk.injEq]
      exact ⟨routeIndexEq, trivial, shiftEq⟩
    have physicalSegmentKeyEq :=
      (FinalGaugedSegmentOccurrenceWitness.physicalKey_eq_iff_segmentOccurrenceKey_eq
        first.segmentWitness second.segmentWitness).mpr
        segmentOccurrenceKeyEq
    have physicalIncidenceIndexEq :
        first.segmentWitness.physicalIncidenceIndex =
          second.segmentWitness.physicalIncidenceIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.1)
        physicalSegmentKeyEq
    have physicalShiftEq :
        first.segmentWitness.physicalShift =
          second.segmentWitness.physicalShift :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        physicalSegmentKeyEq
    simp only [
      FinalGaugedRoutePointOccurrenceWitness.physicalKey,
      Prod.mk.injEq]
    exact ⟨physicalIncidenceIndexEq, pointIndexEq, physicalShiftEq⟩

end PeriodicOrthocrossing
end LeanTrominoes
