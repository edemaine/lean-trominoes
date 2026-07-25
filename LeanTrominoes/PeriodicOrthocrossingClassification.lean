import LeanTrominoes.PeriodicOrthocrossingSegments

/-!
# Semantic classification of constructed route segments

For the global no-overlap proof, anonymous within-route indices are awkward.
This file mirrors the executable route constructor with a finite semantic
classification: fanout pieces, port columns, private low/high tracks, gates,
and boundary detours.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The geometric job performed by one segment in a constructed edge route. -/
inductive SegmentRole (Vertex : Type*)
  | sourceFanoutHorizontal (port : GraphPort Vertex)
  | sourceFanoutVertical (port : GraphPort Vertex)
  | sourcePortVertical (port : GraphPort Vertex)
  | lowHorizontal (edgeIndex : Nat)
  | highHorizontal (edgeIndex : Nat)
  | gateVertical (edgeIndex : Nat)
  | boundaryVertical (edgeIndex : Nat)
  | targetPortVertical (port : GraphPort Vertex)
  | targetFanoutVertical (port : GraphPort Vertex)
  | targetFanoutHorizontal (port : GraphPort Vertex)
  deriving DecidableEq, Repr

/-- A concrete generated segment together with its semantic role. -/
structure ClassifiedSegment (Vertex : Type*) where
  role : SegmentRole Vertex
  segment : GridSegment
  deriving DecidableEq, Repr

/-- Classified source fanout pieces. -/
def classifiedSourceFanout {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    List (ClassifiedSegment Vertex) :=
  let port := sourcePort edge edgeIndex
  let center := vertexX (graph.vertices.idxOf edge.source)
  let column := portX graph port
  if center = column then
    [⟨.sourceFanoutVertical port,
      GridSegment.mk (center, 2) (column, 3)⟩]
  else
    [⟨.sourceFanoutHorizontal port,
      GridSegment.mk (center, 2) (column, 2)⟩,
    ⟨.sourceFanoutVertical port,
      GridSegment.mk (column, 2) (column, 3)⟩]

/-- Classified private-track core pieces. -/
def classifiedEdgeCore {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    List (ClassifiedSegment Vertex) :=
  let size : Int := drawingGridSize graph
  let source := sourcePort edge edgeIndex
  let target := targetPort edge edgeIndex
  let sourceX := portX graph source
  let targetX := portX graph target
  let sourcePoint : Cell := (sourceX, 3)
  let targetPoint : Cell :=
    Cell.add (targetX, 3) (Cell.scale size edge.offset)
  let low := edgeTrack edgeIndex
  let high := low + 1
  let gate := edgeGateX graph edgeIndex
  match edge.offset with
  | (0, 0) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (targetX, low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, low) targetPoint⟩]
  | (1, 0) =>
      if targetX < sourceX then
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (size + targetX, low)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (size + targetX, low) targetPoint⟩]
      else
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (size, low)⟩,
          ⟨.boundaryVertical edgeIndex,
            GridSegment.mk (size, low) (size, high)⟩,
          ⟨.highHorizontal edgeIndex,
            GridSegment.mk (size, high) (size + targetX, high)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (size + targetX, high) targetPoint⟩]
  | (-1, 0) =>
      if sourceX < targetX then
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (targetX - size, low)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (targetX - size, low) targetPoint⟩]
      else
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (0, low)⟩,
          ⟨.boundaryVertical edgeIndex,
            GridSegment.mk (0, low) (0, high)⟩,
          ⟨.highHorizontal edgeIndex,
            GridSegment.mk (0, high) (targetX - size, high)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (targetX - size, high) targetPoint⟩]
  | (0, 1) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, high)⟩,
        ⟨.highHorizontal edgeIndex,
          GridSegment.mk (sourceX, high) (gate, high)⟩,
        ⟨.gateVertical edgeIndex,
          GridSegment.mk (gate, high) (gate, size + low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (gate, size + low) (targetX, size + low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, size + low) targetPoint⟩]
  | (0, -1) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (gate, low)⟩,
        ⟨.gateVertical edgeIndex,
          GridSegment.mk (gate, low) (gate, high - size)⟩,
        ⟨.highHorizontal edgeIndex,
          GridSegment.mk (gate, high - size) (targetX, high - size)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, high - size) targetPoint⟩]
  | _ =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (targetPoint.1, low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetPoint.1, low) targetPoint⟩]

/-- Classified target fanout pieces, already translated to the target cell. -/
def classifiedTargetFanout {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    List (ClassifiedSegment Vertex) :=
  let port := targetPort edge edgeIndex
  let center := vertexX (graph.vertices.idxOf edge.target)
  let column := portX graph port
  let translate := Cell.scale (drawingGridSize graph : Int) edge.offset
  if center = column then
    [⟨.targetFanoutVertical port,
      GridSegment.mk
        (Cell.add translate (column, 3))
        (Cell.add translate (center, 2))⟩]
  else
    [⟨.targetFanoutVertical port,
      GridSegment.mk
        (Cell.add translate (column, 3))
        (Cell.add translate (column, 2))⟩,
    ⟨.targetFanoutHorizontal port,
      GridSegment.mk
        (Cell.add translate (column, 2))
        (Cell.add translate (center, 2))⟩]

/-- All classified pieces of one complete constructed route. -/
def classifiedRouteSegments {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    List (ClassifiedSegment Vertex) :=
  classifiedSourceFanout graph edge edgeIndex ++
    classifiedEdgeCore graph edge edgeIndex ++
    classifiedTargetFanout graph edge edgeIndex

/-- Erasing the semantic roles recovers exactly the segment list derived from
the executable polyline constructor. -/
theorem classifiedRouteSegments_map_segment {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (classifiedRouteSegments graph edge edgeIndex).map
        ClassifiedSegment.segment =
      gridPolylineSegments (constructedEdgeRoute graph edge edgeIndex) := by
  let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
  let targetCenter := vertexX (graph.vertices.idxOf edge.target)
  let sourceColumn := portX graph (sourcePort edge edgeIndex)
  let targetColumn := portX graph (targetPort edge edgeIndex)
  by_cases sourceSame : sourceCenter = sourceColumn
  · by_cases targetSame : targetCenter = targetColumn
    · simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout, constructedEdgeRoute,
        joinPolylines, fanout, sourceCenter, targetCenter, sourceColumn,
        targetColumn, sourceSame, targetSame, translatePolyline]
      split <;> simp_all [edgeCore, Cell.add, Cell.scale, add_comm]
      all_goals try rfl
      all_goals split <;>
        simp_all [edgeCore, Cell.add, Cell.scale, add_comm] <;> rfl
    · simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout, constructedEdgeRoute,
        joinPolylines, fanout, sourceCenter, targetCenter, sourceColumn,
        targetColumn, sourceSame, targetSame, translatePolyline]
      split <;> simp_all [edgeCore, Cell.add, Cell.scale, add_comm]
      all_goals try rfl
      all_goals split <;>
        simp_all [edgeCore, Cell.add, Cell.scale, add_comm] <;> rfl
  · by_cases targetSame : targetCenter = targetColumn
    · simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout, constructedEdgeRoute,
        joinPolylines, fanout, sourceCenter, targetCenter, sourceColumn,
        targetColumn, sourceSame, targetSame, translatePolyline]
      split <;> simp_all [edgeCore, Cell.add, Cell.scale, add_comm]
      all_goals try rfl
      all_goals split <;>
        simp_all [edgeCore, Cell.add, Cell.scale, add_comm] <;> rfl
    · simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout, constructedEdgeRoute,
        joinPolylines, fanout, sourceCenter, targetCenter, sourceColumn,
        targetColumn, sourceSame, targetSame, translatePolyline]
      split <;> simp_all [edgeCore, Cell.add, Cell.scale, add_comm]
      all_goals try rfl
      all_goals split <;>
        simp_all [edgeCore, Cell.add, Cell.scale, add_comm] <;> rfl

/-- A segment occurrence in the erased route has a classified occurrence at
the same within-route index. -/
theorem exists_classifiedSegment_of_mem {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {taggedSegment : GridSegment × Nat}
    (taggedMem :
      taggedSegment ∈
        (gridPolylineSegments
          (constructedEdgeRoute graph edge edgeIndex)).zipIdx) :
    ∃ taggedClassified ∈
        (classifiedRouteSegments graph edge edgeIndex).zipIdx,
      taggedClassified.1.segment = taggedSegment.1 ∧
        taggedClassified.2 = taggedSegment.2 := by
  have mappedMem :
      taggedSegment ∈
        ((classifiedRouteSegments graph edge edgeIndex).map
          ClassifiedSegment.segment).zipIdx := by
    rw [classifiedRouteSegments_map_segment]
    exact taggedMem
  rw [List.zipIdx_map] at mappedMem
  rcases List.mem_map.mp mappedMem with
    ⟨taggedClassified, classifiedMem, equality⟩
  refine ⟨taggedClassified, classifiedMem, ?_, ?_⟩
  · exact congrArg Prod.fst equality
  · exact congrArg Prod.snd equality

/-- Every role remembers the protoedge index that owns its piece. -/
def SegmentRole.edgeIndex {Vertex : Type*} : SegmentRole Vertex → Nat
  | .sourceFanoutHorizontal port
  | .sourceFanoutVertical port
  | .sourcePortVertical port
  | .targetPortVertical port
  | .targetFanoutVertical port
  | .targetFanoutHorizontal port => port.edgeIndex
  | .lowHorizontal edgeIndex
  | .highHorizontal edgeIndex
  | .gateVertical edgeIndex
  | .boundaryVertical edgeIndex => edgeIndex

/-- Every role produced for an indexed edge records that edge's index. -/
theorem classifiedSegment_role_edgeIndex {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex) :
    classified.role.edgeIndex = edgeIndex := by
  have classifiedMem' :
      (classified ∈ classifiedSourceFanout graph edge edgeIndex ∨
        classified ∈ classifiedEdgeCore graph edge edgeIndex) ∨
          classified ∈ classifiedTargetFanout graph edge edgeIndex := by
    simpa only [classifiedRouteSegments, List.mem_append] using classifiedMem
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.edgeIndex = edgeIndex := by
    simp [classifiedSourceFanout, SegmentRole.edgeIndex, sourcePort]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.edgeIndex = edgeIndex := by
    simp [classifiedEdgeCore, SegmentRole.edgeIndex, sourcePort, targetPort]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.edgeIndex = edgeIndex := by
    simp [classifiedTargetFanout, SegmentRole.edgeIndex, targetPort]
    split <;> simp_all
  exact classifiedMem'.elim
    (fun sourceOrCore => sourceOrCore.elim
      (sourceAll classified) (coreAll classified))
    (targetAll classified)

end PeriodicOrthocrossing
end LeanTrominoes
