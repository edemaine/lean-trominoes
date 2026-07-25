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

/-- Every segment in the completed drawing exposes its originating indexed
protoedge and its semantic classified occurrence. -/
theorem exists_classifiedSegment_of_drawing_mem {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments) :
    ∃ taggedRoute ∈ graph.edges.zipIdx.zipIdx,
      ∃ taggedClassified ∈
          (classifiedRouteSegments graph
            taggedRoute.1.1 taggedRoute.1.2).zipIdx,
        indexed =
          ⟨taggedRoute.2, taggedClassified.2,
            taggedClassified.1.segment⟩ := by
  rcases (mem_drawing_indexedSegments_iff.mp indexedMem) with
    ⟨taggedRoute, routeMem, taggedSegment, segmentMem, indexedEq⟩
  rcases exists_classifiedSegment_of_mem segmentMem with
    ⟨taggedClassified, classifiedMem, segmentEq, indexEq⟩
  refine ⟨taggedRoute, routeMem, taggedClassified, classifiedMem, ?_⟩
  rw [indexedEq]
  simp only [IndexedGridSegment.mk.injEq, true_and]
  exact ⟨indexEq.symm, segmentEq.symm⟩

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

/-- Semantic roles occur at most once within a constructed route. -/
theorem classifiedRouteSegments_roles_nodup {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    ((classifiedRouteSegments graph edge edgeIndex).map
      ClassifiedSegment.role).Nodup := by
  let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
  let targetCenter := vertexX (graph.vertices.idxOf edge.target)
  let sourceColumn := portX graph (sourcePort edge edgeIndex)
  let targetColumn := portX graph (targetPort edge edgeIndex)
  by_cases sourceSame : sourceCenter = sourceColumn <;>
    by_cases targetSame : targetCenter = targetColumn <;>
    simp [classifiedRouteSegments, classifiedSourceFanout,
      classifiedEdgeCore, classifiedTargetFanout, sourceCenter,
      targetCenter, sourceColumn, targetColumn, sourceSame, targetSame]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

/-- Equal roles in one indexed classified route are the same occurrence,
including the same within-route index. -/
theorem taggedClassified_eq_of_role_eq {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {first second : ClassifiedSegment Vertex × Nat}
    (firstMem :
      first ∈ (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (secondMem :
      second ∈ (classifiedRouteSegments graph edge edgeIndex).zipIdx)
    (rolesEqual : first.1.role = second.1.role) :
    first = second := by
  let classified := classifiedRouteSegments graph edge edgeIndex
  let roles := classified.map ClassifiedSegment.role
  have firstIndexLt : first.2 < classified.length := by
    simpa [classified] using List.snd_lt_of_mem_zipIdx firstMem
  have secondIndexLt : second.2 < classified.length := by
    simpa [classified] using List.snd_lt_of_mem_zipIdx secondMem
  have firstAt : classified[first.2]'firstIndexLt = first.1 := by
    simpa [classified] using (List.mem_zipIdx' firstMem).2.symm
  have secondAt : classified[second.2]'secondIndexLt = second.1 := by
    simpa [classified] using (List.mem_zipIdx' secondMem).2.symm
  have rolesNodup : roles.Nodup := by
    exact classifiedRouteSegments_roles_nodup graph edge edgeIndex
  have firstRoleAt :
      roles[first.2]'(by simpa [roles] using firstIndexLt) =
        first.1.role := by
    simp [roles, firstAt]
  have secondRoleAt :
      roles[second.2]'(by simpa [roles] using secondIndexLt) =
        second.1.role := by
    simp [roles, secondAt]
  have firstIdxOf :=
    rolesNodup.idxOf_getElem first.2
      (by simpa [roles] using firstIndexLt)
  have secondIdxOf :=
    rolesNodup.idxOf_getElem second.2
      (by simpa [roles] using secondIndexLt)
  rw [firstRoleAt] at firstIdxOf
  rw [secondRoleAt, ← rolesEqual] at secondIdxOf
  have indicesEqual : first.2 = second.2 := by
    omega
  apply Prod.ext
  · have firstAtOption :=
      (List.mem_zipIdx_iff_getElem?).mp firstMem
    have secondAtOption :=
      (List.mem_zipIdx_iff_getElem?).mp secondMem
    rw [indicesEqual, secondAtOption] at firstAtOption
    exact Option.some.inj firstAtOption.symm
  · exact indicesEqual

end PeriodicOrthocrossing
end LeanTrominoes
