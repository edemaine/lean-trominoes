/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingPolygonalPointBounds
import LeanTrominoes.GridSegmentPerturbationTranslation

/-! # Linear direction bounds without child-graph locality

A raw child edge may cross two period boundaries. Its direction is still
bounded by twice the original period, since it is a translated piece of a
local parent route. No locality assertion about the child graph is needed.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

theorem subdivisionSegment_direction_bounds {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (valid : drawing.IsRealDrawing source) (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    |(subdivisionSegment source drawing tagged.1).direction.1| ≤ 2*(drawing.gridSize : Int) ∧
      |(subdivisionSegment source drawing tagged.1).direction.2| ≤ 2*(drawing.gridSize : Int) := by
  have indexValid : tagged.2 < (subdivisionGraph source drawing).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have recordMember := recordAt_mem (source := source) (drawing := drawing) indexValid
  obtain ⟨parent,parentMember,piece,_,recordEq⟩ := record_provenance recordMember
  let absolute := absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1
  have absoluteMember : absolute ∈ gridPolylineSegments (drawing.edgeRoute parent.2) := by
    have indexed := record_segment_in_original_route valid recordMember
    have parentIndex := congrArg (fun record : (Nat × Nat) × PeriodicEdge (Vertex V) => record.1.1) recordEq
    rw [recordAt_edge member,parentIndex] at indexed
    exact List.fst_mem_of_mem_zipIdx indexed
  have endpoints := gridPolylineSegments_endpoints_mem absoluteMember
  have length : 2 ≤ (drawing.edgeRoute parent.2).length := by
    have positive := List.length_pos_of_mem absoluteMember
    rw [gridPolylineSegments_length] at positive
    omega
  have bounds := local_rectangle_coordinate_difference
    (graphLocal parent.1 (List.fst_mem_of_mem_zipIdx parentMember))
    (polygonal_point_in_local_rectangle drawingLocal parentMember length endpoints.1)
    (polygonal_point_in_local_rectangle drawingLocal parentMember length endpoints.2)
  have directions : (subdivisionSegment source drawing tagged.1).direction = absolute.direction := by
    have lifted := lifted_subdivision_segment_eq source drawing tagged.1 (0,0)
    simpa only [GridSegment.direction_translate] using congrArg GridSegment.direction lifted
  rw [directions]
  exact bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
