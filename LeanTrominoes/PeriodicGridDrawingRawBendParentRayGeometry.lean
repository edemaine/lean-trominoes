/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendParentPorts
import LeanTrominoes.PeriodicGridDrawingPolygonalPointBounds
import LeanTrominoes.OrthogonalBendFanRaySigns

/-! # Every ray at an inserted bend belongs to its original parent route -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def bendCenter {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) : Cell :=
  Cell.add (position source drawing (.bend edgeIndex pointIndex))
    (drawing.periodTranslation (sourceCell (V := V) drawing (.bend edgeIndex pointIndex)))

theorem bend_port_outward_segment {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (portMember : port ∈ allPorts (subdivisionGraph source drawing)) {edgeIndex pointIndex : Nat}
    (vertex : port.vertex = .bend edgeIndex pointIndex) :
    ∃ segment : GridSegment, (shiftedDrawing source drawing).portRayKey port = segment.straightRayKey ∧
      segment.start = bendCenter source drawing edgeIndex pointIndex ∧
      segment.finish ∈ drawing.edgeRoute edgeIndex ∧ segment.start ≠ segment.finish := by
  obtain ⟨tagged,taggedMember,kind⟩ := GeneralVertexNormalization.allPorts_has_edge portMember
  have recordMember := recordAt_mem (source := source) (drawing := drawing)
    (by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx taggedMember)
  have indexed := record_segment_in_original_route planar.1 recordMember
  rw [recordAt_edge taggedMember] at indexed
  have parentValid := record_parent_index_valid planar.1.1 recordMember
  have nonconstant := (planar.1.2.1 _ (List.fst_mem_of_mem_zipIdx (BendSubdivision.edgeRoute_tagged_mem_of_lt parentValid))).2.1
    _ (List.fst_mem_of_mem_zipIdx indexed)
  have absoluteEqual : (subdivisionSegment source drawing tagged.1).translate
      (Cell.scale drawing.gridSize (sourceCell drawing tagged.1.source)) =
      absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1 :=
    straightRoute_absolute_segment source drawing tagged.1
  have parentIndex := bend_port_parent portMember vertex
  rcases kind with rfl | rfl
  · change (recordAt source drawing tagged.2).1.1 = edgeIndex at parentIndex
    rw [parentIndex] at indexed
    have endpoints := gridPolylineSegments_endpoints_mem (List.fst_mem_of_mem_zipIdx indexed)
    refine ⟨absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1,?_,?_,endpoints.2,nonconstant⟩
    · rw [shifted_source_portRayKey source drawing taggedMember,← absoluteEqual,GridSegment.straightRayKey_translate]
    · change tagged.1.source = .bend edgeIndex pointIndex at vertex
      simp only [absoluteSegment,bendCenter,vertex,periodTranslation]
  · change (recordAt source drawing tagged.2).1.1 = edgeIndex at parentIndex
    rw [parentIndex] at indexed
    have endpoints := gridPolylineSegments_endpoints_mem (List.fst_mem_of_mem_zipIdx indexed)
    refine ⟨(absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).reverse,?_,?_,endpoints.1,?_⟩
    · rw [shifted_target_portRayKey source drawing taggedMember,← absoluteEqual]
      change (subdivisionSegment source drawing tagged.1).reverse.straightRayKey =
        ((subdivisionSegment source drawing tagged.1).reverse.translate (Cell.scale drawing.gridSize (sourceCell drawing tagged.1.source))).straightRayKey
      rw [GridSegment.straightRayKey_translate]
    · change tagged.1.target = .bend edgeIndex pointIndex at vertex
      have cellEqual := bend_target_cell taggedMember vertex
      change Cell.add (position source drawing tagged.1.target)
        (Cell.scale drawing.gridSize (Cell.add (sourceCell drawing tagged.1.source) tagged.1.offset)) = _
      rw [cellEqual,vertex]
      rfl
    · exact fun equal => nonconstant equal.symm

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
