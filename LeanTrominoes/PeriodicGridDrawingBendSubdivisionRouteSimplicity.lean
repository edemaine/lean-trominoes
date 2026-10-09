/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionRouteContacts

/-! # Nonconstant subdivision edges are simple straight routes -/
namespace LeanTrominoes.GridPolyline

theorem isRealSimple_pair {first last : Cell} (different : first≠last) : IsRealSimple [first,last] := by
  refine ⟨by simp,?_,?_⟩
  · intro segment member
    simp only [gridPolylineSegments,List.mem_singleton] at member
    subst segment
    exact different
  · intro firstPiece firstMember secondPiece secondMember ordered
    simp only [gridPolylineSegments,List.zipIdx_cons,List.zipIdx_nil,List.mem_singleton] at firstMember secondMember
    subst firstPiece
    subst secondPiece
    omega

end LeanTrominoes.GridPolyline

namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem subdivision_segment_nonconstant {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int))
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing factor).edges.zipIdx) :
    (subdivisionSegment source drawing factor tagged.1).start≠
      (subdivisionSegment source drawing factor tagged.1).finish := by
  have recordMember := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx member)
  have pieceMember := record_segment_in_moved_route planar recordMember
  rw [recordAt_edge member] at pieceMember
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph spacing
  have routeMember := List.fst_mem_of_mem_zipIdx
    (edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 recordMember))
  have nonconstant := (movedPlanar.1.2.1 _ routeMember).2.1 _ (List.fst_mem_of_mem_zipIdx pieceMember)
  have segmentEq := straightRoute_absolute_segment source drawing factor tagged.1
  change (subdivisionSegment source drawing factor tagged.1).translate
    (Cell.scale ((factor:Int)*drawing.gridSize) (sourceCell drawing factor tagged.1.source))=_ at segmentEq
  intro equal
  apply nonconstant
  rw [← segmentEq]
  exact congrArg (Cell.add
    (Cell.scale ((factor:Int)*drawing.gridSize) (sourceCell drawing factor tagged.1.source))) equal

theorem subdivisionDrawing_routesSimple {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).RealRoutesAreSimple := by
  intro route member
  obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨index,indexValid,indexMember⟩ := List.mem_iff_getElem.mp edgeMember
  have taggedMember : (edge,index) ∈ (subdivisionGraph source drawing factor).edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_some_iff.mpr ⟨indexValid,indexMember⟩
  exact GridPolyline.isRealSimple_pair
    (subdivision_segment_nonconstant planar localDrawing localGraph spacing taggedMember)

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
