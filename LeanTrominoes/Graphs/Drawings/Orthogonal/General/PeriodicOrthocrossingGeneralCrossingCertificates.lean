/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralDrawing

/-! # Integral crossing points and the exclusion of triple crossings -/
namespace LeanTrominoes
namespace PeriodicGridDrawing

theorem realProperlyCrossesAt_integral {first second : GridSegment} {point : ℝ × ℝ}
    (crossing : RealProperlyCrossesAt first second point) : ∃ cell : Cell, point = realCell cell := by
  have firstContains := GridSegment.realInteriorContains_implies_realContains crossing.1
  have secondContains := GridSegment.realInteriorContains_implies_realContains crossing.2.1
  rcases crossing.2.2 with ⟨horizontal,vertical⟩ | ⟨vertical,horizontal⟩
  · exact ⟨(second.start.1,first.start.2),Prod.ext
      (GridSegment.realContains_vertical_x vertical secondContains)
      (GridSegment.realContains_horizontal_y horizontal firstContains)⟩
  · exact ⟨(first.start.1,second.start.2),Prod.ext
      (GridSegment.realContains_vertical_x vertical firstContains)
      (GridSegment.realContains_horizontal_y horizontal secondContains)⟩

end PeriodicGridDrawing
namespace PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] core classifiedCore fan route

theorem drawing_crossings_integral {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (isLocal : graph.IsLocal)
    (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstIndex secondIndex : Nat} {firstCell secondCell : Cell}
    (firstValid : firstIndex < (drawing graph orthogonal).edgeRoutes.length)
    (secondValid : secondIndex < (drawing graph orthogonal).edgeRoutes.length)
    (different : (firstIndex,firstCell) ≠ (secondIndex,secondCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((drawing graph orthogonal).realEdgeRoute firstIndex firstCell) point)
    (secondContains : GridPolyline.RealContains ((drawing graph orthogonal).realEdgeRoute secondIndex secondCell) point)
    (notEndpoint : ¬ GridPolyline.RealIsEndpoint ((drawing graph orthogonal).realEdgeRoute firstIndex firstCell) point) :
    ∃ cell : Cell, point = realCell cell := by
  have contact := drawing_isRealOrthocrossing wellFormed orthogonal degree isLocal
    firstIndex secondIndex firstCell secondCell firstValid secondValid different point firstContains secondContains
  rcases contact with endpoints | ⟨_,_,_,_,crossing⟩
  · exact (notEndpoint endpoints.1).elim
  · exact PeriodicGridDrawing.realProperlyCrossesAt_integral crossing

theorem core_occurrences_no_triple {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (isLocal : graph.IsLocal)
    {a b c : PeriodicEdge Vertex × Nat}
    (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx) (cm : c ∈ graph.edges.zipIdx)
    {ap bp cp : ClassifiedSegment Vertex}
    (apm : ap ∈ classifiedCore graph a.1 a.2) (bpm : bp ∈ classifiedCore graph b.1 b.2)
    (cpm : cp ∈ classifiedCore graph c.1 c.2)
    {ac bc cc : Cell} (ab : (a,ac) ≠ (b,bc)) (acDiff : (a,ac) ≠ (c,cc)) (bcDiff : (b,bc) ≠ (c,cc))
    {point : ℝ × ℝ}
    (ah : (ap.segment.translate (Cell.scale (drawingGridSize graph : Int) ac)).RealContains point)
    (bh : (bp.segment.translate (Cell.scale (drawingGridSize graph : Int) bc)).RealContains point)
    (ch : (cp.segment.translate (Cell.scale (drawingGridSize graph : Int) cc)).RealContains point) : False := by
  have aligned {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
      {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2) :
      piece.segment.IsAxisAligned := by
    apply (orthogonalPolyline_iff_segments _).mp
      (core_orthogonal wellFormed member (isLocal _ (List.fst_mem_of_mem_zipIdx member)))
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩
  have parallelImpossible {first second : PeriodicEdge Vertex × Nat}
      (fm : first ∈ graph.edges.zipIdx) (sm : second ∈ graph.edges.zipIdx)
      {fp sp : ClassifiedSegment Vertex} (fpm : fp ∈ classifiedCore graph first.1 first.2)
      (spm : sp ∈ classifiedCore graph second.1 second.2) {fc sc : Cell}
      (different : (first,fc) ≠ (second,sc))
      (fh : (fp.segment.translate (Cell.scale (drawingGridSize graph : Int) fc)).RealContains point)
      (sh : (sp.segment.translate (Cell.scale (drawingGridSize graph : Int) sc)).RealContains point)
      (parallel : (fp.segment.IsHorizontal ∧ sp.segment.IsHorizontal) ∨
        (fp.segment.IsVertical ∧ sp.segment.IsVertical)) : False := by
    rcases parallel with ⟨firstAxis,secondAxis⟩ | ⟨firstAxis,secondAxis⟩
    · have equal := horizontal_core_contacts_unique wellFormed fm sm
        (isLocal _ (List.fst_mem_of_mem_zipIdx fm)) fpm spm firstAxis secondAxis fh sh
      exact different (Prod.ext equal.1 equal.2.2)
    · have equal := vertical_core_contacts_unique wellFormed fm sm
        (isLocal _ (List.fst_mem_of_mem_zipIdx fm)) (isLocal _ (List.fst_mem_of_mem_zipIdx sm))
        fpm spm firstAxis secondAxis fh sh
      exact different (Prod.ext equal.1 equal.2.2)
  rcases aligned am apm with aH | aV <;> rcases aligned bm bpm with bH | bV
  · exact parallelImpossible am bm apm bpm ab ah bh (Or.inl ⟨aH,bH⟩)
  · rcases aligned cm cpm with cH | cV
    · exact parallelImpossible am cm apm cpm acDiff ah ch (Or.inl ⟨aH,cH⟩)
    · exact parallelImpossible bm cm bpm cpm bcDiff bh ch (Or.inr ⟨bV,cV⟩)
  · rcases aligned cm cpm with cH | cV
    · exact parallelImpossible bm cm bpm cpm bcDiff bh ch (Or.inl ⟨bH,cH⟩)
    · exact parallelImpossible am cm apm cpm acDiff ah ch (Or.inr ⟨aV,cV⟩)
  · exact parallelImpossible am bm apm bpm ab ah bh (Or.inr ⟨aV,bV⟩)

theorem route_occurrences_no_triple {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (isLocal : graph.IsLocal)
    (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {a b c : PeriodicEdge Vertex × Nat}
    (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx) (cm : c ∈ graph.edges.zipIdx)
    {ac bc cc : Cell} (ab : (a,ac) ≠ (b,bc)) (acDiff : (a,ac) ≠ (c,cc)) (bcDiff : (b,bc) ≠ (c,cc))
    {point : ℝ × ℝ}
    (ah : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) ac)
      (route graph orthogonal a.1 a.2)) point)
    (bh : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) bc)
      (route graph orthogonal b.1 b.2)) point)
    (ch : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) cc)
      (route graph orthogonal c.1 c.2)) point)
    (notEndpoint : ¬ GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) ac)
      (route graph orthogonal a.1 a.2)) point) : False := by
  have contact := route_occurrence_contacts wellFormed orthogonal degree am bm
    (isLocal _ (List.fst_mem_of_mem_zipIdx am)) (isLocal _ (List.fst_mem_of_mem_zipIdx bm)) ab ah bh
  rcases contact with endpoints | ⟨ap,apm,bp,bpm,crossing⟩
  · exact notEndpoint endpoints.1
  · have aCore := GridSegment.realInteriorContains_implies_realContains crossing.1
    have bCore := GridSegment.realInteriorContains_implies_realContains crossing.2.1
    rcases lifted_route_realContains_parts orthogonal degree cm ch with ⟨target,fanContains⟩ | ⟨cp,cpm,cCore⟩
    · have equal := route_fan_core_contacts_same_occurrence wellFormed orthogonal degree cm am
        (isLocal _ (List.fst_mem_of_mem_zipIdx am)) apm target fanContains aCore
      exact acDiff (Prod.ext equal.1 equal.2).symm
    · exact core_occurrences_no_triple wellFormed isLocal am bm cm apm bpm cpm ab acDiff bcDiff aCore bCore cCore

end PeriodicOrthocrossing.GeneralPorts
end LeanTrominoes
