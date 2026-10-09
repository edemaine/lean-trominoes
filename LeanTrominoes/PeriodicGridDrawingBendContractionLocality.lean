/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendContractionDrawing

/-! # Joined refined routes remain in the original pair of neighboring cells -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem chainEdges_cells_allowed {V : Type*} {points : List (V × Cell)} (label : V → Cell) (offset : Cell)
    (sourceLabels : ∀ point∈points.dropLast,label point.1=point.2)
    (allowed : ∀ point∈points,point.2=(0,0) ∨ point.2=offset) :
    ∀ edge∈chainEdges points,
      (label edge.source=(0,0) ∨ label edge.source=offset) ∧
      (Cell.add (label edge.source) edge.offset=(0,0) ∨ Cell.add (label edge.source) edge.offset=offset) := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [chainEdges]
  | cons_cons first second rest _ induction =>
      intro edge member
      simp only [chainEdges,List.mem_cons] at member
      rcases member with rfl | member
      · have sourceEq := sourceLabels first (by simp)
        have targetEq : Cell.add first.2 (Cell.sub second.2 first.2)=second.2 := by
          apply Prod.ext <;> simp only [Cell.add,Cell.sub] <;> ring
        simpa only [sourceEq,targetEq] using
          And.intro (allowed first (by simp)) (allowed second (by simp))
      · exact induction second (fun point member => sourceLabels point
          (by simp only [List.dropLast_cons_cons,List.mem_cons]; exact Or.inr member))
          (fun point member => allowed point (List.mem_cons_of_mem first member)) edge member

theorem parentRecord_cells_allowed {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ parentRecords drawing (bendRefinementFactor drawing) parent) :
    (sourceCell drawing (bendRefinementFactor drawing) record.2.source=(0,0) ∨
      sourceCell drawing (bendRefinementFactor drawing) record.2.source=parent.1.offset) ∧
    (Cell.add (sourceCell drawing (bendRefinementFactor drawing) record.2.source) record.2.offset=(0,0) ∨
      Cell.add (sourceCell drawing (bendRefinementFactor drawing) record.2.source) record.2.offset=parent.1.offset) := by
  obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
  apply chainEdges_cells_allowed (sourceCell drawing (bendRefinementFactor drawing)) parent.1.offset
    (fun _ member => nodes_source_labels drawing _ parent member) ?_ piece.1 (List.fst_mem_of_mem_zipIdx pieceMember)
  intro entry entryMember
  have localOffset := localGraph parent.1 (List.fst_mem_of_mem_zipIdx parentMember)
  simp only [nodes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at entryMember
  rcases entryMember with (rfl | entryMember) | rfl
  · exact Or.inl rfl
  · obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp entryMember
    have routeMember := edgeRoute_mem_of_compatible planar.1.1 parentMember
    have bounds := polygonal_point_in_local_rectangle localDrawing parentMember
      (planar.1.2.1 _ routeMember).1 (internalPoint_mem_route originalMember)
    exact InteriorBends.cells_allowed (by have := bendRefinementFactor_spacing drawing; omega) localOffset bounds
  · exact Or.inr rfl

theorem realPointInCell_translate_inverse_iff (drawing : PeriodicGridDrawing) (base copy : Cell) (p : ℝ × ℝ) :
    drawing.RealPointInCell base (p.1-(drawing.periodTranslation copy).1,p.2-(drawing.periodTranslation copy).2) ↔
      drawing.RealPointInCell (Cell.add base copy) p := by
  simp only [RealPointInCell,periodTranslation,Cell.scale,Cell.add,Int.cast_mul,Int.cast_natCast,Int.cast_add]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem refinedPiece_local {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ parentRecords drawing (bendRefinementFactor drawing) parent) {p : ℝ × ℝ}
    (contains : GridPolyline.RealContains (refinedPiece source drawing record) p) :
    (orthogonalSubdivision source drawing).RealPointInCell (0,0) p ∨
      (orthogonalSubdivision source drawing).RealPointInCell parent.1.offset p := by
  have globalMember := parentRecord_mem parentMember member
  let output := orthogonalSubdivision source drawing
  let copy := sourceCell drawing (bendRefinementFactor drawing) record.2.source
  let shift := output.periodTranslation copy
  have baseContains : GridPolyline.RealContains (output.edgeRoute (recordIndex source drawing (bendRefinementFactor drawing) record))
      (p.1-shift.1,p.2-shift.2) := by
    apply (GridPolyline.realContains_translate shift _ _).mp
    simpa only [refinedPiece,realEdgeRoute,PeriodicOrthocrossing.translatePolyline,add_sub_cancel] using contains
  have localPoints := orthogonalSubdivision_local planar localDrawing localGraph degree
    _ (recordIndex_tagged globalMember) _ baseContains
  have cells := parentRecord_cells_allowed planar localDrawing localGraph parentMember member
  have sourceCellEq : Cell.add (0,0) copy=copy := by apply Prod.ext <;> simp [Cell.add]
  have targetCellEq : Cell.add record.2.offset copy=Cell.add copy record.2.offset := by
    apply Prod.ext <;> simp only [Cell.add] <;> ring
  rcases localPoints with sourcePoint | targetPoint
  · have translated := (realPointInCell_translate_inverse_iff output (0,0) copy p).mp sourcePoint
    rw [sourceCellEq] at translated
    rcases cells.1 with zero | neighbor
    · exact Or.inl (by simpa only [copy,zero] using translated)
    · exact Or.inr (by simpa only [copy,neighbor] using translated)
  · have translated := (realPointInCell_translate_inverse_iff output record.2.offset copy p).mp targetPoint
    rw [targetCellEq] at translated
    rcases cells.2 with zero | neighbor
    · exact Or.inl (by simpa only [copy,zero] using translated)
    · exact Or.inr (by simpa only [copy,neighbor] using translated)

theorem contractedDrawing_local {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsRealLocal source := by
  intro parent parentMember p contains
  rw [contractedDrawing_edgeRoute parentMember] at contains
  obtain ⟨route,routeMember,routeContains⟩ := GridPolyline.joinRouteChain_contains
    (parentPieces_chain planar localDrawing localGraph degree parentMember)
    (fun route member => (parentPieces_openSimple planar localDrawing localGraph degree parentMember member).1) contains
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp routeMember
  have localPoints := refinedPiece_local planar localDrawing localGraph degree parentMember recordMember routeContains
  have sameSize : (contractedDrawing source drawing).gridSize=(orthogonalSubdivision source drawing).gridSize := by
    rw [contractedDrawing_gridSize,orthogonalSubdivision_gridSize,polygonalScale,Nat.mul_assoc]
  simpa only [RealPointInCell,sameSize] using localPoints

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
